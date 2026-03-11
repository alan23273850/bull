/*
 * Decoder learning: cooperative multitasking + 表驅動 MQ/EQ.
 *
 * 本檔案實作了基於 ucontext 的協程 (Coroutine) 排程器，用於並行執行多個 BULL Learner。
 * 主要機制包含：
 * 1. 協程排程 (Cooperative Multitasking)：
 * - 每個 Learner 擁有獨立的 Stack (LearnerContext)。
 * - 透過 ucontext_t 進行 Context Switch，避免使用 Pthread 帶來的 Race Condition 與 Mutex 成本。
 * - 當 Learner 遇到 Equivalence Query (EQ) 時，會主動 yield (交出控制權) 給 Dispatcher。
 *
 * 2. 表驅動的 Membership Query (MQ)：
 * - 維護一個全域的 meas_to_decoders_table (大小為 2^num_meas)。
 * - 當 Learner 提出 MQ 時，先查表；若表未填 (valid == false)，則呼叫 Z3 求解器
 * 將該 key 代入 all_commute 定義中，解出所有 Decoder 的正確答案並存入表中。
 *
 * 3. 全域 Equivalence Query (Global EQ) 檢查與防禦性機制：
 * - 當所有尚未完成的 Learner 都停在 EQ 時 (L_WAIT_EQ)，Dispatcher 會進行全域檢查。
 * - 使用 Z3 求解器尋找反例：將所有 Learner 的猜測公式 (Hypothesis) 與對應的 Decoder 綁定，
 * 並加上 NOT(all_commute) 條件來尋找違反對易性的錯誤。
 * - 若 Z3 找到的反例 key 已經在表格內 (valid == true)，理論上必定有至少一個 Learner 尚未收斂 (預測錯誤)，此時將其作為有效反例踢回。
 * - 【防禦性機制 (Fail-Fast)】：根據 QEC 理論，若 Table 答案合法，應能修正該 key 下所有容許的 faults。
 * 若發生「所有 Learner 預測皆正確，但 Z3 仍報錯」的異常狀況，代表 SMT 模型包含了超出糾錯極限的錯誤或約束有瑕疵。
 * 此時程式將「放棄治療」，直接中斷並跳轉至 cleanup，回傳空結果以避免產生錯誤的 Decoder。
 * - 【例外處理 (UNKNOWN)】：若 Z3 資源耗盡或超時回傳 UNKNOWN，將發出警告並強制中止學習。
 *
 * 4. JSON 結果輸出：
 * - 學習完成後，將所有 Learner 得到的 boolformula 轉換為 Z3 SMT-LIB2 格式。
 * - 封裝成 JSON 字串並回傳給 Python 呼叫端。
 */
 #include <stdio.h>
 #include <stdlib.h>
 #include <string.h>
 #include <stdbool.h>
 
 // 引入協程所需的標頭檔 (POSIX 標準)
 #if !defined(_WIN32)
 #include <ucontext.h>
 #else
 #error "ucontext.h is not supported on Windows natively. Please compile on Linux/macOS."
 #endif
 
 // Z3 C API
 #include <z3.h>
 
 // BULL core headers
 #include "../core/type.h"
 #include "../core/bitvector.h"
 #include "../core/boolformula.h"
 #include "../core/query.h"
 #include "../core/cdnf.h"
 #include "decoder_learning_helpers.h"
 
 #ifdef _WIN32
 #define EXPORT __declspec(dllexport)
 #else
 #define EXPORT __attribute__((visibility("default")))
 #endif
 
 static MeasToDecodersEntry *meas_to_decoders_table = NULL;
 static size_t meas_table_size = 0;       // 表格大小，為 2^num_meas
 static int num_global_decoders = 0;
 
 // Global EQ：負責在 Learner 與 Dispatcher 之間傳遞資料
 static boolformula_t **pending_formula = NULL;   // Learner 交出的猜測公式 (Hypothesis)
 static equivalence_result_t **eq_pending_result = NULL;  // Dispatcher 填寫的驗證結果 (包含反例)
 
 // 全域/靜態變數供 Dispatcher 與 Learner 進行 Context Switch
 static ucontext_t dispatcher_ctx;
 static LearnerContext *global_learners = NULL;
 static int current_learner_id = -1;
 static int global_num_meas = 0;  // 測量向量長度，對應 key 的位元數
 static const char **global_meas_names = NULL;
 
 // Z3 全域變數
 static Z3_context z3_ctx = NULL;
 static Z3_solver z3_solver = NULL;
 static Z3_ast *z3_meas_vars = NULL;
 static Z3_ast *z3_dec_vars = NULL;
 static Z3_ast z3_all_commute = NULL;
 
 static int table_valid_entries = 0; // 統計 table 中已填寫的有效資料數
 
 // ============================================================================
 // 輔助函式：交出控制權 (Yield)
 // ============================================================================
 // Learner 呼叫此函式，主動將執行權交還給 Dispatcher
 static void yield_to_dispatcher() {
     if (current_learner_id >= 0) {
         swapcontext(&global_learners[current_learner_id].ctx, &dispatcher_ctx);
     }
 }
 
 // ============================================================================
 // Learner 的主邏輯 (跑在獨立的 Stack 上)
 // ============================================================================
 
 // Membership Query (MQ)：
 // 將測量結果 (meas) 轉為 key 查表。若表未填，呼叫 Z3 解出該 key 下所有 Decoder 的答案並記錄。
 static membership_result_t membership(void *info, bitvector *bv) {
     (void)info;
     if (!meas_to_decoders_table || current_learner_id < 0 || current_learner_id >= num_global_decoders) {
         fprintf(stderr, "[MQ] learner=%d 表未就緒或 id 無效，回傳 true\n", current_learner_id);
         return true;
     }
     size_t key = meas_bv_to_key(bv);
     if (key >= meas_table_size) {
         fprintf(stderr, "[MQ] learner=%d key=%zu 超出表大小，拋出錯誤\n", current_learner_id, key);
         abort();
     }
     MeasToDecodersEntry *e = &meas_to_decoders_table[key];
     if (!e->c) return true;
     if (!e->valid) {
         // 表內無資料，呼叫 Z3 進行全域求解並填滿該 row
         fill_meas_table_row_with_z3(z3_ctx, z3_solver, z3_meas_vars, z3_dec_vars, z3_all_commute, key, meas_table_size, meas_to_decoders_table, num_global_decoders, global_num_meas, &table_valid_entries);
     }
     bool out = e->c[current_learner_id];
     fprintf(stderr, "[MQ] learner=%d key=%zu -> %d\n", current_learner_id, key, out ? 1 : 0);
     return out;
 }
 
 // Equivalence Query (EQ)：
 // Learner 提交猜測 (Hypothesis) 給 Dispatcher，並進入 L_WAIT_EQ 等待。
 // 被喚醒時，讀取 Dispatcher 準備好的反例 (或收斂訊號)。
 static equivalence_result_t *equivalence(void *info,
                                          uscalar_t num_vars,
                                          boolformula_t *b) {
     (void)info;
     (void)num_vars;
     int id = current_learner_id;
     fprintf(stderr, "[EQ] learner=%d 交出 hypothesis，進入 L_WAIT_EQ\n", id);
     if (id < 0 || id >= num_global_decoders || !pending_formula || !eq_pending_result)
         return NULL;
 
     if (pending_formula[id]) {
         boolformula_free(pending_formula[id]);
         pending_formula[id] = NULL;
     }
     pending_formula[id] = boolformula_copy(b);
     global_learners[id].state = L_WAIT_EQ;
     yield_to_dispatcher(); // 交出控制權，等待 Global EQ 驗證
 
     // 被 dispatcher 喚醒後，回傳驗證結果
     equivalence_result_t *res = eq_pending_result[id];
     if (res) {
         fprintf(stderr, "[EQ] learner=%d 被 resume，is_equal=%d counterexample=%s\n",
                 id, res->is_equal ? 1 : 0, res->counterexample ? "有" : "無");
     } else {
         fprintf(stderr, "[EQ] learner=%d 被 resume，result=NULL\n", id);
     }
     return res;
 }
 
 static void learner_routine(int id) {
     LearnerContext *me = &global_learners[id];
     me->state = L_RUNNING;
 
     fprintf(stderr, "[Learner %d (%s)] 啟動！\n", id, me->name);
 
     void *info = NULL;
     uscalar_t num_vars = (global_num_meas > 0) ? (uscalar_t)global_num_meas : 1;
 
     // 啟動 BULL 學習核心
     boolformula_t *f = learn(info,
                              num_vars,
                              membership,   // MQ 介面
                              NULL,         // COMEM
                              equivalence,  // EQ 介面
                              CDNF);
 
     if (f) {
         me->result_formula = f; 
         fprintf(stderr, "[Learner %d (%s)] 公式：", id, me->name);
         boolformula_print(f);
         fprintf(stderr, "\n");
     } else {
         me->result_formula = NULL;
         fprintf(stderr, "[Learner %d] learn() 回傳 NULL。\n", id);
     }
 
     fprintf(stderr, "[Learner %d (%s)] DONE！\n", id, me->name);
     me->state = L_DONE;
 
     yield_to_dispatcher(); // 結束前最後一次跳回
 }
 
 // ============================================================================
 // 主程式進入點 (Python C-API 入口)
 // ============================================================================
 EXPORT char *decoder_learning_in_C(
     const char *smt2_str,
     const char **meas_names,
     int num_meas,
     const char **decoder_names,
     int num_decoders,
     const char *all_commute_name)
 {
     // 全域變數重置，確保多次呼叫安全
     global_meas_names = meas_names;
     num_global_decoders = num_decoders;
     global_num_meas = num_meas;
     table_valid_entries = 0;
     current_learner_id = -1;
     meas_to_decoders_table = NULL;
     meas_table_size = 0;
     pending_formula = NULL;
     eq_pending_result = NULL;
     global_learners = NULL;
     z3_ctx = NULL;
     z3_solver = NULL;
     z3_meas_vars = NULL;
     z3_dec_vars = NULL;
     z3_all_commute = NULL;
 
     char *json_result = NULL;
 
     if (num_decoders <= 0 || num_meas <= 0) {
         json_result = (char *)malloc(3);
         if (json_result) { json_result[0] = '{'; json_result[1] = '}'; json_result[2] = '\0'; }
         return json_result;
     }
 
     // 初始化 Z3 求解器環境
     Z3_config cfg = Z3_mk_config();
     z3_ctx = Z3_mk_context(cfg);
     Z3_del_config(cfg);
     z3_solver = Z3_mk_solver(z3_ctx);
     Z3_solver_inc_ref(z3_ctx, z3_solver);
 
     // 載入背景物理定義 (SMT-LIB2 格式)
     Z3_ast_vector ast_vec = Z3_parse_smtlib2_string(z3_ctx, smt2_str, 0, NULL, NULL, 0, NULL, NULL);
     Z3_ast_vector_inc_ref(z3_ctx, ast_vec);
     for (unsigned i = 0; i < Z3_ast_vector_size(z3_ctx, ast_vec); i++) {
         Z3_solver_assert(z3_ctx, z3_solver, Z3_ast_vector_get(z3_ctx, ast_vec, i));
     }
     Z3_ast_vector_dec_ref(z3_ctx, ast_vec);
 
     Z3_sort bool_sort = Z3_mk_bool_sort(z3_ctx);
     z3_meas_vars = (Z3_ast *)malloc(num_meas * sizeof(Z3_ast));
     for (int i = 0; i < num_meas; i++) {
         z3_meas_vars[i] = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, meas_names[i]), bool_sort);
     }
     z3_dec_vars = (Z3_ast *)malloc(num_decoders * sizeof(Z3_ast));
     for (int i = 0; i < num_decoders; i++) {
         z3_dec_vars[i] = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, decoder_names[i]), bool_sort);
     }
     z3_all_commute = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, all_commute_name), bool_sort);
 
     // 初始化 MQ 表格：大小為 2^num_meas
     meas_table_size = (size_t)1 << (num_meas <= (int)(sizeof(size_t) * 8) ? num_meas : 0);
     meas_to_decoders_table = (MeasToDecodersEntry *)calloc(meas_table_size, sizeof(MeasToDecodersEntry));
     if (meas_to_decoders_table) {
         for (size_t k = 0; k < meas_table_size; k++) {
             meas_to_decoders_table[k].valid = false;
             meas_to_decoders_table[k].c = (bool *)calloc((size_t)num_decoders, sizeof(bool));
         }
     }
 
     pending_formula = (boolformula_t **)calloc((size_t)num_decoders, sizeof(boolformula_t *));
     eq_pending_result = (equivalence_result_t **)calloc((size_t)num_decoders, sizeof(equivalence_result_t *));
     if (!pending_formula || !eq_pending_result) goto cleanup;
 
     // ---------------------------------------------------------
     // 階段 1：初始化 Learner 與 Coroutine Stack
     // ---------------------------------------------------------
     global_learners = (LearnerContext *)calloc(num_decoders, sizeof(LearnerContext));
 
     for (int i = 0; i < num_decoders; i++) {
         global_learners[i].id = i;
         global_learners[i].name = decoder_names[i] ? decoder_names[i] : "Unknown";
         global_learners[i].state = L_INIT;
         global_learners[i].counted_as_done = false;
         global_learners[i].result_formula = NULL;
 
         global_learners[i].stack_memory = malloc(STACK_SIZE);
 
         getcontext(&global_learners[i].ctx);
         global_learners[i].ctx.uc_stack.ss_sp = global_learners[i].stack_memory;
         global_learners[i].ctx.uc_stack.ss_size = STACK_SIZE;
         global_learners[i].ctx.uc_link = &dispatcher_ctx;
 
         makecontext(&global_learners[i].ctx, (void (*)(void))learner_routine, 1, i);
     }
 
     // ---------------------------------------------------------
     // 階段 2：主迴圈 Dispatcher
     // ---------------------------------------------------------
     fprintf(stderr, "\n=== 進入 Dispatcher 區域 ===\n");
     int active_learners = num_decoders;
 
     while (active_learners > 0) {
         // 1. 調度尚未等待 EQ 的 Learner 繼續執行
         int someone_running = 0;
         for (int i = 0; i < num_decoders; i++) {
             LearnerContext *l = &global_learners[i];
             if (l->state == L_RUNNING || l->state == L_INIT) {
                 current_learner_id = l->id;
                 swapcontext(&dispatcher_ctx, &l->ctx);
                 someone_running = 1;
             }
             if (l->state == L_DONE && !l->counted_as_done) {
                 l->counted_as_done = true;
                 active_learners--;
             }
         }
         if (someone_running || active_learners == 0) continue;
 
         // 2. 確認是否所有非 DONE 的 Learner 都處於 L_WAIT_EQ
         int all_wait_eq = 1;
         for (int i = 0; i < num_decoders; i++) {
             if (global_learners[i].state != L_DONE && global_learners[i].state != L_WAIT_EQ) {
                 all_wait_eq = 0;
                 break;
             }
         }
         if (!all_wait_eq) continue;
 
         // 3. 進入 Global EQ：使用 Z3 驗證所有 Conjecture
         fprintf(stderr, "[Dispatcher] Global EQ: 使用 Z3 尋找反例\n");
         
         Z3_solver_push(z3_ctx, z3_solver);
         Z3_solver_assert(z3_ctx, z3_solver, Z3_mk_not(z3_ctx, z3_all_commute));
         
         for (int i = 0; i < num_decoders; i++) {
             if (pending_formula[i]) {
                 Z3_ast conj_ast = encode_boolformula_to_z3_ast(z3_ctx, pending_formula[i], z3_meas_vars);
                 Z3_solver_assert(z3_ctx, z3_solver, Z3_mk_eq(z3_ctx, z3_dec_vars[i], conj_ast));
             }
         }
         
         Z3_lbool res = Z3_solver_check(z3_ctx, z3_solver);
 
         if (res == Z3_L_TRUE) {
             // SAT：找到反例
             size_t key = 0;
             Z3_model model = Z3_solver_get_model(z3_ctx, z3_solver);
             Z3_model_inc_ref(z3_ctx, model);
             
             for (int i = 0; i < global_num_meas && i < sizeof(size_t) * 8; i++) {
                 Z3_ast eval_res;
                 Z3_model_eval(z3_ctx, model, z3_meas_vars[i], true, &eval_res);
                 if (Z3_get_bool_value(z3_ctx, eval_res) == Z3_L_TRUE) {
                     key |= ((size_t)1 << i);
                 }
             }
 
             // 檢查該 key 是否已在表內
             if (meas_to_decoders_table[key].valid) {
                 // 檢查是否真的有等待中的 Learner 猜測與 Table 不符
                 bool any_learner_wrong = false;
                 int n = global_num_meas > 0 ? global_num_meas : 1;
                 bool *vals = (bool *)malloc((size_t)(n + 1) * sizeof(bool));
                 for (int v = 1; v <= n; v++) vals[v] = ((key >> (v - 1)) & 1) != 0;
 
                 for (int i = 0; i < num_decoders; i++) {
                     if (global_learners[i].state != L_WAIT_EQ) continue;
                     bool pred = pending_formula[i] ? eval_boolformula_with_vals(pending_formula[i], vals) : false;
                     bool truth = meas_to_decoders_table[key].c[i];
                     if (pred != truth) {
                         any_learner_wrong = true;
                         break;
                     }
                 }
                 free(vals);
 
                 if (any_learner_wrong) {
                     fprintf(stderr, "[Dispatcher] Z3 找到反例 key=%zu 已在表內，且有 Learner 預測錯誤，作為有效反例踢回！\n", key);
                 } else {
                     // 【防禦性編程 (Fail-Fast)】：放棄治療
                     fprintf(stderr, "[Dispatcher] ⚠ 致命錯誤：Z3 找到反例 key=%zu 已在表內，且所有 Learner 皆正確！\n", key);
                     fprintf(stderr, "這代表 SMT 模型中存在超出糾錯能力極限的 Uncorrectable Error 或物理約束有瑕疵。\n");
                     fprintf(stderr, "觸發防禦機制：放棄治療，直接中斷學習程序並跳至 cleanup。\n");
                     
                     Z3_model_dec_ref(z3_ctx, model);
                     Z3_solver_pop(z3_ctx, z3_solver, 1);
                     goto cleanup;
                 }
             } else {
                 fprintf(stderr, "[Dispatcher] Z3 確定採用新反例 key=%zu\n", key);
             }
 
             // 確保 Z3 狀態恢復與資源釋放
             Z3_model_dec_ref(z3_ctx, model);
             Z3_solver_pop(z3_ctx, z3_solver, 1);
             
             // 填表確保該 key 有標準答案
             if (!meas_to_decoders_table[key].valid) {
                 fill_meas_table_row_with_z3(z3_ctx, z3_solver, z3_meas_vars, z3_dec_vars, z3_all_commute, key, meas_table_size, meas_to_decoders_table, num_decoders, global_num_meas, &table_valid_entries);
             }
             
             // 喚醒猜錯的 Learner 並分派反例
             int n = global_num_meas > 0 ? global_num_meas : 1;
             bool *vals = (bool *)malloc((size_t)(n + 1) * sizeof(bool));
             for (int v = 1; v <= n; v++) vals[v] = ((key >> (v - 1)) & 1) != 0;
             
             for (int i = 0; i < num_decoders; i++) {
                 if (global_learners[i].state != L_WAIT_EQ) continue;
                 bool pred = pending_formula[i] ? eval_boolformula_with_vals(pending_formula[i], vals) : false;
                 bool truth = meas_to_decoders_table[key].c[i];
                 if (pred != truth) {
                     equivalence_result_t *r = (equivalence_result_t *)malloc(sizeof(equivalence_result_t));
                     r->is_equal = false;
                     r->counterexample = bitvector_new((uscalar_t)(n + 1));
                     bitvector_set(r->counterexample, 0, truth);
                     for (int j = 0; j < n; j++)
                         bitvector_set(r->counterexample, (uscalar_t)(j + 1), ((key >> j) & 1) != 0);
                     eq_pending_result[i] = r;
                     global_learners[i].state = L_RUNNING;
                     current_learner_id = i;
                     swapcontext(&dispatcher_ctx, &global_learners[i].ctx);
                 }
             }
             free(vals);
 
         } else if (res == Z3_L_FALSE) {
             // UNSAT：數學證明收斂完成！
             Z3_solver_pop(z3_ctx, z3_solver, 1);
             fprintf(stderr, "[Dispatcher] Z3 證明全部正確 (UNSAT)！\n");
             
             for (int i = 0; i < num_decoders; i++) {
                 if (global_learners[i].state != L_WAIT_EQ) continue;
                 eq_pending_result[i] = (equivalence_result_t *)malloc(sizeof(equivalence_result_t));
                 if (eq_pending_result[i]) {
                     eq_pending_result[i]->is_equal = true;
                     eq_pending_result[i]->counterexample = NULL;
                 }
                 current_learner_id = i;
                 swapcontext(&dispatcher_ctx, &global_learners[i].ctx);
             }
         } else {
             // UNKNOWN：Z3 解不出來，強制中止當前 EQ
             Z3_solver_pop(z3_ctx, z3_solver, 1);
             fprintf(stderr, "[Dispatcher] 🚨 嚴重異常：因 Z3 回傳 UNKNOWN (解不出來)！\n");
             fprintf(stderr, "可能是因為超時、資源耗盡，或遇到無法處理的複雜度。強制將所有 Learner 視為收斂以終止程式。\n");
             
             for (int i = 0; i < num_decoders; i++) {
                 if (global_learners[i].state != L_WAIT_EQ) continue;
                 eq_pending_result[i] = (equivalence_result_t *)malloc(sizeof(equivalence_result_t));
                 if (eq_pending_result[i]) {
                     eq_pending_result[i]->is_equal = true; 
                     eq_pending_result[i]->counterexample = NULL;
                 }
                 current_learner_id = i;
                 swapcontext(&dispatcher_ctx, &global_learners[i].ctx);
             }
         }
     }
     fprintf(stderr, "=== Dispatcher 結束：所有 Learner 皆已 DONE ===\n\n");
 
     // ---------------------------------------------------------
     // 階段 3：產生結果 JSON
     // ---------------------------------------------------------
     if (global_learners) {
         json_result = build_results_json(global_learners, num_decoders, decoder_names, global_meas_names, global_num_meas);
     } else {
         json_result = strdup("{}");
     }
     printf("Table Size: %d\n", table_valid_entries);
 
 cleanup:
     // 當發生異常跳轉時，json_result 仍為 NULL，這裡會補上 "{}" 回傳給 Python，不留髒記憶體
     if (!json_result) json_result = strdup("{}");
     cleanup_learning_resources(&meas_to_decoders_table, meas_table_size,
                                &pending_formula, num_decoders,
                                &eq_pending_result,
                                &global_learners);
 
     if (z3_meas_vars) free(z3_meas_vars);
     if (z3_dec_vars) free(z3_dec_vars);
     if (z3_solver) {
         Z3_solver_dec_ref(z3_ctx, z3_solver);
     }
     if (z3_ctx) {
         Z3_del_context(z3_ctx);
     }
 
     return json_result;
 }