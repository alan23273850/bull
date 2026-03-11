/*
 * Decoder learning: cooperative multitasking + 表驅動 MQ/EQ.
 *
 * 本檔案實作了基於 ucontext 的協程 (Coroutine) 排程器，用於並行執行多個 BULL Learner。
 * 主要機制包含：
 * 1. 協程排程 (Cooperative Multitasking)：
 *    - 每個 Learner 擁有獨立的 Stack (LearnerContext)。
 *    - 透過 ucontext_t 進行 Context Switch，避免使用 Pthread 帶來的 Race Condition 與 Mutex 成本。
 *    - 當 Learner 遇到 Equivalence Query (EQ) 時，會主動 yield (交出控制權) 給 Dispatcher。
 *
 * 2. 表驅動的 Membership Query (MQ)：
 *    - 維護一個全域的 meas_to_decoders_table (大小為 2^num_meas)。
 *    - 當 Learner 提出 MQ 時，先查表；若表未填，則為「所有」Learner 產生一組對應的值並存入表中。
 *    - 為了避免產生不必要的反例，填表時會參考其他 Learner 當前的 Conjecture (pending_formula) 來給值。
 *
 * 3. 全域 Equivalence Query (Global EQ) 檢查：
 *    - 當所有 Learner 都停在 EQ 時 (L_WAIT_EQ)，Dispatcher 會進行全域檢查。
 *    - 第 1 輪：挑選新的 key，針對奇數 Learner 給予反例，偶數 Learner 給予正確答案並填表。
 *    - 第 2 輪：挑選新的 key，針對偶數 Learner 給予反例，奇數 Learner 給予正確答案並填表。
 *    - 第 3 輪起：不再隨機產生新 key，而是遍歷現有表格。若發現 Learner 的 Conjecture 與表格不符，則給予該反例並喚醒該 Learner；若完全相符，則判定該 Learner 學習完成。
 *
 * 4. JSON 結果輸出：
 *    - 學習完成後，將所有 Learner 得到的 boolformula 轉換為 Z3 SMT-LIB2 格式。
 *    - 封裝成 JSON 字串並回傳給 Python 呼叫端。
 */
 #include <stdio.h>
 #include <stdlib.h>
 #include <string.h>
 #include <stdbool.h>
#include <time.h>

// 引入協程所需的標頭檔 (POSIX 標準)
#if !defined(_WIN32)
#include <ucontext.h>
#else
#error "ucontext.h is not supported on Windows natively. Please compile on Linux/macOS."
#endif

// Z3 C API（你已經安裝 libz3-dev）
#include <z3.h>

// BULL core headers，提供 learn() / boolformula_t / bitvector 等型別
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
 static size_t meas_table_size = 0;       // 2^num_meas
 static int num_global_decoders = 0;

 // Global EQ：每個 learner 在 EQ 時交出 hypothesis，由 dispatcher 統一檢查
 static boolformula_t **pending_formula = NULL;   // pending_formula[i] = learner i 目前交出的公式
 static equivalence_result_t **eq_pending_result = NULL;  // dispatcher 填寫，learner 被 resume 時讀取
 static int global_eq_round_count = 0;           // 第 1 輪 odd 反例+填表，第 2 輪 even 反例+填表，第 3 輪起只驗表格

// 全域/靜態變數供 Dispatcher 與 Learner 進行 Context Switch
static ucontext_t dispatcher_ctx;
static LearnerContext *global_learners = NULL;
static int current_learner_id = -1;
static int global_num_meas = 0;  // 測量向量長度，供 learn() 的 num_vars 使用
static const char **global_meas_names = NULL;  // 變數編號 1..num_meas 對應的名稱，用於還原 formula 輸出

// Z3 全域變數
static Z3_context z3_ctx = NULL;
static Z3_solver z3_solver = NULL;
static Z3_ast *z3_meas_vars = NULL;
static Z3_ast *z3_dec_vars = NULL;
static Z3_ast z3_all_commute = NULL;

static int table_valid_entries = 0; // 統計 table 中被用到的 valid entry 數量

// ============================================================================
// 輔助函式：交出控制權 (Yield)
// ============================================================================
 // Learner 呼叫此函式，必定會跳回主迴圈的 Dispatcher 區域
 static void yield_to_dispatcher() {
     if (current_learner_id >= 0) {
         swapcontext(&global_learners[current_learner_id].ctx, &dispatcher_ctx);
     }
 }

 // ============================================================================
 // Learner 的主邏輯 (跑在自己獨立的 Stack 上)
 // ============================================================================

// Membership Query：查 meas → decoders 表；若該 key 沒有則用 Z3 求解
static membership_result_t membership(void *info, bitvector *bv) {
    (void)info;
    if (!meas_to_decoders_table || current_learner_id < 0 || current_learner_id >= num_global_decoders) {
        fprintf(stderr, "[MQ] learner=%d 表未就緒或 id 無效，回傳 true\n", current_learner_id);
        return true;
    }
    size_t key = meas_bv_to_key(bv);
    if (key >= meas_table_size) {
        fprintf(stderr, "[MQ] learner=%d key=%zu 超出表大小 (meas_table_size=%zu)，拋出錯誤\n",
                current_learner_id, key, meas_table_size);
        abort();
    }
    MeasToDecodersEntry *e = &meas_to_decoders_table[key];
    if (!e->c) return true;
    if (!e->valid) {
        fill_meas_table_row_with_z3(z3_ctx, z3_solver, z3_meas_vars, z3_dec_vars, z3_all_commute, key, meas_table_size, meas_to_decoders_table, num_global_decoders, global_num_meas, &table_valid_entries);
    }
    bool out = e->c[current_learner_id];
    fprintf(stderr, "[MQ] learner=%d key=%zu -> %d\n", current_learner_id, key, out ? 1 : 0);
    return out;
}


// Equivalence Query：交出 hypothesis 給 dispatcher，yield；被 resume 時回傳 global 的結果（反例或收斂）
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
    yield_to_dispatcher();
    // 被 dispatcher resume 後從這裡繼續，回傳 dispatcher 填好的結果（learn() 會 free）
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

    // 這裡直接呼叫 BULL 的 learn()，使用簡化版的 membership / equivalence。
    void *info = NULL;
    // 目前先用 meas 的長度當作變數個數；若為 0 則退回 1。
    uscalar_t num_vars = (global_num_meas > 0) ? (uscalar_t)global_num_meas : 1;

    boolformula_t *f = learn(info,
                             num_vars,
                             membership,   // MEM
                             NULL,         // COMEM
                             equivalence,  // EQ
                             CDNF);        // 先用最基本模式

    if (f) {
        me->result_formula = f; // 接到階段 3，由主流程寫入 JSON 後再 free
        fprintf(stderr, "[Learner %d (%s)] 公式：", id, me->name);
        boolformula_print(f);
        fprintf(stderr, "\n");
    } else {
        me->result_formula = NULL;
        fprintf(stderr, "[Learner %d] learn() 回傳 NULL（可能是 prototype 還沒接好）。\n", id);
    }

    fprintf(stderr, "[Learner %d (%s)] DONE！\n", id, me->name);
     me->state = L_DONE;

     // 徹底結束前，最後一次跳回 Dispatcher
     yield_to_dispatcher();
 }

 // ============================================================================
// 主程式進入點
// ============================================================================
EXPORT char *decoder_learning_in_C(
    const char *smt2_str,
    const char **meas_names,
    int num_meas,
    const char **decoder_names,
    int num_decoders,
    const char *all_commute_name)
{
    // 確保每次呼叫時全域變數都重置為初始狀態
    global_meas_names = meas_names;
    num_global_decoders = num_decoders;
    global_num_meas = num_meas;
    global_eq_round_count = 0;
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

    srand((unsigned)time(NULL));

    // 初始化 Z3
    Z3_config cfg = Z3_mk_config();
    z3_ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    z3_solver = Z3_mk_solver(z3_ctx);
    Z3_solver_inc_ref(z3_ctx, z3_solver);

    // 解析 smt2_str (包含 assert)
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

     // 表格：meas → decoders，key = 0 .. 2^num_meas - 1
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
     // 階段 1：初始化所有的 Learner 與其專屬 Stack
     // ---------------------------------------------------------
    global_learners = (LearnerContext *)calloc(num_decoders, sizeof(LearnerContext));

     for (int i = 0; i < num_decoders; i++) {
         global_learners[i].id = i;
         global_learners[i].name = decoder_names[i] ? decoder_names[i] : "Unknown";
         global_learners[i].state = L_INIT;
         global_learners[i].counted_as_done = false;
         global_learners[i].result_formula = NULL;

         // 分配獨立 Stack
         global_learners[i].stack_memory = malloc(STACK_SIZE);

         // 設定 ucontext
         getcontext(&global_learners[i].ctx);
         global_learners[i].ctx.uc_stack.ss_sp = global_learners[i].stack_memory;
         global_learners[i].ctx.uc_stack.ss_size = STACK_SIZE;
         global_learners[i].ctx.uc_link = &dispatcher_ctx; // Fallback 連接

         // 綁定函式與參數
         makecontext(&global_learners[i].ctx, (void (*)(void))learner_routine, 1, i);
     }

    // ---------------------------------------------------------
    // 階段 2：主迴圈 Dispatcher；全部 L_WAIT_EQ 時做 global EQ，滿 3 輪宣佈收斂
    // ---------------------------------------------------------
    fprintf(stderr, "\n=== 進入 Dispatcher 區域 ===\n");
    int active_learners = num_decoders;

    while (active_learners > 0) {
        // 1. 先把所有 L_RUNNING 或 L_INIT 的 learner 跑一輪
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

         // 2. 沒人在跑：檢查是否全部非 DONE 的都在 L_WAIT_EQ
         int all_wait_eq = 1;
         for (int i = 0; i < num_decoders; i++) {
             if (global_learners[i].state != L_DONE && global_learners[i].state != L_WAIT_EQ) {
                 all_wait_eq = 0;
                 break;
             }
         }
         if (!all_wait_eq) continue;

        // 3. 全部都在等 EQ → 使用 Z3 找反例
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
            // 找到反例！
            Z3_model model = Z3_solver_get_model(z3_ctx, z3_solver);
            Z3_model_inc_ref(z3_ctx, model);
            
            size_t key = 0;
            for (int i = 0; i < global_num_meas && i < sizeof(size_t) * 8; i++) {
                Z3_ast eval_res;
                Z3_model_eval(z3_ctx, model, z3_meas_vars[i], true, &eval_res);
                if (Z3_get_bool_value(z3_ctx, eval_res) == Z3_L_TRUE) {
                    key |= ((size_t)1 << i);
                }
            }
            Z3_model_dec_ref(z3_ctx, model);
            Z3_solver_pop(z3_ctx, z3_solver, 1);
            
            fprintf(stderr, "[Dispatcher] Z3 找到反例 key=%zu\n", key);
            
            // 確保這個 key 在表裡有正確答案
            if (!meas_to_decoders_table[key].valid) {
                fill_meas_table_row_with_z3(z3_ctx, z3_solver, z3_meas_vars, z3_dec_vars, z3_all_commute, key, meas_table_size, meas_to_decoders_table, num_decoders, global_num_meas, &table_valid_entries);
            }
            
            // 找出哪些 learner 猜錯了，給他們反例並喚醒
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
            
        } else {
            // UNSAT (或 UNKNOWN) -> 沒有反例，全部正確！
            Z3_solver_pop(z3_ctx, z3_solver, 1);
            fprintf(stderr, "[Dispatcher] Z3 證明全部正確！\n");
            
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
    // 階段 3：收集答案並產生 JSON（公式轉成 Z3/SMT-LIB2 格式再傳回 Python）
    // ---------------------------------------------------------
    if (global_learners) {
        json_result = build_results_json(global_learners, num_decoders, decoder_names, global_meas_names, global_num_meas);
    } else {
        json_result = strdup("{}");
    }
    printf("Table Size: %d\n", table_valid_entries);

cleanup:
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
