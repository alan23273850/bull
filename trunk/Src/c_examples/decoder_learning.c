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
 * 2. 稀疏表驅動的 Membership Query (MQ)：
 * - 維護全域的 key -> decoders row hash map（只存實際查詢到的 key）。
 * - 當 Learner 提出 MQ 時，先查 map；若 row 未填 (valid == false)，則呼叫 Z3 求解器
 * 將該 key 代入 all_commute 定義中，解出所有 Decoder 的正確答案並存入 row。
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
#include <stdint.h>
 
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
 
 static int num_global_decoders = 0;
typedef struct MeasRowNode {
    bool used;
    bool valid;
    uint64_t hash;
    uint64_t *key_words;  // 長度 global_key_words
    bool *c;  // 長度 num_global_decoders
} MeasRowNode;

static MeasRowNode *meas_row_map = NULL;
static size_t meas_row_map_buckets = 0;
static size_t meas_row_map_size = 0;
static size_t global_key_words = 0;
static uint64_t *scratch_key_words = NULL;
static size_t scratch_key_words_cap = 0;
 
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

#define MEAS_ROW_MAP_BUCKETS (1u << 15)
#define MEAS_ROW_MAP_LOAD_NUM 7u
#define MEAS_ROW_MAP_LOAD_DEN 10u

static inline bool meas_key_get_bit(const uint64_t *key_words, int bit_idx) {
    size_t w = (size_t)bit_idx >> 6;
    unsigned b = (unsigned)bit_idx & 63u;
    return ((key_words[w] >> b) & 1ULL) != 0ULL;
}

static inline void meas_key_set_bit(uint64_t *key_words, int bit_idx) {
    size_t w = (size_t)bit_idx >> 6;
    unsigned b = (unsigned)bit_idx & 63u;
    key_words[w] |= (1ULL << b);
}

static uint64_t meas_key_hash(const uint64_t *key_words, size_t words) {
    // FNV-1a 64-bit
    uint64_t h = 1469598103934665603ULL;
    const uint8_t *bytes = (const uint8_t *)key_words;
    size_t n = words * sizeof(uint64_t);
    for (size_t i = 0; i < n; i++) {
        h ^= (uint64_t)bytes[i];
        h *= 1099511628211ULL;
    }
    return h;
}

static int ensure_scratch_key_words(size_t need_words) {
    if (scratch_key_words_cap >= need_words) return 1;
    uint64_t *new_buf = (uint64_t *)realloc(scratch_key_words, need_words * sizeof(uint64_t));
    if (!new_buf) return 0;
    scratch_key_words = new_buf;
    scratch_key_words_cap = need_words;
    return 1;
}

static int meas_row_map_init(void) {
    meas_row_map_buckets = (size_t)MEAS_ROW_MAP_BUCKETS;
    meas_row_map_size = 0;
    meas_row_map = (MeasRowNode *)calloc(meas_row_map_buckets, sizeof(MeasRowNode));
    return meas_row_map ? 1 : 0;
}

static size_t meas_row_map_find_slot(const uint64_t *key_words, uint64_t hash, int *found) {
    size_t mask = meas_row_map_buckets - 1; // buckets must be power-of-two
    size_t idx = (size_t)hash & mask;
    for (;;) {
        MeasRowNode *slot = &meas_row_map[idx];
        if (!slot->used) {
            *found = 0;
            return idx;
        }
        if (slot->hash == hash &&
            slot->key_words &&
            memcmp(slot->key_words, key_words, global_key_words * sizeof(uint64_t)) == 0) {
            *found = 1;
            return idx;
        }
        idx = (idx + 1) & mask;
    }
}

static int meas_row_map_rehash(size_t new_buckets) {
    MeasRowNode *old_map = meas_row_map;
    size_t old_buckets = meas_row_map_buckets;

    MeasRowNode *new_map = (MeasRowNode *)calloc(new_buckets, sizeof(MeasRowNode));
    if (!new_map) return 0;

    meas_row_map = new_map;
    meas_row_map_buckets = new_buckets;
    meas_row_map_size = 0;

    size_t mask = new_buckets - 1;
    for (size_t i = 0; i < old_buckets; i++) {
        MeasRowNode *old = &old_map[i];
        if (!old->used) continue;
        size_t idx = (size_t)old->hash & mask;
        while (new_map[idx].used) idx = (idx + 1) & mask;
        new_map[idx] = *old;
        meas_row_map_size++;
    }

    free(old_map);
    return 1;
}

static MeasRowNode *meas_row_map_get_or_create(const uint64_t *key_words) {
    if (!meas_row_map || meas_row_map_buckets == 0) return NULL;

    if ((meas_row_map_size + 1) * MEAS_ROW_MAP_LOAD_DEN >
        meas_row_map_buckets * MEAS_ROW_MAP_LOAD_NUM) {
        if (!meas_row_map_rehash(meas_row_map_buckets << 1)) return NULL;
    }

    uint64_t hash = meas_key_hash(key_words, global_key_words);
    int found = 0;
    size_t idx = meas_row_map_find_slot(key_words, hash, &found);
    MeasRowNode *slot = &meas_row_map[idx];
    if (found) return slot;

    slot->used = true;
    slot->valid = false;
    slot->hash = hash;
    slot->key_words = (uint64_t *)malloc(global_key_words * sizeof(uint64_t));
    if (!slot->key_words) {
        memset(slot, 0, sizeof(*slot));
        return NULL;
    }
    memcpy(slot->key_words, key_words, global_key_words * sizeof(uint64_t));
    slot->c = (bool *)calloc((size_t)num_global_decoders, sizeof(bool));
    if (!slot->c) {
        free(slot->key_words);
        memset(slot, 0, sizeof(*slot));
        return NULL;
    }
    meas_row_map_size++;
    return slot;
}

static void meas_row_map_free_all(void) {
    if (!meas_row_map) return;
    for (size_t i = 0; i < meas_row_map_buckets; i++) {
        if (!meas_row_map[i].used) continue;
        free(meas_row_map[i].key_words);
        free(meas_row_map[i].c);
    }
    free(meas_row_map);
    meas_row_map = NULL;
    meas_row_map_buckets = 0;
    meas_row_map_size = 0;
}

static void fill_meas_row_with_z3(const uint64_t *key_words, MeasRowNode *row) {
    if (!row || !row->c) return;
    if (row->valid) return;

    Z3_solver_push(z3_ctx, z3_solver);
    Z3_solver_assert(z3_ctx, z3_solver, z3_all_commute);
    for (int i = 0; i < global_num_meas; i++) {
        bool bit = meas_key_get_bit(key_words, i);
        Z3_ast val = bit ? Z3_mk_true(z3_ctx) : Z3_mk_false(z3_ctx);
        Z3_solver_assert(z3_ctx, z3_solver, Z3_mk_eq(z3_ctx, z3_meas_vars[i], val));
    }

    Z3_lbool res = Z3_solver_check(z3_ctx, z3_solver);
    if (res == Z3_L_TRUE) {
        Z3_model model = Z3_solver_get_model(z3_ctx, z3_solver);
        Z3_model_inc_ref(z3_ctx, model);
        for (int j = 0; j < num_global_decoders; j++) {
            Z3_ast eval_res;
            Z3_model_eval(z3_ctx, model, z3_dec_vars[j], true, &eval_res);
            row->c[j] = (Z3_get_bool_value(z3_ctx, eval_res) == Z3_L_TRUE);
        }
        Z3_model_dec_ref(z3_ctx, model);
    } else {
        for (int j = 0; j < num_global_decoders; j++) {
            row->c[j] = false;
        }
    }
    Z3_solver_pop(z3_ctx, z3_solver, 1);
    row->valid = true;
    table_valid_entries++;

    fprintf(stderr, "[Table] MQ/CE Z3 填 hash=0x%llx columns:", (unsigned long long)row->hash);
    for (int d = 0; d < num_global_decoders; d++) fprintf(stderr, " %d", row->c[d] ? 1 : 0);
    fprintf(stderr, "\n");
}
 
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
static void meas_key_from_bv(bitvector *bv, uint64_t *out_words, size_t words) {
    memset(out_words, 0, words * sizeof(uint64_t));
    if (!bv || bitvector_length(bv) <= 1) return;
    size_t len = (size_t)bitvector_length(bv);
    for (size_t i = 1; i < len; i++) {
        if (bitvector_get(bv, (uscalar_t)i)) {
            meas_key_set_bit(out_words, (int)(i - 1));
        }
    }
}

 static membership_result_t membership(void *info, bitvector *bv) {
     (void)info;
    if (!meas_row_map || current_learner_id < 0 || current_learner_id >= num_global_decoders) {
         fprintf(stderr, "[MQ] learner=%d 表未就緒或 id 無效，回傳 true\n", current_learner_id);
         return true;
     }
    if (!ensure_scratch_key_words(global_key_words)) return true;
    meas_key_from_bv(bv, scratch_key_words, global_key_words);
   MeasRowNode *e = meas_row_map_get_or_create(scratch_key_words);
    if (!e || !e->c) return true;
   if (!e->valid) fill_meas_row_with_z3(scratch_key_words, e);
    bool out = e->c[current_learner_id];
    fprintf(stderr, "[MQ] learner=%d hash=0x%llx -> %d\n", current_learner_id, (unsigned long long)e->hash, out ? 1 : 0);
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
    global_key_words = (size_t)((num_meas + 63) / 64);
     table_valid_entries = 0;
     current_learner_id = -1;
    meas_row_map = NULL;
    meas_row_map_buckets = 0;
    meas_row_map_size = 0;
     pending_formula = NULL;
     eq_pending_result = NULL;
     global_learners = NULL;
     z3_ctx = NULL;
     z3_solver = NULL;
     z3_meas_vars = NULL;
     z3_dec_vars = NULL;
     z3_all_commute = NULL;
    scratch_key_words = NULL;
    scratch_key_words_cap = 0;
 
     char *json_result = NULL;
 
     if (num_decoders <= 0 || num_meas <= 0) {
         json_result = (char *)malloc(3);
         if (json_result) { json_result[0] = '{'; json_result[1] = '}'; json_result[2] = '\0'; }
         return json_result;
     }
    if (global_key_words == 0) global_key_words = 1;
 
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
 
    // 初始化稀疏 MQ 表格（hash map），避免 2^num_meas 全表配置
    if (!meas_row_map_init()) goto cleanup;
 
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
             Z3_model model = Z3_solver_get_model(z3_ctx, z3_solver);
             Z3_model_inc_ref(z3_ctx, model);
            if (!ensure_scratch_key_words(global_key_words)) {
                Z3_model_dec_ref(z3_ctx, model);
                Z3_solver_pop(z3_ctx, z3_solver, 1);
                goto cleanup;
            }
            memset(scratch_key_words, 0, global_key_words * sizeof(uint64_t));

           for (int i = 0; i < global_num_meas; i++) {
                 Z3_ast eval_res;
                 Z3_model_eval(z3_ctx, model, z3_meas_vars[i], true, &eval_res);
                 if (Z3_get_bool_value(z3_ctx, eval_res) == Z3_L_TRUE) {
                    meas_key_set_bit(scratch_key_words, i);
                 }
             }
 
             // 檢查該 key 是否已在表內
           MeasRowNode *row = meas_row_map_get_or_create(scratch_key_words);
            if (!row) {
                Z3_model_dec_ref(z3_ctx, model);
                Z3_solver_pop(z3_ctx, z3_solver, 1);
                goto cleanup;
            }

            if (row->valid) {
                 // 檢查是否真的有等待中的 Learner 猜測與 Table 不符
                 bool any_learner_wrong = false;
                 int n = global_num_meas > 0 ? global_num_meas : 1;
                 bool *vals = (bool *)malloc((size_t)(n + 1) * sizeof(bool));
                for (int v = 1; v <= n; v++) vals[v] = meas_key_get_bit(scratch_key_words, v - 1);
 
                 for (int i = 0; i < num_decoders; i++) {
                     if (global_learners[i].state != L_WAIT_EQ) continue;
                     bool pred = pending_formula[i] ? eval_boolformula_with_vals(pending_formula[i], vals) : false;
                    bool truth = row->c[i];
                     if (pred != truth) {
                         any_learner_wrong = true;
                         break;
                     }
                 }
                 free(vals);
 
                 if (any_learner_wrong) {
                    fprintf(stderr, "[Dispatcher] Z3 找到反例 hash=0x%llx 已在表內，且有 Learner 預測錯誤，作為有效反例踢回！\n", (unsigned long long)row->hash);
                 } else {
                     // 【防禦性編程 (Fail-Fast)】：放棄治療
                    fprintf(stderr, "[Dispatcher] ⚠ 致命錯誤：Z3 找到反例 hash=0x%llx 已在表內，且所有 Learner 皆正確！\n", (unsigned long long)row->hash);
                     fprintf(stderr, "這代表 SMT 模型中存在超出糾錯能力極限的 Uncorrectable Error 或物理約束有瑕疵。\n");
                     fprintf(stderr, "觸發防禦機制：放棄治療，直接中斷學習程序並跳至 cleanup。\n");
                     
                     Z3_model_dec_ref(z3_ctx, model);
                     Z3_solver_pop(z3_ctx, z3_solver, 1);
                     goto cleanup;
                 }
             } else {
                fprintf(stderr, "[Dispatcher] Z3 確定採用新反例 hash=0x%llx\n", (unsigned long long)row->hash);
             }
 
             // 確保 Z3 狀態恢復與資源釋放
             Z3_model_dec_ref(z3_ctx, model);
             Z3_solver_pop(z3_ctx, z3_solver, 1);
             
             // 填表確保該 key 有標準答案
           if (!row->valid) fill_meas_row_with_z3(scratch_key_words, row);

            uint64_t *ce_key_words = (uint64_t *)malloc(global_key_words * sizeof(uint64_t));
            if (!ce_key_words) {
                goto cleanup;
            }
            memcpy(ce_key_words, scratch_key_words, global_key_words * sizeof(uint64_t));

             // 喚醒猜錯的 Learner 並分派反例
             int n = global_num_meas > 0 ? global_num_meas : 1;
             bool *vals = (bool *)malloc((size_t)(n + 1) * sizeof(bool));
            for (int v = 1; v <= n; v++) vals[v] = meas_key_get_bit(ce_key_words, v - 1);
             
             for (int i = 0; i < num_decoders; i++) {
                 if (global_learners[i].state != L_WAIT_EQ) continue;
                 bool pred = pending_formula[i] ? eval_boolformula_with_vals(pending_formula[i], vals) : false;
                bool truth = row->c[i];
                 if (pred != truth) {
                     equivalence_result_t *r = (equivalence_result_t *)malloc(sizeof(equivalence_result_t));
                     r->is_equal = false;
                     r->counterexample = bitvector_new((uscalar_t)(n + 1));
                     bitvector_set(r->counterexample, 0, truth);
                     for (int j = 0; j < n; j++)
                        bitvector_set(r->counterexample, (uscalar_t)(j + 1), meas_key_get_bit(ce_key_words, j));
                     eq_pending_result[i] = r;
                     global_learners[i].state = L_RUNNING;
                     current_learner_id = i;
                     swapcontext(&dispatcher_ctx, &global_learners[i].ctx);
                 }
             }
             free(vals);
            free(ce_key_words);
 
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
    meas_row_map_free_all();
    free(scratch_key_words);
    scratch_key_words = NULL;
    scratch_key_words_cap = 0;
    cleanup_learning_resources(NULL, 0,
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