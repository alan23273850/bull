/*
 * Decoder learning: cooperative multitasking framework + BULL learn() prototype.
 * 這一版讓每個 learner 直接呼叫 BULL 的 learn()，
 * 其中 membership 一律回 true，equivalence 會檢查 b 是否為 tautology。
 * 目前 equivalence 使用 Z3 solver，檢查 ¬b 是否 SAT。
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

// Z3 C API（你已經安裝 libz3-dev）
#include <z3.h>
 
// BULL core headers，提供 learn() / boolformula_t / bitvector 等型別
#include "../core/type.h"
#include "../core/bitvector.h"
#include "../core/boolformula.h"
#include "../core/query.h"
#include "../core/cdnf.h"

 #ifdef _WIN32
 #define EXPORT __declspec(dllexport)
 #else
 #define EXPORT __attribute__((visibility("default")))
 #endif
 
 // ============================================================================
 // 協程與 Learner 狀態定義
 // ============================================================================
 #define STACK_SIZE (64 * 1024) // 每個 Learner 分配 64KB 獨立 Stack
 
 typedef enum {
     L_INIT,
     L_RUNNING,
     L_DONE
 } LearnerState;
 
 typedef struct {
     int id;
     const char *name;
     LearnerState state;
     bool counted_as_done;
     boolformula_t *result_formula; // learn() 回傳的公式，接到階段 3 輸出
     
     ucontext_t ctx;     // 儲存此 Learner 的 CPU 暫存器狀態
     void *stack_memory; // 獨立的 Stack 記憶體
 } LearnerContext;
 
 // 全域/靜態變數供 Dispatcher 與 Learner 進行 Context Switch
 static ucontext_t dispatcher_ctx;
 static LearnerContext *global_learners = NULL;
 static int current_learner_id = -1;
static int global_num_meas = 0;  // 測量向量長度，供 learn() 的 num_vars 使用
 
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

// Membership Query prototype：不看 info / bv，一律回傳 true
static membership_result_t proto_membership(void *info, bitvector *bv) {
    (void)info;
    (void)bv;
    return true;
}

// ---------------------------------------------------------------------------
// 輔助：把 boolformula_t encode 成 Z3 AST
//   - 變數編號從 1 開始，到 num_vars
//   - vars[v] 表示第 v 個 Z3 Bool 變數
// ---------------------------------------------------------------------------
static Z3_ast encode_boolformula_to_z3(Z3_context ctx, boolformula_t *f, Z3_ast *vars) {
    switch (boolformula_get_type(f)) {
        case literal: {
            lit l = boolformula_get_value(f);
            var v = boolformula_var_from_lit(l);
            Z3_ast base = vars[v];
            return boolformula_positive_lit(l) ? base : Z3_mk_not(ctx, base);
        }
        case conjunct: {
            uscalar_t len = boolformula_get_length(f);
            if (len == 0) {
                return Z3_mk_true(ctx);
            }
            Z3_ast *children = (Z3_ast *)malloc(sizeof(Z3_ast) * len);
            for (uscalar_t i = 0; i < len; ++i) {
                boolformula_t *sub = boolformula_get_subformula(f, i);
                children[i] = encode_boolformula_to_z3(ctx, sub, vars);
            }
            Z3_ast res = Z3_mk_and(ctx, (unsigned)len, children);
            free(children);
            return res;
        }
        case disjunct: {
            uscalar_t len = boolformula_get_length(f);
            if (len == 0) {
                return Z3_mk_false(ctx);
            }
            Z3_ast *children = (Z3_ast *)malloc(sizeof(Z3_ast) * len);
            for (uscalar_t i = 0; i < len; ++i) {
                boolformula_t *sub = boolformula_get_subformula(f, i);
                children[i] = encode_boolformula_to_z3(ctx, sub, vars);
            }
            Z3_ast res = Z3_mk_or(ctx, (unsigned)len, children);
            free(children);
            return res;
        }
        case exclusive_disjunct: {
            uscalar_t len = boolformula_get_length(f);
            if (len == 0) {
                return Z3_mk_false(ctx);
            }
            Z3_ast acc = encode_boolformula_to_z3(ctx, boolformula_get_subformula(f, 0), vars);
            for (uscalar_t i = 1; i < len; ++i) {
                boolformula_t *sub = boolformula_get_subformula(f, i);
                Z3_ast next = encode_boolformula_to_z3(ctx, sub, vars);
                acc = Z3_mk_xor(ctx, acc, next);
            }
            return acc;
        }
        default:
            // 理論上不會到這裡
            return Z3_mk_false(ctx);
    }
}

// Equivalence Query prototype：
//   - 使用 Z3 檢查 b 是否「永遠為真」（tautology）
//   - 作法：檢查 ¬b 是否 SAT；若 SAT，從 model 取 counterexample
static equivalence_result_t *proto_equivalence(void *info,
                                               uscalar_t num_vars,
                                               boolformula_t *b) {
    (void)info;

    equivalence_result_t *res = (equivalence_result_t *)malloc(sizeof(equivalence_result_t));
    if (!res) return NULL;
    res->is_equal = true;
    res->counterexample = NULL;

    // 根據實際公式算出需要的變數個數（可能 <= num_vars）
    scalar_t fv = boolformula_num_of_var(b);
    if (fv <= 0) {
        // 沒有變數，表示常數式：這裡當作「永遠為真」
        return res;
    }

    uscalar_t n = (uscalar_t)fv;

    // 建立 Z3 context
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // 準備變數陣列：vars[v] 對應第 v 個布林變數
    Z3_ast *vars = (Z3_ast *)calloc(n + 1, sizeof(Z3_ast));
    if (!vars) {
        Z3_del_context(ctx);
        return res;
    }

    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    for (uscalar_t v = 1; v <= n; ++v) {
        char name_buf[32];
        snprintf(name_buf, sizeof(name_buf), "x%u", (unsigned)v);
        Z3_symbol sym = Z3_mk_string_symbol(ctx, name_buf);
        vars[v] = Z3_mk_const(ctx, sym, bool_sort);
    }

    // b → Z3 AST
    Z3_ast phi = encode_boolformula_to_z3(ctx, b, vars);
    Z3_ast not_phi = Z3_mk_not(ctx, phi);

    // 建立 solver 並檢查 ¬b 是否 SAT
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_solver_assert(ctx, solver, not_phi);

    Z3_lbool r = Z3_solver_check(ctx, solver);
    if (r == Z3_L_FALSE) {
        // ¬b UNSAT → b 為 tautology
        Z3_solver_dec_ref(ctx, solver);
        free(vars);
        Z3_del_context(ctx);
        return res;
    }

    if (r != Z3_L_TRUE) {
        // Z3_L_UNDEF 等情況下，保守視為等價
        Z3_solver_dec_ref(ctx, solver);
        free(vars);
        Z3_del_context(ctx);
        return res;
    }

    // SAT：取得 model，構造 counterexample
    Z3_model model = Z3_solver_get_model(ctx, solver);
    Z3_model_inc_ref(ctx, model);

    bitvector *cex = bitvector_new(n + 1);
    for (uscalar_t v = 1; v <= n; ++v) {
        Z3_ast val_ast = NULL;
        bool bit = false;
        /* 第四個參數 model_completion = 1，讓 Z3 自動補完未定義的變數 */
        (void)Z3_model_eval(ctx, model, vars[v], 1, &val_ast);
        if (val_ast != NULL) {
            Z3_lbool bv = Z3_get_bool_value(ctx, val_ast);
            bit = (bv == Z3_L_TRUE);
        }
        bitvector_set(cex, v - 1, bit);
    }
    // 最後一個 bit 對應 membership 結果，這裡 proto_membership 一律 true
    bitvector_set(cex, n, true);

    res->is_equal = false;
    res->counterexample = cex;

    Z3_model_dec_ref(ctx, model);
    Z3_solver_dec_ref(ctx, solver);
    free(vars);
    Z3_del_context(ctx);

    return res;
}

// ---------------------------------------------------------------------------
// 輔助：把 boolformula_t 轉成 Z3 / SMT-LIB2 字串，供階段 3 傳回 Python
// 變數為 x1, x2, ...；格式 (and ...), (or ...), (xor ...), (not x1)
// 回傳值為 malloc，caller 須 free
// ---------------------------------------------------------------------------
#define Z3_SMT2_BUF 8192
static int formula_append_z3_smt2(boolformula_t *f, char *buf, int size, int pos) {
    if (pos >= size - 1) return -1;
    switch (boolformula_get_type(f)) {
        case literal: {
            lit l = boolformula_get_value(f);
            var v = boolformula_var_from_lit(l);
            if (boolformula_positive_lit(l)) {
                int n = snprintf(buf + pos, (size_t)(size - pos), "x%u", (unsigned)v);
                return (n < 0 || pos + n >= size) ? -1 : pos + n;
            } else {
                int n = snprintf(buf + pos, (size_t)(size - pos), "(not x%u)", (unsigned)v);
                return (n < 0 || pos + n >= size) ? -1 : pos + n;
            }
        }
        case conjunct: {
            uscalar_t len = boolformula_get_length(f);
            if (len == 0) {
                int n = snprintf(buf + pos, (size_t)(size - pos), "true");
                return (n < 0 || pos + n >= size) ? -1 : pos + n;
            }
            if (pos + 6 >= size) return -1;
            memcpy(buf + pos, "(and ", 5);
            pos += 5;
            for (uscalar_t i = 0; i < len; i++) {
                pos = formula_append_z3_smt2(boolformula_get_subformula(f, i), buf, size, pos);
                if (pos < 0) return -1;
                if (i < len - 1 && pos < size) buf[pos++] = ' ';
            }
            if (pos >= size) return -1;
            buf[pos++] = ')';
            return pos;
        }
        case disjunct: {
            uscalar_t len = boolformula_get_length(f);
            if (len == 0) {
                int n = snprintf(buf + pos, (size_t)(size - pos), "false");
                return (n < 0 || pos + n >= size) ? -1 : pos + n;
            }
            if (pos + 5 >= size) return -1;
            memcpy(buf + pos, "(or ", 4);
            pos += 4;
            for (uscalar_t i = 0; i < len; i++) {
                pos = formula_append_z3_smt2(boolformula_get_subformula(f, i), buf, size, pos);
                if (pos < 0) return -1;
                if (i < len - 1 && pos < size) buf[pos++] = ' ';
            }
            if (pos >= size) return -1;
            buf[pos++] = ')';
            return pos;
        }
        case exclusive_disjunct: {
            uscalar_t len = boolformula_get_length(f);
            if (len == 0) {
                int n = snprintf(buf + pos, (size_t)(size - pos), "false");
                return (n < 0 || pos + n >= size) ? -1 : pos + n;
            }
            if (len == 1) {
                return formula_append_z3_smt2(boolformula_get_subformula(f, 0), buf, size, pos);
            }
            /* 多個子式：鏈狀 (xor (xor a b) c) */
            if (pos + 6 >= size) return -1;
            memcpy(buf + pos, "(xor ", 5);
            pos += 5;
            pos = formula_append_z3_smt2(boolformula_get_subformula(f, 0), buf, size, pos);
            if (pos < 0) return -1;
            for (uscalar_t i = 1; i < len; i++) {
                if (pos + 2 >= size) return -1;
                buf[pos++] = ' ';
                pos = formula_append_z3_smt2(boolformula_get_subformula(f, i), buf, size, pos);
                if (pos < 0) return -1;
            }
            if (pos >= size) return -1;
            buf[pos++] = ')';
            return pos;
        }
        default:
            return pos;
    }
}
static char *formula_to_z3_smt2(boolformula_t *f) {
    if (!f) return NULL;
    char *buf = (char *)malloc(Z3_SMT2_BUF);
    if (!buf) return NULL;
    int n = formula_append_z3_smt2(f, buf, Z3_SMT2_BUF, 0);
    if (n < 0) { free(buf); return NULL; }
    buf[n] = '\0';
    return buf;
}

// JSON 跳脫：將 " 與 \ 跳脫，回傳 malloc 字串，caller 須 free
static char *json_escape(const char *s) {
    if (!s) return strdup("");
    size_t len = strlen(s);
    size_t cap = len + 1;
    char *out = (char *)malloc(cap);
    if (!out) return NULL;
    size_t j = 0;
    for (size_t i = 0; s[i]; i++) {
        if (j + 2 > cap) {
            cap *= 2;
            char *n = (char *)realloc(out, cap);
            if (!n) { free(out); return NULL; }
            out = n;
        }
        if (s[i] == '"' || s[i] == '\\') {
            out[j++] = '\\';
            out[j++] = s[i];
        } else {
            out[j++] = s[i];
        }
    }
    out[j] = '\0';
    return out;
}

 static void learner_routine(int id) {
     LearnerContext *me = &global_learners[id];
     me->state = L_RUNNING;
 
     printf("[Learner %d (%s)] 啟動！\n", id, me->name);
 
    // 這裡直接呼叫 BULL 的 learn()，使用簡化版的 membership / equivalence。
    void *info = NULL;
    // 目前先用 meas 的長度當作變數個數；若為 0 則退回 1。
    uscalar_t num_vars = (global_num_meas > 0) ? (uscalar_t)global_num_meas : 1;

    boolformula_t *f = learn(info,
                             num_vars,
                             proto_membership,   // MEM：永遠 true
                             NULL,               // COMEM：目前不用
                             proto_equivalence,  // EQ：答案為 true
                             CDNF);              // 先用最基本模式

    if (f) {
        me->result_formula = f; // 接到階段 3，由主流程寫入 JSON 後再 free
        fprintf(stderr, "[Learner %d (%s)] 公式：", id, me->name);
        boolformula_print(f);
        fprintf(stderr, "\n");
    } else {
        me->result_formula = NULL;
        fprintf(stderr, "[Learner %d] learn() 回傳 NULL（可能是 prototype 還沒接好）。\n", id);
    }

    printf("[Learner %d (%s)] DONE！\n", id, me->name);
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
     (void)smt2_str;
    (void)meas_names;
     (void)all_commute_name;
 
    if (num_decoders <= 0 || num_meas <= 0) {
         char *empty = (char *)malloc(3);
         if (empty) { empty[0] = '{'; empty[1] = '}'; empty[2] = '\0'; }
         return empty;
     }
 
     // ---------------------------------------------------------
     // 階段 1：初始化所有的 Learner 與其專屬 Stack
     // ---------------------------------------------------------
    global_learners = (LearnerContext *)calloc(num_decoders, sizeof(LearnerContext));
    global_num_meas = num_meas;
     
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
     // 階段 2：主迴圈 Dispatcher (Round-Robin 調度)
     // ---------------------------------------------------------
     printf("\n=== 進入 Dispatcher 區域 ===\n");
     int active_learners = num_decoders;
     int current_idx = 0;
 
     // 只要還有 Learner 沒 DONE，Dispatcher 就繼續輪詢
     while (active_learners > 0) {
         LearnerContext *l = &global_learners[current_idx];
 
         if (l->state != L_DONE) {
             current_learner_id = current_idx;
             
             // 【跳轉核心】: Dispatcher 決定把控制權交給 current_idx
             swapcontext(&dispatcher_ctx, &l->ctx);
             
             // 【控制權回歸】: Learner 呼叫了 yield，一律回到這裡
             if (l->state == L_DONE && !l->counted_as_done) {
                 l->counted_as_done = true;
                 active_learners--;
             }
         }
         
         // 換下一棒 (Round-Robin)
         current_idx = (current_idx + 1) % num_decoders;
     }
     printf("=== Dispatcher 結束：所有 Learner 皆已 DONE ===\n\n");
 
     // ---------------------------------------------------------
     // 階段 3：收集答案並產生 JSON（公式轉成 Z3/SMT-LIB2 格式再傳回 Python）
     // ---------------------------------------------------------
     size_t buf_size = 256;
     char *json = (char *)malloc(buf_size);
     if (!json) goto cleanup;
     
     json[0] = '{';
     size_t pos = 1;
 
     for (int i = 0; i < num_decoders; i++) {
         const char *name = decoder_names[i] ? decoder_names[i] : "";
         char *formula_str = NULL;
         char *value_str = NULL;
         if (global_learners[i].result_formula) {
             formula_str = formula_to_z3_smt2(global_learners[i].result_formula);
             value_str = formula_str ? json_escape(formula_str) : strdup("null");
         } else {
             value_str = strdup("null");
         }
         if (!value_str) { free(formula_str); free(json); goto cleanup; }
         if (i > 0) {
             if (pos + 2 >= buf_size) {
                 buf_size *= 2;
                 char *n = (char *)realloc(json, buf_size);
                 if (!n) { free(value_str); free(formula_str); free(json); goto cleanup; }
                 json = n;
             }
             json[pos++] = ',';
             json[pos++] = ' ';
         }
         size_t need = 6 + strlen(name) * 2 + strlen(value_str) * 2 + 16;
         while (pos + need >= buf_size) {
             buf_size *= 2;
             char *n = (char *)realloc(json, buf_size);
             if (!n) { free(value_str); free(formula_str); free(json); goto cleanup; }
             json = n;
         }
         pos += (size_t)sprintf(json + pos, "\"%s\": \"%s\"", name, value_str);
         free(value_str);
         free(formula_str);
     }
 
     if (pos + 2 >= buf_size) {
         buf_size = pos + 3;
         char *n = (char *)realloc(json, buf_size);
         if (!n) { free(json); goto cleanup; }
         json = n;
     }
     json[pos++] = '}';
     json[pos] = '\0';
 
 cleanup:
     // 清理分配的 Stack、result_formula 與結構
     for (int i = 0; i < num_decoders; i++) {
         if (global_learners[i].result_formula) {
             boolformula_free(global_learners[i].result_formula);
         }
         free(global_learners[i].stack_memory);
     }
     free(global_learners);
 
     return json;
 }
 
 EXPORT void free_c_string(char *ptr) {
     if (ptr) free(ptr);
 }