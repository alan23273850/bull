/*
 * Decoder learning helpers (Header)
 *
 * 本檔案定義了 decoder_learning 所需的輔助資料結構與函式宣告。
 * 包含：
 * - 協程與 Learner 狀態定義 (LearnerContext, LearnerState)
 * - 表格項目定義 (MeasToDecodersEntry)
 * - boolformula 評估與 Z3 SMT-LIB2 格式轉換
 * - 記憶體清理與 JSON 輸出生成
 */
#ifndef DECODER_LEARNING_HELPERS_H
#define DECODER_LEARNING_HELPERS_H

#include <stdbool.h>
#include <stddef.h>
#if !defined(_WIN32)
#include <ucontext.h>
#endif
#include <z3.h>
#include "../core/type.h"
#include "../core/bitvector.h"
#include "../core/boolformula.h"
#include "../core/query.h"

// ============================================================================
// 協程與 Learner 狀態定義
// ============================================================================
#define STACK_SIZE (64 * 1024) // 每個 Learner 分配 64KB 獨立 Stack

typedef enum {
    L_INIT,
    L_RUNNING,
    L_WAIT_EQ,  // 在 EQ 等待 global 檢查結果
    L_DONE
} LearnerState;

typedef struct {
    int id;
    const char *name;
    LearnerState state;
    bool counted_as_done;
    boolformula_t *result_formula; // learn() 回傳的公式，接到階段 3 輸出

#if !defined(_WIN32)
    ucontext_t ctx;     // 儲存此 Learner 的 CPU 暫存器狀態
#else
    void *ctx;
#endif
    void *stack_memory; // 獨立的 Stack 記憶體
} LearnerContext;

// 表格：meas（測量結果）→ 各 decoder 的輸出
// key = 測量向量的整數編碼 (0 .. 2^num_meas - 1)，value = 每個 decoder 的 bool 輸出
typedef struct {
    bool valid;
    bool *c;  // 長度 num_decoders，c[d] = decoder d 在該 meas 下的輸出
} MeasToDecodersEntry;

// 評估 boolformula_t (給定 bool 陣列 vals[1..n])
bool eval_boolformula_with_vals(boolformula_t *f, const bool *vals);

// 把 boolformula_t 轉成 Z3/SMT-LIB2 字串
// global_meas_names：變數名稱陣列（長度 global_num_meas），用來還原變數名
char *formula_to_z3_smt2(boolformula_t *f, const char **global_meas_names, int global_num_meas);

// JSON 字串跳脫
char *json_escape(const char *s);

// 把測量向量 bv 轉成表格 key。BULL 慣例：index 0 為輸出/特殊，index 1..length-1 為輸入，故只取 1..length-1 建 key
size_t meas_bv_to_key(bitvector *bv);

// 將 boolformula_t 轉換為 Z3_ast（供 solver 使用）
Z3_ast encode_boolformula_to_z3_ast(Z3_context ctx, boolformula_t *f, Z3_ast *meas_vars);

// MQ 查不到表時，用 Z3 求解並填入該列；table_valid_entries 可為 NULL 或傳入指標以累加
void fill_meas_table_row_with_z3(Z3_context ctx, Z3_solver solver, Z3_ast *meas_vars, Z3_ast *dec_vars, Z3_ast all_commute,
    size_t key, size_t meas_table_size, MeasToDecodersEntry *meas_to_decoders_table, int num_global_decoders, int global_num_meas,
    int *table_valid_entries);

// MQ 填表時：當前 learner 用隨機，其他 learner 用其 conjecture 評估結果，不讓其他人因此列出現反例
void fill_meas_table_row_for_mq(size_t key, int current_id, size_t meas_table_size, MeasToDecodersEntry *meas_to_decoders_table, int num_global_decoders, int global_num_meas, boolformula_t **pending_formula);

// 清理所有全域與配置的記憶體
void cleanup_learning_resources(MeasToDecodersEntry **meas_to_decoders_table_ptr, size_t meas_table_size,
                                boolformula_t ***pending_formula_ptr, int num_decoders,
                                equivalence_result_t ***eq_pending_result_ptr,
                                LearnerContext **global_learners_ptr);

// 根據所有 learner 的結果建立回傳的 JSON 字串
char *build_results_json(LearnerContext *global_learners, int num_decoders, const char **decoder_names, const char **global_meas_names, int global_num_meas);

#endif // DECODER_LEARNING_HELPERS_H
