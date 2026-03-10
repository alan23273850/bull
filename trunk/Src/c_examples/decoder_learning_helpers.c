/*
 * Decoder learning helpers (Implementation)
 *
 * 本檔案實作了 decoder_learning 所需的輔助函式：
 * 1. eval_boolformula_with_vals: 在給定的變數賦值下，評估 boolformula_t 的真假值。
 * 2. formula_to_z3_smt2: 將 BULL 的 boolformula_t 轉換為 Z3 SMT-LIB2 格式的字串，並支援自訂變數名稱。
 * 3. json_escape: 處理字串的 JSON 逸出字元。
 * 4. meas_bv_to_key: 將 BULL 的 bitvector 轉換為對應的表格索引 (key)。
 * 5. fill_meas_table_row_for_mq: 在 MQ 查表未命中時，為所有 Learner 產生並填入一列表格資料。
 * 6. cleanup_learning_resources: 統一釋放學習過程中配置的各項全域與區域記憶體。
 * 7. build_results_json: 將所有 Learner 的結果打包成 JSON 格式字串回傳。
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "decoder_learning_helpers.h"

// 在給定 valuation vals[1..n] 下評估 boolformula_t
bool eval_boolformula_with_vals(boolformula_t *f, const bool *vals) {
    if (!f) return false;
    switch (boolformula_get_type(f)) {
        case literal: {
            lit l = boolformula_get_value(f);
            var v = boolformula_var_from_lit(l);
            bool b = vals[v];
            return boolformula_positive_lit(l) ? b : !b;
        }
        case conjunct: {
            uscalar_t len = boolformula_get_length(f);
            for (uscalar_t i = 0; i < len; i++)
                if (!eval_boolformula_with_vals(boolformula_get_subformula(f, i), vals)) return false;
            return true;
        }
        case disjunct: {
            uscalar_t len = boolformula_get_length(f);
            for (uscalar_t i = 0; i < len; i++)
                if (eval_boolformula_with_vals(boolformula_get_subformula(f, i), vals)) return true;
            return false;
        }
        case exclusive_disjunct: {
            uscalar_t len = boolformula_get_length(f);
            bool acc = false;
            for (uscalar_t i = 0; i < len; i++)
                if (eval_boolformula_with_vals(boolformula_get_subformula(f, i), vals)) acc = !acc;
            return acc;
        }
        default:
            return false;
    }
}

#define Z3_SMT2_BUF 8192

static int formula_append_z3_smt2(boolformula_t *f, char *buf, int size, int pos, const char **global_meas_names, int global_num_meas) {
    if (pos >= size - 1) return -1;
    switch (boolformula_get_type(f)) {
        case literal: {
            lit l = boolformula_get_value(f);
            var v = boolformula_var_from_lit(l);
            const char *var_name = NULL;
            if (global_meas_names && v >= 1 && v <= (var)global_num_meas && global_meas_names[v - 1] && global_meas_names[v - 1][0])
                var_name = global_meas_names[v - 1];
            
            int need_pipe = 0;
            if (var_name) {
                for (const char *p = var_name; *p; p++)
                    if (*p == ' ' || *p == '(' || *p == ')' || *p == '|' || *p == '\\') { need_pipe = 1; break; }
            }
            if (boolformula_positive_lit(l)) {
                if (var_name) {
                    int n = need_pipe ? snprintf(buf + pos, (size_t)(size - pos), "|%s|", var_name)
                                      : snprintf(buf + pos, (size_t)(size - pos), "%s", var_name);
                    return (n < 0 || pos + n >= size) ? -1 : pos + n;
                } else {
                    int n = snprintf(buf + pos, (size_t)(size - pos), "x%u", (unsigned)v);
                    return (n < 0 || pos + n >= size) ? -1 : pos + n;
                }
            } else {
                if (var_name) {
                    int n = need_pipe ? snprintf(buf + pos, (size_t)(size - pos), "(not |%s|)", var_name)
                                      : snprintf(buf + pos, (size_t)(size - pos), "(not %s)", var_name);
                    return (n < 0 || pos + n >= size) ? -1 : pos + n;
                } else {
                    int n = snprintf(buf + pos, (size_t)(size - pos), "(not x%u)", (unsigned)v);
                    return (n < 0 || pos + n >= size) ? -1 : pos + n;
                }
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
                pos = formula_append_z3_smt2(boolformula_get_subformula(f, i), buf, size, pos, global_meas_names, global_num_meas);
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
                pos = formula_append_z3_smt2(boolformula_get_subformula(f, i), buf, size, pos, global_meas_names, global_num_meas);
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
                return formula_append_z3_smt2(boolformula_get_subformula(f, 0), buf, size, pos, global_meas_names, global_num_meas);
            }
            if (pos + 6 >= size) return -1;
            memcpy(buf + pos, "(xor ", 5);
            pos += 5;
            pos = formula_append_z3_smt2(boolformula_get_subformula(f, 0), buf, size, pos, global_meas_names, global_num_meas);
            if (pos < 0) return -1;
            for (uscalar_t i = 1; i < len; i++) {
                if (pos + 2 >= size) return -1;
                buf[pos++] = ' ';
                pos = formula_append_z3_smt2(boolformula_get_subformula(f, i), buf, size, pos, global_meas_names, global_num_meas);
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

char *formula_to_z3_smt2(boolformula_t *f, const char **global_meas_names, int global_num_meas) {
    if (!f) return NULL;
    char *buf = (char *)malloc(Z3_SMT2_BUF);
    if (!buf) return NULL;
    int n = formula_append_z3_smt2(f, buf, Z3_SMT2_BUF, 0, global_meas_names, global_num_meas);
    if (n < 0) { free(buf); return NULL; }
    buf[n] = '\0';
    return buf;
}

char *json_escape(const char *s) {
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

#ifdef _WIN32
#define EXPORT __declspec(dllexport)
#else
#define EXPORT __attribute__((visibility("default")))
#endif

EXPORT void free_c_string(char *ptr) {
    if (ptr) free(ptr);
}

// 清理所有全域與配置的記憶體
void cleanup_learning_resources(MeasToDecodersEntry **meas_to_decoders_table_ptr, size_t meas_table_size,
                                boolformula_t ***pending_formula_ptr, int num_decoders,
                                equivalence_result_t ***eq_pending_result_ptr,
                                LearnerContext **global_learners_ptr) {
    if (meas_to_decoders_table_ptr && *meas_to_decoders_table_ptr) {
        MeasToDecodersEntry *table = *meas_to_decoders_table_ptr;
        for (size_t k = 0; k < meas_table_size; k++) {
            free(table[k].c);
        }
        free(table);
        *meas_to_decoders_table_ptr = NULL;
    }
    if (pending_formula_ptr && *pending_formula_ptr) {
        boolformula_t **pf = *pending_formula_ptr;
        for (int i = 0; i < num_decoders; i++) {
            if (pf[i]) boolformula_free(pf[i]);
        }
        free(pf);
        *pending_formula_ptr = NULL;
    }
    if (eq_pending_result_ptr && *eq_pending_result_ptr) {
        free(*eq_pending_result_ptr);
        *eq_pending_result_ptr = NULL;
    }
    if (global_learners_ptr && *global_learners_ptr) {
        LearnerContext *gl = *global_learners_ptr;
        for (int i = 0; i < num_decoders; i++) {
            if (gl[i].result_formula) {
                boolformula_free(gl[i].result_formula);
            }
            free(gl[i].stack_memory);
        }
        free(gl);
        *global_learners_ptr = NULL;
    }
}

char *build_results_json(LearnerContext *learners, int num_decoders, const char **decoder_names, const char **global_meas_names, int global_num_meas) {
    size_t buf_size = 256;
    char *json = (char *)malloc(buf_size);
    if (!json) return NULL;
    
    json[0] = '{';
    size_t pos = 1;

    for (int i = 0; i < num_decoders; i++) {
        const char *name = decoder_names[i] ? decoder_names[i] : "";
        char *formula_str = NULL;
        char *value_str = NULL;
        if (learners[i].result_formula) {
            formula_str = formula_to_z3_smt2(learners[i].result_formula, global_meas_names, global_num_meas);
            value_str = formula_str ? json_escape(formula_str) : strdup("null");
        } else {
            value_str = strdup("null");
        }
        if (!value_str) { free(formula_str); free(json); return NULL; }
        if (i > 0) {
            if (pos + 2 >= buf_size) {
                buf_size *= 2;
                char *n = (char *)realloc(json, buf_size);
                if (!n) { free(value_str); free(formula_str); free(json); return NULL; }
                json = n;
            }
            json[pos++] = ',';
            json[pos++] = ' ';
        }
        size_t need = 6 + strlen(name) * 2 + strlen(value_str) * 2 + 16;
        while (pos + need >= buf_size) {
            buf_size *= 2;
            char *n = (char *)realloc(json, buf_size);
            if (!n) { free(value_str); free(formula_str); free(json); return NULL; }
            json = n;
        }
        pos += (size_t)sprintf(json + pos, "\"%s\": \"%s\"", name, value_str);
        free(value_str);
        free(formula_str);
    }

    if (pos + 2 >= buf_size) {
        buf_size = pos + 3;
        char *n = (char *)realloc(json, buf_size);
        if (!n) { free(json); return NULL; }
        json = n;
    }
    json[pos++] = '}';
    json[pos] = '\0';
    return json;
}

// 把測量向量 bv 轉成表格 key。BULL 慣例：index 0 為輸出/特殊，index 1..length-1 為輸入，故只取 1..length-1 建 key
size_t meas_bv_to_key(bitvector *bv) {
    if (!bv || bitvector_length(bv) <= 1) return 0;
    size_t len = (size_t)bitvector_length(bv);
    size_t n = len - 1;  /* 輸入 bit 數 = indices 1..length-1 */
    if (n > sizeof(size_t) * 8) n = sizeof(size_t) * 8;
    size_t key = 0;
    for (size_t i = 1; i < len && (i - 1) < sizeof(size_t) * 8; i++) {
        if (bitvector_get(bv, (uscalar_t)i)) key |= (size_t)1 << (i - 1);
    }
    return key;
}

// MQ 填表時：當前 learner 用隨機，其他 learner 用其 conjecture 評估結果，不讓其他人因此列出現反例
void fill_meas_table_row_for_mq(size_t key, int current_id, size_t meas_table_size, MeasToDecodersEntry *meas_to_decoders_table, int num_global_decoders, int global_num_meas, boolformula_t **pending_formula) {
    if (key >= meas_table_size || !meas_to_decoders_table || current_id < 0 || current_id >= num_global_decoders) return;
    MeasToDecodersEntry *e = &meas_to_decoders_table[key];
    if (!e->c) return;
    int n = global_num_meas > 0 ? global_num_meas : 1;
    bool *vals = (bool *)malloc((size_t)(n + 1) * sizeof(bool));
    if (!vals) return;
    for (int v = 1; v <= n; v++)
        vals[v] = ((key >> (v - 1)) & 1) != 0;
    for (int j = 0; j < num_global_decoders; j++) {
        if (j == current_id)
            e->c[j] = (rand() & 1) != 0;
        else
            e->c[j] = pending_formula && pending_formula[j]
                ? eval_boolformula_with_vals(pending_formula[j], vals)
                : (rand() & 1) != 0;
    }
    e->valid = true;
    free(vals);
    fprintf(stderr, "[Table] MQ 填 key=%zu columns:", key);
    for (int d = 0; d < num_global_decoders; d++)
        fprintf(stderr, " %d", e->c[d] ? 1 : 0);
    fprintf(stderr, "\n");
}
