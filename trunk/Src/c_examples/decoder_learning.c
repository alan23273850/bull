/*
 * Decoder learning: cooperative multitasking framework.
 * Returns JSON with "true" per decoder; round-robin via ucontext.
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
     
     ucontext_t ctx;     // 儲存此 Learner 的 CPU 暫存器狀態
     void *stack_memory; // 獨立的 Stack 記憶體
 } LearnerContext;
 
 // 全域/靜態變數供 Dispatcher 與 Learner 進行 Context Switch
 static ucontext_t dispatcher_ctx;
 static LearnerContext *global_learners = NULL;
 static int current_learner_id = -1;
 
 // ============================================================================
 // 輔助函式：交出控制權 (Yield)
 // ============================================================================
 // Learner 呼叫此函式，必定會跳回主迴圈的 Dispatcher 區域
 static void yield_to_dispatcher() {
     if (current_learner_id >= 0) {
         swapcontext(&global_learners[current_learner_id].ctx, &dispatcher_ctx);
     }
 }
 
 // 模擬您提到的 @cdnf.c (405-408) 呼叫
 static void mock_call_cdnf_logic(int learner_id) {
     printf("[Learner %d] 呼叫 @cdnf.c (405-408) 相關邏輯...\n", learner_id);
 }
 
 // ============================================================================
 // Learner 的主邏輯 (跑在自己獨立的 Stack 上)
 // ============================================================================
 static void learner_routine(int id) {
     LearnerContext *me = &global_learners[id];
     me->state = L_RUNNING;
 
     printf("[Learner %d (%s)] 啟動！\n", id, me->name);
 
     // --- 模擬 Learner 的運作過程 ---
     // 第一次工作
     mock_call_cdnf_logic(id);
     
     // 【跳轉要求】: 工作告一段落，一律先跳回 Dispatcher
     yield_to_dispatcher();
 
     // 第二次工作 (當 Dispatcher 決定再次跳到這裡時，會從這裡繼續)
     printf("[Learner %d (%s)] 被喚醒，繼續執行第二階段...\n", id, me->name);
     mock_call_cdnf_logic(id);
 
     yield_to_dispatcher();
 
     // --- 結束 ---
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
     (void)num_meas;
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
     
     for (int i = 0; i < num_decoders; i++) {
         global_learners[i].id = i;
         global_learners[i].name = decoder_names[i] ? decoder_names[i] : "Unknown";
         global_learners[i].state = L_INIT;
         global_learners[i].counted_as_done = false;
 
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
     // 階段 3：收集答案並產生 JSON (原有的程式碼)
     // ---------------------------------------------------------
     size_t buf_size = 256;
     char *json = (char *)malloc(buf_size);
     if (!json) goto cleanup;
     
     json[0] = '{';
     size_t pos = 1;
 
     for (int i = 0; i < num_decoders; i++) {
         const char *name = decoder_names[i] ? decoder_names[i] : "";
         if (i > 0) {
             if (pos + 2 >= buf_size) {
                 buf_size *= 2;
                 char *n = (char *)realloc(json, buf_size);
                 if (!n) { free(json); goto cleanup; }
                 json = n;
             }
             json[pos++] = ',';
             json[pos++] = ' ';
         }
         size_t need = 6 + strlen(name) * 2 + 16;
         while (pos + need >= buf_size) {
             buf_size *= 2;
             char *n = (char *)realloc(json, buf_size);
             if (!n) { free(json); goto cleanup; }
             json = n;
         }
         pos += (size_t)sprintf(json + pos, "\"%s\": \"true\"", name);
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
     // 清理分配的 Stack 與結構
     for (int i = 0; i < num_decoders; i++) {
         free(global_learners[i].stack_memory);
     }
     free(global_learners);
 
     return json;
 }
 
 EXPORT void free_c_string(char *ptr) {
     if (ptr) free(ptr);
 }