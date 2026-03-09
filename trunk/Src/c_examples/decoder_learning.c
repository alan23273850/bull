/*
 * Decoder learning: fake solution only.
 * Returns JSON with "true" per decoder (fake solution); no real learning.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#define EXPORT __declspec(dllexport)
#else
#define EXPORT __attribute__((visibility("default")))
#endif

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

    size_t buf_size = 256;
    char *json = (char *)malloc(buf_size);
    if (!json) return NULL;
    json[0] = '{';
    size_t pos = 1;

    for (int i = 0; i < num_decoders; i++) {
        const char *name = decoder_names[i] ? decoder_names[i] : "";
        if (i > 0) {
            if (pos + 2 >= buf_size) {
                buf_size *= 2;
                char *n = (char *)realloc(json, buf_size);
                if (!n) { free(json); return NULL; }
                json = n;
            }
            json[pos++] = ',';
            json[pos++] = ' ';
        }
        size_t need = 6 + strlen(name) * 2 + 16;
        while (pos + need >= buf_size) {
            buf_size *= 2;
            char *n = (char *)realloc(json, buf_size);
            if (!n) { free(json); return NULL; }
            json = n;
        }
        pos += (size_t)sprintf(json + pos, "\"%s\": \"true\"", name);
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

EXPORT void free_c_string(char *ptr) {
    if (ptr) free(ptr);
}
