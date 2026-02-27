/*
 * minisat.cc
 *
 *  Created on: 2011/8/29
 *      Author: Yu-Fang Chen
 *  Modified to use ABC via external file
 */

#include <errno.h>
#include <signal.h>
#include <zlib.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"
#include "minisat_stub.h"

extern "C" void sat_result_free(sat_result_t* r){
	if(r->is_sat==1)
		free(r->counterexample);
	free(r);
}

extern "C" sat_result_t* solve(int** clauses, int num_of_clauses){
    sat_result_t* res=(sat_result_t*)malloc(sizeof(sat_result_t));
    
    // Find max variable to set number of variables properly
    int max_var = 0;
    for (int i = 0; i < num_of_clauses; i++) {
        int* clause = clauses[i];
        for (int j = 0; clause[j] != 0; j++) {
            int v = abs(clause[j]);
            if (v > max_var) max_var = v;
        }
    }
    
    // Write out the CNF file
    char filename[256];
    sprintf(filename, "/tmp/bull_solve_%d.cnf", getpid());
    FILE* fcnf = fopen(filename, "w");
    if (!fcnf) {
        perror("Failed to create temporary CNF file");
        res->is_sat = 0;
        return res;
    }
    
    // ABC requires exactly the declared number of variables
    fprintf(fcnf, "p cnf %d %d\n", max_var, num_of_clauses);
    for (int i = 0; i < num_of_clauses; i++) {
        int* clause = clauses[i];
        for (int j = 0; clause[j] != 0; j++) {
            fprintf(fcnf, "%d ", clause[j]);
        }
        fprintf(fcnf, "0\n");
    }
    fclose(fcnf);
    
    // Call ABC
    char cmd[1024];
    char out_filename[256];
    char cex_filename[256];
    sprintf(out_filename, "/tmp/bull_solve_%d.out", getpid());
    sprintf(cex_filename, "/tmp/bull_solve_%d.cex", getpid());
    
    // Use iprove and write_cex to get the satisfying pattern
    sprintf(cmd, "/home/alan23273850/flag-analysis/abc/abc -c \"read_cnf %s; iprove; write_cex %s\" > %s 2>&1", filename, cex_filename, out_filename);
    int ret = system(cmd);
    
    // Check if SATISFIABLE
    FILE* fout = fopen(out_filename, "r");
    if (!fout) {
        res->is_sat = 0;
        remove(filename);
        remove(cex_filename);
        return res;
    }
    
    res->is_sat = 0;
    res->counterexample = NULL;
    res->cesize = max_var;
    
    char line[4096];
    int is_sat = 0;
    while (fgets(line, sizeof(line), fout)) {
        if (strstr(line, "SATISFIABLE") || strstr(line, "satisfiable") || strstr(line, "Sat")) {
            if (strstr(line, "UNSATISFIABLE") || strstr(line, "Unsatisfiable")) {
                is_sat = 0;
                break;
            } else {
                is_sat = 1;
            }
        }
    }
    fclose(fout);
    
    if (is_sat) {
        FILE* fcex = fopen(cex_filename, "r");
        if (fcex && fgets(line, sizeof(line), fcex)) {
            res->is_sat = 1;
            res->counterexample = (int*)malloc(sizeof(int) * max_var);
            // Initialize everything to 0
            for(int i=0; i<max_var; i++) res->counterexample[i] = 0;
            
            // Format: "001# DONE"
            for (int i = 0; i < max_var && line[i] != '\0' && line[i] != '#'; i++) {
                if (line[i] == '1') {
                    res->counterexample[i] = 1;
                } else if (line[i] == '0') {
                    res->counterexample[i] = 0;
                }
            }
        }
        if (fcex) fclose(fcex);
    }
    
    // Cleanup
    remove(filename);
    remove(out_filename);
    remove(cex_filename);
    
    return res;
}

