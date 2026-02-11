/*****************************************************************************
 *
 *
 * Author: Yu-Fang Chen & Bow-Yaw Wang
 * Copyright reserved
 *****************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "type.h"
#include "bitvector.h"
#include "vector.h"
#include "boolformula.h"

/* variable id's start from 1 */

const lit NOT_A_LITERAL = 0;

void boolformula_print (boolformula_t *f)
{
	switch(f->t){
		case disjunct:
			  if (vector_length (f->d.v) == 0) {
			    fprintf (stderr, "{ F }");
			  } else {
			    uscalar_t i;
			    fprintf (stderr, "{ ");
			    for (i = 0; i < vector_length (f->d.v)-1; i++) {
			      boolformula_print ((boolformula_t*)vector_get (f->d.v, i));
			      fprintf (stderr, " | ");
			    }
			    assert (i == vector_length (f->d.v)-1);
			    boolformula_print ((boolformula_t*)vector_get (f->d.v, vector_length (f->d.v)-1));
			    fprintf (stderr, " }");
			  }
			break;
		case conjunct:
			  if (vector_length (f->d.v) == 0) {
			    fprintf (stderr, "{ T }");
			  } else {
			    uscalar_t i;
			    fprintf (stderr, "{ ");
			    for (i = 0; i < vector_length (f->d.v)-1; i++) {
			      boolformula_print ((boolformula_t*)vector_get (f->d.v, i));
			      fprintf (stderr, " & ");
			    }
			    assert (i == vector_length (f->d.v)-1);
			    boolformula_print ((boolformula_t*)vector_get (f->d.v, vector_length (f->d.v)-1));
			    fprintf (stderr, " }");
			  }
			break;
		case literal:
		      fprintf (stderr, "%ld", (long)f->d.l);
			break;
	}
}

scalar_t boolformula_num_of_var(boolformula_t* f){

	scalar_t cur=0, temp;
	uscalar_t i;
	switch(f->t){
	case literal:
		return (scalar_t)(f->d.l >= 0 ? f->d.l : -f->d.l);
	default:
		for(i=0;i<vector_length(f->d.v);i++){
			temp=boolformula_num_of_var((boolformula_t*)vector_get(f->d.v, i));
			cur=cur > temp?cur:temp;
		}
		break;
	}
	return cur;
}
