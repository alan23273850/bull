/*****************************************************************************
 *
 *
 * Author: Yu-Fang Chen & Bow-Yaw Wang
 * Copyright reserved
 *****************************************************************************/

#ifndef _BOOLFORMULA_H_
#define _BOOLFORMULA_H_

#include "type.h"
#include "vector.h"
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#ifndef __cplusplus
#include <stdbool.h>
#endif

typedef uscalar_t var;
typedef scalar_t lit;
extern const lit NOT_A_LITERAL;

enum type{disjunct, conjunct, exclusive_disjunct, literal};

union data {
    lit l;
    vector* v;
};

typedef struct {
	uscalar_t ref;
	enum type t;
	union data d;
} boolformula_t;

static inline lit boolformula_lit_from_var (var v)
{
  assert (v > 0);
  return v;
}

static inline var boolformula_var_from_lit (lit l)
{
  assert (l != 0);
  return l > 0 ? l : -l;
}

static inline lit boolformula_lit_complement (lit l)
{
  assert (l != 0);
  return -l;
}

static inline bool boolformula_positive_lit (lit l)
{
  assert (l != 0);
  return l > 0;
}

static inline boolformula_t *boolformula_disjunction_unit (void)
{
	boolformula_t* ret=(boolformula_t*)malloc(sizeof(boolformula_t));
	ret->d.v=vector_new(0);
	ret->t=disjunct;
	ret->ref=1;
	return ret;
}

static inline boolformula_t *boolformula_disjunction_new (uscalar_t length)
{
	boolformula_t* ret=(boolformula_t*)malloc(sizeof(boolformula_t));
	ret->d.v=vector_new(length);
	ret->t=disjunct;
	ret->ref=1;
	return ret;
}

static inline boolformula_t *boolformula_conjunction_unit (void)
{
	boolformula_t* ret=(boolformula_t*)malloc(sizeof(boolformula_t));
	ret->d.v=vector_new(0);
	ret->t=conjunct;
	ret->ref=1;
	return ret;
}

static inline boolformula_t *boolformula_conjunction_new (uscalar_t length)
{
	boolformula_t* ret=(boolformula_t*)malloc(sizeof(boolformula_t));
	ret->t=conjunct;
	ret->d.v=vector_new(length);
	ret->ref=1;
	return ret;
}

static inline boolformula_t *boolformula_literal_new (lit l)
{
	boolformula_t* ret=(boolformula_t*)malloc(sizeof(boolformula_t));
	ret->d.l=l;
	ret->t=literal;
	ret->ref=1;
	return ret;
}

static inline boolformula_t *boolformula_xor_unit (void)
{
	boolformula_t* ret=(boolformula_t*)malloc(sizeof(boolformula_t));
	ret->d.v=vector_new(0);
	ret->t=exclusive_disjunct;
	ret->ref=1;
	return ret;
}

static inline boolformula_t *boolformula_xor_new (uscalar_t length)
{
	boolformula_t* ret=(boolformula_t*)malloc(sizeof(boolformula_t));
	ret->d.v=vector_new(length);
	ret->t=exclusive_disjunct;
	ret->ref=1;
	return ret;
}

static inline boolformula_t *boolformula_add (boolformula_t *f, boolformula_t *g)
{
	assert(f->t!=literal);
	vector_add (f->d.v, g);
	g->ref++;
	return f;
}

static inline boolformula_t *boolformula_set (boolformula_t *f, uscalar_t idx, boolformula_t *g)
{
	assert(f->t!=literal);
	vector_set (f->d.v, idx, g);
	g->ref++;
	return f;
}

static inline void boolformula_free (boolformula_t *f)
{
	if(f->ref>1){
		f->ref--;
		return;
	}
	if(f->t!=literal){
		uscalar_t num_of_subformulae = vector_length (f->d.v);
		int i;
		for (i = 0; i < (int)num_of_subformulae; i++) {
			boolformula_free((boolformula_t*)vector_get (f->d.v, i));
		}
		vector_free (f->d.v);
	}
	free(f);
}

static inline boolformula_t* boolformula_neg (boolformula_t * f){
	int num_of_subformulae;
	int i;
	switch(f->t){
		case disjunct:
			f->t=conjunct;
			num_of_subformulae = (int)vector_length (f->d.v);
			for (i = 0; i < num_of_subformulae; i++) {
			  boolformula_neg((boolformula_t*)vector_get (f->d.v, i));
			}
			break;
		case conjunct:
			f->t=disjunct;
			num_of_subformulae = (int)vector_length (f->d.v);
			for (i = 0; i < num_of_subformulae; i++) {
			  boolformula_neg((boolformula_t*)vector_get (f->d.v, i));
			}
			break;
		case exclusive_disjunct:
			/* ¬(a⊕b⊕c) = (¬a)⊕b⊕c */
			if (vector_length (f->d.v) > 0)
				boolformula_neg((boolformula_t*)vector_get (f->d.v, 0));
			break;
		case literal:
			f->d.l=-f->d.l;
			break;
	}
	return f;
}

static inline boolformula_t *boolformula_copy(boolformula_t * f){
	boolformula_t* ret=NULL, *temp;
	uscalar_t i;
	switch(f->t){
	case conjunct:
		ret=boolformula_conjunction_new(vector_length(f->d.v));
		for(i=0;i<vector_length(f->d.v);i++){
			temp=boolformula_copy((boolformula_t*)vector_get(f->d.v,i));
			boolformula_set(ret,i, temp);
			boolformula_free(temp);
		}
		break;
	case disjunct:
		ret=boolformula_disjunction_new(vector_length(f->d.v));
		for(i=0;i<vector_length(f->d.v);i++){
			temp=boolformula_copy((boolformula_t*)vector_get(f->d.v,i));
			boolformula_set(ret,i, temp);
			boolformula_free(temp);
		}
		break;
	case exclusive_disjunct:
		ret=boolformula_xor_new(vector_length(f->d.v));
		for(i=0;i<vector_length(f->d.v);i++){
			temp=boolformula_copy((boolformula_t*)vector_get(f->d.v,i));
			boolformula_set(ret,i, temp);
			boolformula_free(temp);
		}
		break;
	case literal:
		ret=boolformula_literal_new(f->d.l);
		break;
	}
	assert(f->t==ret->t);
	return ret;
}

/* Add clauses for x ≡ a (equivalence): (¬x∨a) ∧ (¬a∨x) */
static inline void add_lit_equiv_clauses(boolformula_t* ret, lit x, lit a){
	boolformula_t* dis;
	dis = boolformula_disjunction_new(2);
	boolformula_set(dis, 0, boolformula_literal_new(boolformula_lit_complement(x)));
	boolformula_set(dis, 1, boolformula_literal_new(a));
	boolformula_add(ret, dis);
	boolformula_free(dis);
	dis = boolformula_disjunction_new(2);
	boolformula_set(dis, 0, boolformula_literal_new(boolformula_lit_complement(a)));
	boolformula_set(dis, 1, boolformula_literal_new(x));
	boolformula_add(ret, dis);
	boolformula_free(dis);
}

/* Add clauses for x ≡ (a⊕b): (¬x∨¬a∨¬b)∧(¬x∨a∨b)∧(x∨¬a∨b)∧(x∨a∨¬b) */
static inline void add_xor_equiv_clauses(boolformula_t* ret, lit x, lit a, lit b){
	boolformula_t* dis;
	dis = boolformula_disjunction_new(3);
	boolformula_set(dis, 0, boolformula_literal_new(boolformula_lit_complement(x)));
	boolformula_set(dis, 1, boolformula_literal_new(boolformula_lit_complement(a)));
	boolformula_set(dis, 2, boolformula_literal_new(boolformula_lit_complement(b)));
	boolformula_add(ret, dis);
	boolformula_free(dis);
	dis = boolformula_disjunction_new(3);
	boolformula_set(dis, 0, boolformula_literal_new(boolformula_lit_complement(x)));
	boolformula_set(dis, 1, boolformula_literal_new(a));
	boolformula_set(dis, 2, boolformula_literal_new(b));
	boolformula_add(ret, dis);
	boolformula_free(dis);
	dis = boolformula_disjunction_new(3);
	boolformula_set(dis, 0, boolformula_literal_new(x));
	boolformula_set(dis, 1, boolformula_literal_new(boolformula_lit_complement(a)));
	boolformula_set(dis, 2, boolformula_literal_new(b));
	boolformula_add(ret, dis);
	boolformula_free(dis);
	dis = boolformula_disjunction_new(3);
	boolformula_set(dis, 0, boolformula_literal_new(x));
	boolformula_set(dis, 1, boolformula_literal_new(a));
	boolformula_set(dis, 2, boolformula_literal_new(boolformula_lit_complement(b)));
	boolformula_add(ret, dis);
	boolformula_free(dis);
}

static inline void add_clauses_to_boolformula(boolformula_t* ret, boolformula_t * f, lit* next_fresh){
	int i, n;
	lit output, cur, val_i;
	boolformula_t* cur_neg=boolformula_literal_new(boolformula_lit_complement(*next_fresh));
	boolformula_t* dis, *temp;
	switch(f->t){
	case conjunct:
		for(i=0;i<(int)vector_length (f->d.v);i++){
			dis=boolformula_disjunction_new(2);
			boolformula_add(ret, dis);
			boolformula_set(dis, 0,cur_neg);
			if(((boolformula_t*)vector_get(f->d.v,i))->t==literal){
				temp=boolformula_literal_new(((boolformula_t*)vector_get(f->d.v,i))->d.l);
				boolformula_set(dis, 1, temp);
				boolformula_free(temp);
			}else{
				(*next_fresh)++;
				temp=boolformula_literal_new(*next_fresh);
				boolformula_set(dis, 1, temp);
				boolformula_free(temp);
				add_clauses_to_boolformula(ret, (boolformula_t*)vector_get(f->d.v,i), next_fresh);
			}
			boolformula_free(dis);
		}
		break;
	case disjunct:
		dis=boolformula_disjunction_new(1+vector_length (f->d.v));
		boolformula_add(ret, dis);
		boolformula_set(dis, 0, cur_neg);
		for(i=0;i<(int)vector_length (f->d.v);i++){
			if(((boolformula_t*)vector_get(f->d.v,i))->t==literal){
				temp=boolformula_literal_new(((boolformula_t*)vector_get(f->d.v,i))->d.l);
				boolformula_set(dis,i+1, temp);
				boolformula_free(temp);
			}else{
				(*next_fresh)++;
				temp=boolformula_literal_new(*next_fresh);
				boolformula_set(dis, i+1,temp);
				boolformula_free(temp);
				add_clauses_to_boolformula(ret, (boolformula_t*)vector_get(f->d.v,i), next_fresh);
			}
		}
		boolformula_free(dis);
		break;
	case exclusive_disjunct: {
		n = (int)vector_length(f->d.v);
		if (n == 0) break;
		output = *next_fresh;
		if (((boolformula_t*)vector_get(f->d.v, 0))->t == literal)
			cur = ((boolformula_t*)vector_get(f->d.v, 0))->d.l;
		else {
			(*next_fresh)++;
			cur = *next_fresh - 1;
			add_clauses_to_boolformula(ret, (boolformula_t*)vector_get(f->d.v, 0), next_fresh);
		}
		if (n == 1) {
			add_lit_equiv_clauses(ret, output, cur);
			break;
		}
		for (i = 1; i < n; i++) {
			if (((boolformula_t*)vector_get(f->d.v, i))->t == literal)
				val_i = ((boolformula_t*)vector_get(f->d.v, i))->d.l;
			else {
				(*next_fresh)++;
				val_i = *next_fresh - 1;
				add_clauses_to_boolformula(ret, (boolformula_t*)vector_get(f->d.v, i), next_fresh);
			}
			if (i == n - 1)
				add_xor_equiv_clauses(ret, output, cur, val_i);
			else {
				add_xor_equiv_clauses(ret, *next_fresh, cur, val_i);
				cur = (*next_fresh)++;
			}
		}
		break;
	}
	case literal:
		printf("Something wrong\n");
		exit(13);
		break;
	}
	boolformula_free(cur_neg);
}

static inline boolformula_t *boolformula_to_cnf (boolformula_t * f, scalar_t num_var){
	scalar_t next_fresh=num_var+1;
	boolformula_t* ret=NULL;
	boolformula_t* cur;

	switch(f->t){
	case literal:
		ret=boolformula_copy(f);
		break;
	case conjunct:
	case disjunct:
	case exclusive_disjunct:
		ret=boolformula_conjunction_unit();
		cur=boolformula_literal_new(next_fresh);
		boolformula_add(ret, cur);
		add_clauses_to_boolformula(ret, f, &next_fresh);
		boolformula_free(cur);
		break;
	}
	return ret;
}

static inline enum type boolformula_get_type (boolformula_t * f){
	assert (f->t == literal || f->t == conjunct || f->t == disjunct || f->t == exclusive_disjunct);
	return f->t;
}

static inline uscalar_t boolformula_get_length (boolformula_t * f){
	assert(f->t == conjunct || f->t == disjunct || f->t == exclusive_disjunct);
	return vector_length (f->d.v);
}

static inline boolformula_t *boolformula_get_subformula (boolformula_t * f, uscalar_t idx){
	assert(f->t == conjunct || f->t == disjunct || f->t == exclusive_disjunct);
	return (boolformula_t*)vector_get(f->d.v, idx);
}

static inline lit boolformula_get_value (boolformula_t * f){
	assert(f->t==literal);
	return f->d.l;
}

void boolformula_print (boolformula_t *f);
scalar_t boolformula_num_of_var(boolformula_t* f);

#endif
