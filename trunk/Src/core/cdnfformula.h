/*****************************************************************************
 *
 *
 * Author: Bow-Yaw Wang
 * Copyright reserved
 *****************************************************************************/

#ifndef _CDNFFORMULA_H_
#define _CDNFFORMULA_H_

#include "type.h"
#include "vector.h"
#include "bitvector.h"
#include "boolformula.h"
#include <assert.h>
#include <stdlib.h>

typedef vector conjunction, disjunction, monomial;

static inline monomial *cdnfformula_monomial_unit (void)
{
  return vector_new (0);
}

static inline monomial *cdnfformula_monomial_add (monomial *m, lit l)
{
  assert (l != 0);
  vector_add (m, (pointer_t)l);
  return m;
}

static inline monomial *cdnfformula_monomial_M_DNF (bitvector *bv)
{
  uscalar_t i;
  monomial *result;
  result = cdnfformula_monomial_unit ();
  for (i = bitvector_length (bv) - 1; i > 0; i--) {
    if (bitvector_get (bv, i))
      result = cdnfformula_monomial_add (result, (lit)i);
  }
  assert (vector_length (result) > 0);
  return result;
}

static inline disjunction *cdnfformula_disjunction_unit (void)
{
  return vector_new (0);
}

static inline disjunction *cdnfformula_disjunction_new (uscalar_t length)
{
  return vector_new (length);
}

static inline disjunction *cdnfformula_disjunction_add (disjunction *f, monomial *disj)
{
  vector_add (f, (pointer_t)disj);
  return f;
}

static inline void cdnfformula_disjunction_free (disjunction *disj)
{
  uscalar_t i, num_disjs;
  num_disjs = vector_length (disj);
  for (i = 0; i < num_disjs; i++) {
    monomial *mono = (monomial *) vector_get (disj, i);
    vector_free (mono);
  }
  vector_free (disj);
}

static inline conjunction *cdnfformula_conjunction_unit (void)
{
  return vector_new (0);
}

static inline conjunction *cdnfformula_conjunction_new (uscalar_t length)
{
  return vector_new (length);
}

static inline conjunction *cdnfformula_conjunction_add (conjunction *f, disjunction *conj)
{
  vector_add (f, (pointer_t)conj);
  return f;
}

static inline void cdnfformula_free (conjunction *f)
{
  uscalar_t i, num_conjs;
  num_conjs = vector_length (f);
  for (i = 0; i < num_conjs; i++) {
    disjunction *disj = (disjunction *) vector_get (f, i);
    cdnfformula_disjunction_free (disj);
  }
  vector_free (f);
}

static inline boolformula_t* monomial_to_boolformula (monomial *m)
{
  boolformula_t* ret = boolformula_conjunction_new(vector_length(m)), *temp;
  uscalar_t i;
  for (i = 0; i < vector_length (m); i++) {
    temp = boolformula_literal_new((lit)vector_get(m,i));
    boolformula_set(ret, i, temp);
    boolformula_free(temp);
  }
  return ret;
}

static inline boolformula_t* dnf_to_boolformula (disjunction *f)
{
  boolformula_t* ret = boolformula_disjunction_new(vector_length(f)), *temp;
  uscalar_t i;
  for (i = 0; i < vector_length (f); i++) {
    temp = monomial_to_boolformula((monomial*)vector_get(f,i));
    boolformula_set(ret, i, temp);
    boolformula_free(temp);
  }
  return ret;
}

static inline boolformula_t *cdnfformula_to_boolformula (conjunction * f){
  boolformula_t* ret = boolformula_conjunction_new(vector_length(f)), *temp;
  uscalar_t i;
  for (i = 0; i < vector_length (f); i++) {
    temp = dnf_to_boolformula((disjunction*)vector_get(f,i));
    boolformula_set(ret, i, temp);
    boolformula_free(temp);
  }
  return ret;
}

void cdnfformula_print (conjunction *f);
bool cdnfformula_eval_M_DNF (disjunction *m_dnf, bitvector *bv);

#endif
