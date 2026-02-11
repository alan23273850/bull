/*****************************************************************************
 *
 *
 * Author: Bow-Yaw Wang
 * Copyright reserved
 *****************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "type.h"
#include "bitvector.h"
#include "vector.h"
#include "boolformula.h"
#include "cdnfformula.h"

static void cdnfformula_monomial_to_string (monomial *m)
{
  if (vector_length (m) == 0) {
    fprintf (stderr, "( T )");
  } else {
    uscalar_t i;
    fprintf (stderr, "( ");
    for (i = vector_length (m) - 1; i > 0; i--) {
      fprintf (stderr, "%ld & ", (long)(lit) vector_get (m, i));
    }
    assert (i == 0);
    fprintf (stderr, "%ld ", (long)(lit) vector_get (m, i));
    fprintf (stderr, " )");
  }
}

static void cdnfformula_disjunction_to_string (disjunction *f)
{
  if (vector_length (f) == 0) {
    fprintf (stderr, "[ F ]");
  } else {
    uscalar_t i;
    fprintf (stderr, "[ ");
    for (i = vector_length (f) - 1; i > 0; i--) {
      cdnfformula_monomial_to_string ((monomial*)vector_get (f, i));
      fprintf (stderr, " | ");
    }
    assert (i == 0);
    cdnfformula_monomial_to_string ((monomial*)vector_get (f, i));
    fprintf (stderr, " ]");
  }
}

void cdnfformula_print (conjunction *f)
{
  if (vector_length (f) == 0) {
    fprintf (stderr, "{ T }");
  } else {
    uscalar_t i;
    fprintf (stderr, "{ ");
    for (i = vector_length (f) - 1; i > 0; i--) {
      cdnfformula_disjunction_to_string ((disjunction*)vector_get (f, i));
      fprintf (stderr, " & ");
    }
    assert (i == 0);
    cdnfformula_disjunction_to_string ((disjunction*)vector_get (f, i));
    fprintf (stderr, " }\n");
  }
}

static bool cdnfformula_eval_monomial (monomial *m, bitvector *bv)
{
  uscalar_t i, length;
  length = vector_length (m);
  for (i = 0; i < length; i++) {
    lit l;
    var v;
    l = (lit) vector_get (m, i);
    v = boolformula_var_from_lit (l);
    assert (0 < v);
    assert (v < bitvector_length (bv));
    if (boolformula_positive_lit (l) != bitvector_get (bv, v))
      return false;
  }
  return true;
}

bool cdnfformula_eval_M_DNF (disjunction *m_dnf, bitvector *bv)
{
  uscalar_t i, length;
  length = vector_length (m_dnf);
  for (i = 0; i < length; i++) {
    monomial *m = (monomial*)vector_get (m_dnf, i);
    if (cdnfformula_eval_monomial (m, bv))
      return true;
  }
  return false;
}
