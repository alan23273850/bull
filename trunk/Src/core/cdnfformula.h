/*****************************************************************************
 *
 * 
 * Author: Bow-Yaw Wang
 * Copyright reserved
 *****************************************************************************/

#ifndef _CDNFFORMULA_H_
#define _CDNFFORMULA_H_

typedef vector conjunction, disjunction, monomial;

monomial *cdnfformula_monomial_M_DNF (bitvector *bv);
disjunction *cdnfformula_disjunction_new (uscalar_t length);
disjunction *cdnfformula_disjunction_unit (void);
disjunction *cdnfformula_disjunction_add (disjunction *, monomial *);
void cdnfformula_disjunction_free (disjunction *);
conjunction *cdnfformula_conjunction_new (uscalar_t length);
conjunction *cdnfformula_conjunction_unit (void);
conjunction *cdnfformula_conjunction_add (conjunction *, disjunction *);
void cdnfformula_free (conjunction *);
void cdnfformula_print (conjunction *f);
boolformula_t *cdnfformula_to_boolformula (conjunction *);
bool cdnfformula_eval_M_DNF (disjunction *m_dnf, bitvector *bv);
#endif
