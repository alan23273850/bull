/*****************************************************************************
 *
 * 
 * Author: Bow-Yaw Wang
 * Copyright reserved
 *****************************************************************************/

#ifndef __BITVECTOR_H_
#define __BITVECTOR_H_

#include <assert.h>
#ifndef __cplusplus
#include <stdbool.h>
#endif

typedef struct {
  uscalar_t length; /* length of bit vector */
  uscalar_t size;   /* size of buffer */
  uscalar_t *buffer;         /* buffer */
} bitvector;

/* For inline accessors */
#define BITVECTOR_BITS_IN_INT    (8u * (unsigned)sizeof (unsigned int))
#define bitvector_array_idx(idx) ((idx) / BITVECTOR_BITS_IN_INT)
#define bitvector_bit_pos(idx)   (1u << ((idx) % BITVECTOR_BITS_IN_INT))

bitvector *bitvector_new (uscalar_t size);
void bitvector_free (bitvector *bv);

static inline uscalar_t bitvector_length (bitvector *bv)
{
  return bv->length;
}

static inline void bitvector_set (bitvector *bv, uscalar_t idx, bool b)
{
  assert (bv != NULL);
  assert (idx < bv->length);
  if (b)
    bv->buffer[bitvector_array_idx(idx)] |= bitvector_bit_pos(idx);
  else
    bv->buffer[bitvector_array_idx(idx)] &= ~bitvector_bit_pos(idx);
}

static inline bool bitvector_get (bitvector *bv, uscalar_t idx)
{
  assert (bv != NULL);
  assert (idx < bv->length);
  return (bv->buffer[bitvector_array_idx(idx)] & bitvector_bit_pos(idx)) != 0;
}

void bitvector_resize (bitvector *bv, uscalar_t new_size);
bitvector *bitvector_xor (bitvector *bv0, bitvector *bv1);
bitvector *bitvector_copy (bitvector *bv);
bool bitvector_is_zeros (bitvector *bv);
void bitvector_print (bitvector *bv);

#endif
