/*

Copyright (c) 2005-2008, Simon Howard

Permission to use, copy, modify, and/or distribute this software
for any purpose with or without fee is hereby granted, provided
that the above copyright notice and this permission notice appear
in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL
WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE
AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR
CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT,
NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

*/

/** @file monotonic_cutpoints.h
 *
 * @brief Given  a  sequences stored  in  an  array, we compute the
 * maximal  monotonic cutpoints by scannings the array and storing every
 * index that corresponds to a change in monotonicity (from increasing to
 *  decreasing, or viceversa).
 */


#ifndef MONOTONIC_CUTPOINTS_H
#define MONOTONIC_CUTPOINTS_H

typedef struct _MonotonicSolution MonotonicSolution;

/**
 * \struct _MonotonicSolution
 * \brief A sequence of the indexes of cutpoints and the size of this sequence
 *
 */
struct _MonotonicSolution {
  int*		monotonix_indexes;
  int 		size;
};


int* get_monotonic_sequence(long int* array_to_sort);


#endif