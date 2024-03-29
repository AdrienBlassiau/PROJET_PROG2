/*

Copyright (c) 2019-2020, Virgile PREVOSTO

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
 * decreasing, or viceversa).
 */


#ifndef MONOTONIC_CUTPOINTS_H
#define MONOTONIC_CUTPOINTS_H

#include "include.h"


/**
 * This function compute the monotonic cupoints of an int array
 * @param  a         An int array
 * @param  length    The length of the int array
 * @param  cutpoints The array of the cutpoints
 * @return           The size of the array of the cutpoints
 */
size_t monotonic(int* a, size_t length, size_t* cutpoints);


#endif
