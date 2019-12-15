/*

Copyright (c) 2019-2020, Adrien BLASSIAU and Corentin JUVIGNY

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

/** @file monotonic_reverse.h
 *
 * @brief Given  a  list with monotonic sub-list, we computes the same list with all sub-list increasing.
 */

#ifndef __MONOTONIC_REVERSE__
#define __MONOTONIC_REVERSE__

/**
 * This function reverses all decreasing segments
 * @param  a         The list we want to modify.
 * @param  length    The length of the list we want to modify.
 * @param  cutpoints The list of cutpoints of a.
 * @param  cutlength The length od the cutpoints list.
 * @return           The list with increasing segments.
 */
int* reverse(int* a, const size_t length, const size_t* cutpoints, const size_t cutlength);

#endif
