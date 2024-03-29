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

/** @file merge.h
 *
 * @brief Sort a list composed of increasing sublists
 */


#ifndef MERGE_H
#define MERGE_H

#include "include.h"


/**
 * This function sort a list with a particular method
 * @param  a           The list we want to sort
 * @param  length      The length of the list a
 * @param  sorted_list The list where we do the sorting
 * @param  cutpoints   The list of cutpoints
 * @param  cutlength   The length of list cutpoints
 * @return             The sorted list
 */
int* merge(int* a, const size_t length, int* sorted_list, size_t* cutpoints, const size_t cutlength);


#endif
