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

#include "include.h"

/*@ predicate increasing_slice(int* a, size_t low, size_t up) =
  (\forall integer i,j; low <= i < j < up ==> a[i] <= a[j]);
*/

/*@ predicate decreasing_slice(int* a, size_t low, size_t up) =
  (\forall integer i,j; low <= i <= j < up ==> a[i] >= a[j]);
*/

/*@ predicate monotone_slice(int* a, size_t low, size_t up) =
  (\forall integer i,j; low <= i < j < up ==> a[i] < a[j]) ||
  (\forall integer i,j; low <= i <= j < up ==> a[i] >= a[j]);
*/


/*@
  requires length < 100;
  requires 0<=bg<=end<length;
  requires a_valid: \valid(a + (0 .. length - 1));
  requires decreasing_slice: decreasing_slice(a,bg,end);
  assigns a[bg .. end];
  ensures increasing: \forall integer k; bg <= k <= end  ==> a[k] ==\old(a[bg+end−k]);
*/
static void reverse_monome(int* a, size_t bg, size_t end, const size_t length)
{
  size_t i,j;
  int r;
  /*@
    loop invariant i_bound: bg <= i <= end;
    loop invariant j_bound: bg <= j <= end;
    loop invariant inner_bound: i <= j+1;

    loop invariant i_plus_j: i+j == bg+end;
    loop invariant pre_1: \forall integer k; bg <= k < i  ==> a[k] == \at(a[end+bg−k] ,Pre);
    loop invariant pre_2: \forall integer k; j < k <= end  ==> a[k] == \at(a[end+bg−k] ,Pre);
    loop invariant middle_valid : \forall integer k; i<=k<=j ==> a[k] == \at(a[k] ,Pre);

    loop assigns i;
    loop assigns j;
    loop assigns r;
    loop assigns a[bg .. end];
    loop variant j-i;
  */

  for (i = bg, j = end; i < j; i++, j--) {
    r = a[i];
    a[i] = a[j];
    a[j] = r;
  }
}

/*@
  requires length < 100;
  requires cutlength > 0;
  requires a_valid: \valid(a + (0 .. length - 1));
  requires res_valid: \valid(cutpoints + (0 .. cutlength-1));
  requires sep: \separated(a + (0 .. length - 1), cutpoints + (0 .. length));
  requires bounds:
    \forall integer i; 0 <= i < cutlength ==> 0 <= cutpoints[i] < length;
  requires beg: cutpoints[0] == 0;
  requires end: cutpoints[cutlength-1] == length;
  requires monotonic:
      \forall integer i; 0 <= i < cutlength-1 ==>
      monotone_slice(a,cutpoints[i],cutpoints[i+1]);
  assigns a[0 .. length-1];
  ensures increasing:
    \forall integer i; 0 <= i < cutlength-1 ==>
    increasing_slice(a,cutpoints[i],cutpoints[i+1]);
*/
int* reverse(int* a, const size_t length, const size_t* cutpoints, const size_t cutlength)
{
  size_t i;

  /*@
    loop invariant inner_bound: 0 <= i < cutlength;
    loop assigns i;
    loop assigns a[0 .. length-1];
    loop variant cutlength-1-i;
  */
  for (i = 0; i < cutlength-1; i++){
    if (a[cutpoints[i]] >= a[cutpoints[i+1]-1]){
      reverse_monome(a,cutpoints[i],cutpoints[i+1]-1,length);
    }
  }
  return a;
}