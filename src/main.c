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
#include "sort.h"

#define CAPACITY 100
#define N 10

int main(int argc,char* argv[])
{
  int i,n;
  int tab[CAPACITY] = {[0 ... CAPACITY-1] = 0};
  int sorted_tab[CAPACITY] = {[0 ... CAPACITY-1] = 0};
  size_t cutpoints[CAPACITY];
  size_t cutlength;

  if ((argc = argc > N ? N : argc-1) < 3) {
    srand(time(NULL));
    for (i = 0, n = N; i < N; i++)
      tab[i] = rand()%20;
  } else {
    for (i = 0, argv=argv+1, n = argc; i < argc; i++)
      tab[i] = strtol(argv[i],NULL,0);
  }

  //Include your code here

  cutlength = monotonic(tab,n,cutpoints);

  for (i = 0; i < n; i++) printf("%d ",tab[i]);
  printf("\n");

  reverse(tab,n,cutpoints,cutlength);

  for (i = 0; i < n; i++) printf("%d ",tab[i]);
  printf("\n");

  merge(tab,n,sorted_tab,cutpoints,cutlength);

  for (i = 0; i < n; i++) printf("%d ",tab[i]);
  printf("\n");

  return 0;
}
