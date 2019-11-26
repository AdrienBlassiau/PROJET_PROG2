#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "monotonic_cutpoints.h"
#include "monotonic_reverse.h"
#include "merge.h"

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

  reverse(tab,cutpoints,cutlength);

  for (i = 0; i < n; i++) printf("%d ",tab[i]);
  printf("\n");

  merge(tab,sorted_tab,cutpoints,cutlength);

  for (i = 0; i < n; i++) printf("%d ",sorted_tab[i]);
  printf("\n");

  return 0;
}
