#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "monotonic_cutpoints.h"

#define CAPACITY 100
#define N 10

int main(int argc,char* argv[])
{
  int i,n;
  int tab[CAPACITY] = {[0 ... CAPACITY-1] = 0};
  size_t cutpoints[CAPACITY];

  if ((argc = argc > N ? N : argc-1) < 3) {
    srand(time(NULL));
    for (i = 0, n = N; i < N; i++)
      tab[i] = rand();
  } else {
    for (i = 0, argv=argv+1, n = argc; i < argc; i++)
      tab[i] = strtol(argv[i],NULL,0);
  }
 
  //Include your code here
  
  printf("%ld\n",monotonic(tab,n,cutpoints));
  
  return 0;
}
