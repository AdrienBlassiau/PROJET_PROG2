#include <stdio.h>
#include <stdlib.h>

#define N 100

int main(int argc,char* argv[])
{
  unsigned int i;
  long tab[N] = {[0 ... 99] = 0};
  
  if ((argc = argc > N ? N : argc-1) < 2)
    return 0;

  for (i = 0, argv=argv+1; i < argc; tab[i++] = strtol(argv[i],NULL,0));

  //Include your code here

  return 0;
}
