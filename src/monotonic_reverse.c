#include "include.h"

static void reverse_monome(int* a, size_t bg, size_t end)
{
  size_t i,j;
  int r;
  for (i = bg, j = end; i < j; i++, j--) {
    r = a[i];
    a[i] = a[j];
    a[j] = r;
  }
}

int* reverse(int* a, const size_t* cutpoints, const size_t cutlength)
{
  size_t i;

  for (i = 0; i < cutlength-1; i++)
    if (a[cutpoints[i]] > a[cutpoints[i]+1])
      reverse_monome(a,cutpoints[i],cutpoints[i+1]-1);

  return a;
}
