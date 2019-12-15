#include "include.h"
#include "merge.h"


/*@ predicate increasing_slice(int* a, size_t low, size_t up) =
  (\forall integer i,j; low <= i < j < up ==> a[i] <= a[j]);
*/

/*@
    requires 1 <= length < 100;
    requires 2 <= cutlength <= length + 1;

    requires a_valid: \valid(a + (0 .. length - 1));
    requires sorted_valid: \valid(sorted_list + (0 .. length - 1));
    requires res_valid: \valid(cutpoints + (0 .. cutlength-1));

    requires sep: \separated(a + (0 .. length - 1),sorted_list + (0 .. length - 1), cutpoints + (0 .. cutlength-1));

    requires increasing:
    \forall integer i; 0 <= i < cutlength-1 ==>
    increasing_slice(a,cutpoints[i],cutpoints[i+1]);

    requires beg: cutpoints[0] == 0;
    requires end: cutpoints[cutlength-1] == length;

    requires \forall integer i; 0 <= i < cutlength-1 ==> 0 <= cutpoints[i] < length;

    requires \forall integer i,j; 0 <= i < j < cutlength-1 ==> 0 <= cutpoints[j] - cutpoints[i] < length;
    
    requires \forall integer i; 0 <= i < cutlength-1 ==> cutpoints[i] < cutpoints[i+1];

    assigns sorted_list[0 .. length-1];
    assigns a[0 .. length-1];
    
    // ensures sorted_result: \forall integer i; 0 <= i < length-1 ==> a[i] <= a[i+1];

*/
int* merge(int* a, const size_t length, int* sorted_list, size_t* cutpoints, const size_t cutlength)
{
  size_t current_ind = 1;
  size_t i = 0;
  size_t j = 0;
  size_t length_s = 0;
  size_t length_t = 0;
  size_t x = 0;
  size_t y = 0;

  /*@
    loop assigns x;
    loop assigns y;
    loop assigns i;
    loop assigns j;

    loop assigns current_ind;

    loop assigns length_s;
    loop assigns length_t;

    loop assigns sorted_list[0 .. length - 1];
    loop assigns a[0 .. length - 1];

    //loop invariant current_ind < cutlength-1 ==> cutpoints[current_ind+1] >= cutpoints[current_ind];
    loop invariant current_ind <= cutlength-1;

    loop variant cutlength-current_ind-1;
  */
  while (current_ind < cutlength-1){ /*Tant qu'il y a deux sous tableaux à fusionner*/
    x = 0; /*Pointe sur la xème case du premier sous tableau trié de a*/
    y = 0; /*Pointe sur la yème case du deuxième sous tableau trié de a*/
    i = 0; /*Pointe sur la ième case de sorted_list dans lequel on copie
    progressivement la fusion des deux premiers sous tableau non trié*/

    length_s = cutpoints[current_ind]; /*Longueur du premier sous-tableau trié*/
    length_t = cutpoints[current_ind+1] - length_s; /*Longueur du deuxième sous-tableau trié*/


    /*@
      loop assigns x;
      loop assigns y;
      loop assigns i;
      loop assigns sorted_list[0 .. length - 1];

      loop invariant 0 <= length_s <= length;
      loop invariant 0 <= length_t <= length;

      loop invariant 0 <= length_t + length_s <= length;

      loop invariant 0 <= i <= length;
      loop invariant 0 <= x <= length_s;
      loop invariant 0 <= y <= length_t;

      loop variant length_s+length_t+length-(x+y+i);
    */
    while (x < length_s && y < length_t && i < length){
      /* Tant qu'on peut toujours itérer sur les deux sous-tableaux */
      if (a[x] < a[y+length_s]){
        sorted_list[i] = a[x];
        x+=1;
      }
      else{
        sorted_list[i] = a[y+length_s];
        y+=1;
      }
      i+=1;
    }

    /*@
        loop assigns x;
        loop assigns i;
        loop assigns sorted_list[0 .. length - 1];

      loop invariant 0 <= length_t <= length;
      loop invariant 0 <= length_s <= length;

        loop invariant 0 <= x <= length_s;
        loop invariant 0 <= i <= length;
        loop variant length_s+length-(x+i);
    */
    while (x < length_s && i < length){
      /* Tant qu'on peut toujours itérer sur le premier sous tableau */
      sorted_list[i] = a[x];
      x+=1;
      i+=1;
    }

    /*@
        loop assigns y;
        loop assigns i;
        loop assigns sorted_list[0 .. length - 1];

      loop invariant 0 <= length_t <= length;
      loop invariant 0 <= length_s <= length;

        loop invariant 0 <= y <= length_t;
        loop invariant 0 <= i <= length;
        loop variant length_t+length-(y+i);
    */
    while (y < length_t && i < length){
      /* Tant qu'on peut toujours itérer sur le deuxième sous tableau */
      sorted_list[i] = a[y+cutpoints[current_ind]];
      y+=1;
      i+=1;
    }


    /*@
        loop invariant inner_bound: 0 <= j <= length_t+length_s;
        loop assigns j;
        loop assigns a[0 .. length_t+length_s-1];
        loop variant length_t+length_s-j;
      */
    for (j = 0; j < length_t+length_s; j++){
      /* Tant qu'on recopie la fusion des deux premiers sous tableaux dans a */
      a[j] = sorted_list[j];
    }

    current_ind++;/* On décale les sous tableaux*/
    /*@ assert current_ind <= cutlength - 1 ;*/
  }

  return a;
}
