#include "include.h"
#include "merge.h"


/*@ predicate increasing_slice(int* a, size_t low, size_t up) =
  (\forall integer i,j; low <= i < j < up ==> a[i] <= a[j]);
*/

/*@
	requires length < 100;

    requires a_valid: \valid(a + (0 .. length - 1));
    requires sorted_valid: \valid(sorted_list + (0 .. length - 1));
    requires res_valid: \valid(cutpoints + (0 .. cutlength-1));

	requires cutlength <= length + 1;

    requires sep: \separated(a + (0 .. length - 1),sorted_list + (0 .. length - 1), cutpoints + (0 .. cutlength-1));

    requires increasing:
    \forall integer i; 0 <= i < cutlength-1 ==>
    increasing_slice(a,cutpoints[i],cutpoints[i+1]);

    requires beg: cutpoints[0] == 0;
  	requires end: cutpoints[cutlength-1] == length;

  	requires \forall integer i; 0 <= i <= cutlength-1 ==> cutpoints[i] <= length;

  	requires \forall integer i,j; 0 <= i < j <= cutlength-1 ==> cutpoints[j] - cutpoints[i] <= length;

    assigns sorted_list[0 .. length-1];
	assigns a[0 .. length-1];

	ensures sorted_result: \forall integer i; 0 <= i < length-1 ==> a[i] <= a[i+1];

*/
int* merge(int* a, const size_t length, int* sorted_list, size_t* cutpoints, const size_t cutlength){
	int second = 1;
	int third = 2;
	int last = cutlength-1;
	int i = 0;
	int j, length_s, length_t;

	int x,y,cut_second,cut_third;

	/*@
	    loop assigns x;
	    loop assigns y;
	    loop assigns i;

	    loop assigns cut_second;
	    loop assigns cut_third;

	    loop assigns length_s;
	    loop assigns length_t;

	    loop assigns sorted_list[0 .. length - 1];
		loop assigns a[0 .. length - 1];

	    loop variant last-second;
	*/
	while (second < last){ /*Tant qu'il y a deux sous tableaux à fusionner*/
		x = 0; /*Pointe sur la xème case du premier sous tableau trié de a*/
		y = 0; /*Pointe sur la yème case du deuxième sous tableau trié de a*/
		i = 0; /*Pointe sur la ième case de sorted_list dans lequel on copie progressivement la fusion des deux premiers sous tableau non trié*/

		cut_second = cutpoints[second]; /*Premier indice du deuxième sous tableau trié*/
		cut_third = cutpoints[third]; /*Premier indice du troisième sous tableau */

		length_s = cut_second; /*Longueur du premier sous-tableau trié*/
		length_t = cut_third - cut_second; /*Longueur du deuxième sous-tableau trié*/


		/*@
		    loop assigns x;
		    loop assigns y;
		    loop assigns i;
		    loop assigns sorted_list[0 .. length_t+length_s];

		    loop invariant 0 <= i <= length_t+length_s-1;
			loop invariant 0 <= x <= length_s;
			loop invariant 0 <= y <= length_t;

		    loop variant length_s+length_t-(x+y);
		*/
		while (x < length_s && y < length_t){
			/* Tant qu'on peut toujours itérer sur les deux sous-tableaux */
			if (a[x] < a[y+cut_second]){
				sorted_list[i] = a[x];
				x+=1;
			}
			else{
				sorted_list[i] = a[y+cut_second];
				y+=1;
			}
			i+=1;
		}

		/*@
		    loop assigns x;
		    loop assigns i;
		    loop assigns sorted_list[0 .. length_t+length_s];

		    loop invariant 0 <= x < length_s;
		    loop variant length_s-x;
		*/
		while (x < length_s){
			/* Tant qu'on peut toujours itérer sur le premier sous tableau */
			sorted_list[i] = a[x];
			x+=1;
			i+=1;
		}

		/*@
		    loop assigns y;
		    loop assigns i;
		    loop assigns sorted_list[0 .. length_t+length_s];

		    loop invariant 0 <= y < length_t;
		    loop variant length_t-y;
		*/
		while (y < length_t){
			/* Tant qu'on peut toujours itérer sur le deuxième sous tableau */
			sorted_list[i] = a[y+cut_second];
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

		second++;/* On décale les sous tableaux*/
		third++;
	}

	return a;
}