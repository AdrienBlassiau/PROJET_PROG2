#include "include.h"
#include "merge.h"


int* merge(int* a, int* sorted_list, size_t* cutpoints, const size_t cutlength){
	int first = 0;
	int second = 1;
	int third = 2;
	int last = cutlength-1;
	int i = 0;
	int j, length_s, length_t;

	int x,y,cut_first,cut_second,cut_third;

	while (second < last){

		x = 0;
		y = 0;
		i = 0;
		cut_first = cutpoints[first];
		cut_second = cutpoints[second];
		cut_third = cutpoints[third];

		length_s = cut_second - cut_first;
		length_t = cut_third - cut_second;

		while (x < length_s && y < length_t){
			if (a[x] < a[y+cut_second]){
				sorted_list[i] = a[x];
				x+=1;
				i+=1;
			}
			else{
				sorted_list[i] = a[y+cut_second];
				y+=1;
				i+=1;
			}
		}

		while (x < cut_second - cut_first){
			sorted_list[i] = a[x];
			x+=1;
			i+=1;
		}

		while (y < cut_third - cut_second){
			sorted_list[i] = a[y+cut_second];
			y+=1;
			i+=1;
		}

		for (j = 0; j < cut_third; j++)
		{
			a[j] = sorted_list[j];
		}

		second++;
		third++;
	}

	return a;
}