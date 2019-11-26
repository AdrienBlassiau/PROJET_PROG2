#include "include.h"
#include "merge.h"

// merged := []
// x, y := 0, 0
// while x < length(s) and y < length(t):
// 	if s[x] < t[y]:
// 		merged.extend(s[x])
// 		x := x + 1
// 	else:
// 		merged.extend(t[y])
// 		y := y + 1
// # append any remaining tail of s or t
// while x < length(s):
// 	merged.extend(s[x])
// 	x := x + 1
// while y < length(t):
// 	merged.extend(t[y])
// 	y := y + 1

int* merge(int* a, int* sorted_list, size_t* cutpoints, const size_t cutlength){
	int first = 0;
	int second = 1;
	int third = 2;
	int last = cutlength-1;
	int i = 0;

	int x,y,cut_first,cut_second,cut_third;

	while (second < last){

		x = 0;
		y = 0;
		cut_first = cutpoints[first];
		cut_second = cutpoints[second];
		cut_third = cutpoints[third];

		printf("first: %d/second: %d/third: %d\n",cut_first,cut_second,cut_third);

		while (x < cut_second - cut_first && y < cut_third - cut_second){
			if (cutpoints[x] < cutpoints[y+second]){
				sorted_list[i] = a[x];
				x+=1;
				i+=1;
			}
			else{
				sorted_list[i] = a[y+second];
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
			sorted_list[i] = a[y+second];
			y+=1;
			i+=1;
		}

		second++;
		third++;
	}

	return sorted_list;
}