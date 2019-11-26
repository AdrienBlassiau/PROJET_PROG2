#include <stdio.h>
#include <stdlib.h>

int size_of_array(long* array){
	return sizeof(array)/sizeof(array[0]);
}

int* get_monotonic_sequence(long int* array_to_sort){

	printf("%d\n",size_of_array(array_to_sort));
	return NULL;
}