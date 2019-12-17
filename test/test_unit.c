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

#include "CUnit/CUnit.h"
#include "CUnit/Basic.h"

#include "test_unit.h"
#include "../src/include.h"
#include "../src/sort.h"


#define CAPACITY 100
#define N 100

int setup(void)  { return 0; }
int teardown(void) { return 0; }

int init_test(void){

	if (CUE_SUCCESS != CU_initialize_registry())
		return CU_get_error();

	CU_pSuite pSuite = CU_add_suite("echantillon_test",setup,teardown);

	if(( NULL == CU_add_test(pSuite, "Test sort", test_sort)))
	{
		CU_cleanup_registry();
		return CU_get_error();
	}

	CU_basic_run_tests();
	CU_basic_show_failures(CU_get_failure_list());
	CU_cleanup_registry();

	return 0;
}


void test_sort(void)
{
  int i,j,n;
  int tab[CAPACITY] = {[0 ... CAPACITY-1] = 0};
  int sorted_tab[CAPACITY] = {[0 ... CAPACITY-1] = 0};
  size_t cutpoints[CAPACITY];
  size_t cutlength;


  int test_bool;
  srand(time(NULL));

  for (j = 0; j < 100000; j++)
  {
    test_bool = 0;

    for (i = 0, n = N; i < N; i++){
      tab[i] = rand()%20;
    }

    cutlength = monotonic(tab,n,cutpoints);
    reverse(tab,n,cutpoints,cutlength);
    merge(tab,n,sorted_tab,cutpoints,cutlength);

    for (i = 0; i < N-1; i++){
      if (tab[i]>tab[i+1])
      {
        test_bool = 1;
      }
    }

    CU_ASSERT_EQUAL(test_bool,0);
  }
}
