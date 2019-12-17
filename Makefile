#----------------------------------------------------------------------
# Copyright (c) 2019-2020, Adrien BLASSIAU and Corentin JUVIGNY

# Permission to use, copy, modify, and/or distribute this software
# for any purpose with or without fee is hereby granted, provided
# that the above copyright notice and this permission notice appear
# in all copies.

# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL
# WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE
# AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR
# CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT,
# NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
# CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#----------------------------------------------------------------------


CC=gcc -Wall -Wextra -std=c11 -O2 -lm

all : main

main : main.o monotonic_cutpoints.o monotonic_reverse.o tools.o merge.o
	cd obj/ && $(CC) $^ -o ../bin/$@


test : main_test.o monotonic_cutpoints.o monotonic_reverse.o tools.o merge.o test_unit.o
	cd obj/ && $(CC) $^ -o ../bin/$@ -lcunit

main.o : src/main.c src/sort.h
	$(CC) -c $< -o obj/$@

monotonic_cutpoints.o : src/monotonic_cutpoints.c
	$(CC) -c $< -o obj/$@

monotonic_reverse.o : src/monotonic_reverse.c
	$(CC) -c $< -o obj/$@

merge.o : src/merge.c
	$(CC) -c $< -o obj/$@

tools.o : src/tools.c
	$(CC) -c $< -o obj/$@

main_test.o : test/main_test.c src/sort.h
	$(CC) -c $< -o obj/$@

test_unit.o : test/test_unit.c src/include.h
	$(CC) -c $< -o obj/$@

doxygen : doc/Doxyfile
	cd doc && doxygen ../$<

.PHONY: clean
clean :
	rm -f obj/*
	rm -rf doc/html/*
	rm -rf doc/latex/*
	rm -rf bin/*
