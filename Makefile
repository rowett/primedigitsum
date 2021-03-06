# Makefile for num

# flags and folders
#EXTRAFLAGS=-DMETRICS
CFLAGS=-Ofast -Wextra -march=native $(EXTRAFLAGS)
#CFLAGS=-g -Wextra -march=native $(EXTRAFLAGS)
LIBS=-lm
CC=gcc

# primegen executable which generates prime data file
ds: ds.c
	$(CC) $(CFLAGS) -o $@ $< $(LIBS)
