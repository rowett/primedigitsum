# Makefile for building ds
# requires a x64 CPU that supports the POPCNT instruction

# uncomment the next line if you want search metrics to be output, small performance penalty if enabled
#EXTRAFLAGS=-DMETRICS

# use the optimizer, extra warnings, and build for the architecture of the build machine
CFLAGS=-Ofast -Wextra -march=native $(EXTRAFLAGS)

# need the math library
LIBS=-lm

# use gcc as the C-compiler, change if you want a different compiler
CC=gcc


# ds executable
ds: ds.c
	$(CC) $(CFLAGS) -o $@ $< $(LIBS)

clean:
	rm -f ds
