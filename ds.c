// Let ds(n) be the smallest prime number where the digit sums of it written in bases 2 to n+1 are all prime.
// this program finds ds(n)
// Usage: ds start end minbase maxbase
// Where:
//     start   - starting search value
//     end     - end search value
//     minbase - minimum n+1
//     maxbase - maximum n+1

// Note: Requires a 64bit CPU with POPCNT support


// header files
#include <stdio.h>
#include <stdlib.h>
#include <nmmintrin.h>
#include <math.h>
#include <stdint.h>
#include <limits.h>
#include <stdbool.h>
#include <locale.h>
#include <sys/time.h>


// metrics (enabled if compiled with -DMETRICS)
#ifdef METRICS
static uint64_t checks = 0;
static uint64_t gate2 = 0;
static uint64_t gate4 = 0;
static uint64_t gate8 = 0;
static uint64_t gate16 = 0;
static uint64_t gate32 = 0;
static uint64_t sums = 0;
static uint64_t primes = 0;
static uint64_t sub16 = 0;
static uint64_t plus16 = 0;
static uint64_t plus32 = 0;
#endif


// array containing which digit sums are prime
bool *smallprimes = NULL;


// lookup arrays for 4 digit sums by radix
unsigned char **digitSumLookup = NULL;


// compute the digit sum of the given value in the given radix
unsigned int sumDigits(uint64_t value, unsigned int radix) {
    // zero the sum
    uint64_t sum = 0;
    uint64_t dividor = 0;

    // sum the digits
    do {
        dividor = value / radix;
        sum += (value - (dividor * radix));
        value = dividor;
    } while (value);

    // return the sum
    return sum;
}


// initialise 4 digit sum lookup array
void initDigitSums(const unsigned int maxRadix, const unsigned int digits) {
    unsigned int i, j, r, arraySize;
    unsigned char *current = NULL;
    unsigned long allocated = 0;

    // allocate the array of lookup arrays
    digitSumLookup = (unsigned char **)malloc((maxRadix  + 1) * sizeof(unsigned char *));
    if (digitSumLookup) {
        // keep track of allocation size
        allocated = (maxRadix  + 1) * sizeof(unsigned char *);

        // for each radix
        for (r = 2; r <= maxRadix; r++) {
            // allocate the lookup array
            arraySize = r;
            for (j = 1; j < digits; j++) {
                arraySize *= r;
            }
            if ((digitSumLookup[r] = (unsigned char *)malloc(arraySize * sizeof(unsigned char)))) {
                // keep track of allocation size
                allocated += arraySize * sizeof(unsigned char);

                // populate the array
                current = digitSumLookup[r];
                for (i = 0; i < arraySize; i++) {
                    *current++ = sumDigits(i, r);
                }
            } else {
                fprintf(stderr, "Fatal: malloc failed for subarray\n");
                exit(EXIT_FAILURE);
            }
        }
    } else {
        fprintf(stderr, "Fatal: malloc failed for array\n");
        exit(EXIT_FAILURE);
    }

    // display allocation size
    printf("Lookup cache for %u digit sums for radix 2 to %u = %'lu bytes\n", digits, maxRadix, allocated);
}


// free 4 digit sum lookup array
void freeDigitSums(unsigned int maxRadix) {
    unsigned long r;

    // check if the array is allocated
    if (digitSumLookup) {
        // check each subarray
        for (r = 2; r <= maxRadix; r++) {
            // check if the subarray is allocated
            if (digitSumLookup[r]) {
                // free the subarray
                free(digitSumLookup[r]);
                digitSumLookup[r] = NULL;
            }
        }

        // free the array
        free(digitSumLookup);
        digitSumLookup = NULL;
    }
}


// compute the digit sum of the given value in the given radix using groups of 4 digits
// and returns whether that digit sum is prime
// Note: requires the digitSumLookup arrays to be allocated and populated
//       and the smallprimes array to be allocated and populated
bool sumDigitsIsPrime(unsigned long number, unsigned int radix) {
    // zero the sum
    unsigned long sum = 0;
    unsigned long dividor = 0;

    // get the lookup array for the given radix
    unsigned char *lookup = digitSumLookup[radix];

    // multiply the radix for 4 digits
    radix *= radix;
    radix *= radix;

    // sum the digits (assume at least 12 digits for speed)
    dividor = number / radix;
    sum += lookup[number - (dividor * radix)];
    number = dividor;

    dividor = number / radix;
    sum += lookup[number - (dividor * radix)];
    number = dividor;

    dividor = number / radix;
    sum += lookup[number - (dividor * radix)];
    number = dividor;

    // process any digits > 12
    while (number) {
        dividor = number / radix;
        sum += lookup[number - (dividor * radix)];
        number = dividor;
    }

    // return whether the digit sum is prime
    return smallprimes[sum];
}


// display the results for a given value
// re-compute the digit sums here since it's faster than storing them
// during the search
void displayResult(uint64_t value, unsigned int radix) {
    printf("%u: [%'lu] ", radix - 1, value);
    for (unsigned int i = 2; i <= radix; i++) {
        printf(" %u", sumDigits(value, i));
    }
    printf("\n");
    fflush(stdout);
}


// cache of last valid prime value
static uint64_t lastprime = 2;

// check if the supplied value is prime
// used to populate small primes array and to check candidate ds(n) values
// not used to check if digit sums are prime - these use the small primes array
bool isPrime(uint64_t value) {
    // check last known prime
    if (value == lastprime) {
        return true;
    }

    // check tiny primes
    if (value <= 3 || value == 5 || value == 7) {
        return value > 1;
    }

    // check simple mods
    if (value % 2 == 0 || value % 3 == 0 || value % 5 == 0 || value % 7 == 0) {
        return false;
    }

    // compute square root as test limit
    uint64_t i;
    uint64_t sq = (uint64_t)ceil(sqrt((double)value));

    // check small values
    if (value <= 211) {
        for (i = 7; i <= sq; i += 30) {
            if (value % i == 0 || value % (i + 4) == 0 || value % (i + 6) == 0 || value % (i + 10) == 0 ||
                value % (i + 12) == 0 || value % (i + 16) == 0 || value % (i + 22) == 0 || value % (i + 24) == 0) {
                // divisor found so not prime
                return false;
            }
        }

        // if no matches then prime
        return true;
    }

    // search divisors up to square root using 2, 3, 5, 7 wheel
    for (i = 11; i <= sq; i+= 210) {
        if (value % i == 0 || value % (i + 2) == 0 || value % (i + 6) == 0 || value % (i + 8) == 0 ||
            value % (i + 12) == 0 || value % (i + 18) == 0 || value % (i + 20) == 0 || value % (i + 26) == 0 ||
            value % (i + 30) == 0 || value % (i + 32) == 0 || value % (i + 36) == 0 || value % (i + 42) == 0 ||
            value % (i + 48) == 0 || value % (i + 50) == 0 || value % (i + 56) == 0 || value % (i + 60) == 0 ||
            value % (i + 62) == 0 || value % (i + 68) == 0 || value % (i + 72) == 0 || value % (i + 78) == 0 ||
            value % (i + 86) == 0 || value % (i + 90) == 0 || value % (i + 92) == 0 || value % (i + 96) == 0 ||
            value % (i + 98) == 0 || value % (i + 102) == 0 || value % (i + 110) == 0 || value % (i + 116) == 0 ||
            value % (i + 120) == 0 || value % (i + 126) == 0 || value % (i + 128) == 0 || value % (i + 132) == 0 ||
            value % (i + 138) == 0 || value % (i + 140) == 0 || value % (i + 146) == 0 || value % (i + 152) == 0 ||
            value % (i + 156) == 0 || value % (i + 158) == 0 || value % (i + 162) == 0 || value % (i + 168) == 0 ||
            value % (i + 170) == 0 || value % (i + 176) == 0 || value % (i + 180) == 0 || value % (i + 182) == 0 ||
            value % (i + 186) == 0 || value % (i + 188) == 0 || value % (i + 198) == 0 || value % (i + 200) == 0) {
            // divisor found so not prime
            return false;
        }
    }

    // if no matches then prime
    lastprime = value;
    return true;
}


// check primes in the given range for consecutive number base digit sum primes
// Note: requires "from" value to be in the form 30k+7
//       works for radix values >= 32
uint64_t checkRange32Plus(uint64_t from, uint64_t to, unsigned int radix) {
    unsigned int digitsum = 0;
    unsigned int r = 0;

    while (from <= to) {
#ifdef METRICS
checks++;
plus32++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
    #ifdef METRICS
    sums++;
    #endif
                                if (isPrime(from)) {
    #ifdef METRICS
    primes++;
    #endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
    #ifdef METRICS
    sums++;
    #endif
                                if (isPrime(from)) {
    #ifdef METRICS
    primes++;
    #endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
    #ifdef METRICS
    sums++;
    #endif
                                if (isPrime(from)) {
    #ifdef METRICS
    primes++;
    #endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
    #ifdef METRICS
    sums++;
    #endif
                                if (isPrime(from)) {
    #ifdef METRICS
    primes++;
    #endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
    #ifdef METRICS
    sums++;
    #endif
                                if (isPrime(from)) {
    #ifdef METRICS
    primes++;
    #endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 6;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
    #ifdef METRICS
    sums++;
    #endif
                                if (isPrime(from)) {
    #ifdef METRICS
    primes++;
    #endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // do a quick check for base 32
                        digitsum = _mm_popcnt_u64(from & 0x1084210842108421UL);
                        digitsum += (_mm_popcnt_u64(from & 0x2108421084210842UL)) << 1;
                        digitsum += (_mm_popcnt_u64(from & 0x4210842108421084UL)) << 2;
                        digitsum += (_mm_popcnt_u64(from & 0x8421084210842108UL)) << 3;
                        digitsum += (_mm_popcnt_u64(from & 0x0842108421084210UL)) << 4;
                        if (smallprimes[digitsum]) {
#ifdef METRICS
gate32++;
#endif
                            // check other bases starting at the largest since it will have fewest digits
                            r = radix;
                            while (r > 2 && sumDigitsIsPrime(from, r)) {
                                r--;
                            }
                            if (r == 2) { 
    #ifdef METRICS
    sums++;
    #endif
                                if (isPrime(from)) {
    #ifdef METRICS
    primes++;
    #endif
                                    return from;
                                }
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 6;

    }

    // not found
    return to + 1;
}


// check primes in the given range for consecutive number base digit sum primes
// Note: requires "from" value to be in the form 30k+7
//       works for radix values >= 16 and < 31
uint64_t checkRange16To31(uint64_t from, uint64_t to, unsigned int radix) {
    unsigned int digitsum = 0;
    unsigned int r = 0;

    while (from <= to) {
#ifdef METRICS
checks++;
plus16++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 6;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        if (smallprimes[_mm_popcnt_u64(from)]) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            if (smallprimes[digitsum]) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                if (smallprimes[digitsum]) {
#ifdef METRICS
gate8++;
#endif
                    // do a quick check for base 16
                    digitsum = _mm_popcnt_u64(from & 0x1111111111111111UL);
                    digitsum += (_mm_popcnt_u64(from & 0x2222222222222222UL)) << 1;
                    digitsum += (_mm_popcnt_u64(from & 0x4444444444444444UL)) << 2;
                    digitsum += (_mm_popcnt_u64(from & 0x8888888888888888UL)) << 3;
                    if (smallprimes[digitsum]) {
#ifdef METRICS
gate16++;
#endif
                        // check other bases starting at the largest since it will have fewest digits
                        r = radix;
                        while (r > 2 && sumDigitsIsPrime(from, r)) {
                            r--;
                        }
                        if (r == 2) { 
#ifdef METRICS
sums++;
#endif
                            if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                                return from;
                            }
                        }
                    }
                }
            }
        }

        // go to next value
        from += 6;

    }

    // not found
    return to + 1;
}


// check primes in the given range for consecutive number base digit sum primes
// Note: requires "from" value to be in the form 30k+7
//       works for radix values < 16
uint64_t checkRangeSub16(uint64_t from, uint64_t to, unsigned int radix) {
    bool allprime = false;

    while (from <= to) {
#ifdef METRICS
checks++;
sub16++;
#endif
        // do a quick check for base 2
        unsigned int digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 4;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 6;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 2;

#ifdef METRICS
checks++;
#endif
        // do a quick check for base 2
        digitsum = _mm_popcnt_u64(from);
        allprime = smallprimes[digitsum];
        if (allprime && radix >= 4) {
#ifdef METRICS
gate2++;
#endif
            // do a quick check for base 4
            digitsum = _mm_popcnt_u64(from & 0x5555555555555555UL);
            digitsum += (_mm_popcnt_u64(from & 0xAAAAAAAAAAAAAAAAUL)) << 1;
            allprime = smallprimes[digitsum];
            if (allprime && radix >= 8) {
#ifdef METRICS
gate4++;
#endif
                // do a quick check for base 8
                digitsum = _mm_popcnt_u64(from & 0x9249249249249249UL);
                digitsum += (_mm_popcnt_u64(from & 0x2492492492492492UL)) << 1;
                digitsum += (_mm_popcnt_u64(from & 0x4924924924924924UL)) << 2;
                allprime = smallprimes[digitsum];
            }
        }

        // if quick tests passed then try other bases
        if (allprime) {
#ifdef METRICS
gate16++;
#endif
            // check other bases starting at the largest since it will have fewest digits
            unsigned int r = radix;
            while (allprime && r > 2) {
                // check if the sum of digits in the base is prime
                allprime = sumDigitsIsPrime(from, r);
                r--;
            }
            if (allprime) {
#ifdef METRICS
sums++;
#endif
                if (isPrime(from)) {
#ifdef METRICS
primes++;
#endif
                    return from;
                }
            }
        }

        // go to next value
        from += 6;

    }

    // not found
    return to + 1;
}


// initialize fast prime lookup for digit sums
void initPrimes(unsigned int base) {
    // calculate maximum number of digits in the given base
    unsigned int number = ceil(log((double)ULLONG_MAX) / log((double)base));

    // calculate the largest digit sum
    unsigned int largestds = number * (base - 1);

    // allocate primes array
    smallprimes = (bool *)calloc(largestds, sizeof(*smallprimes));

    // populate primes array
    for (unsigned int i = 0; i < largestds; i++) {
        smallprimes[i] = isPrime(i);
    }

    printf("Cached primes up to %u\n", largestds);
}


// free fast prime lookup for digit sums
void freePrimes() {
    // free primes memory
    free(smallprimes);
    smallprimes = NULL;
}


// validate command line arguments
bool validateArguments(const char *program, uint64_t start, uint64_t end, unsigned int minradix, unsigned int maxradix) {
    if (minradix < 2 || minradix > 50 || maxradix < 2 || maxradix > 50) {
        fprintf(stderr, "%s: bases must be in the range 2 to 50\n", program);
        return false;
    }

    if (start > end) {
        fprintf(stderr, "%s: start must be less than end\n", program);
        return false;
    }

    return true;
}


// main entry point
int main(int argc, char **argv) {
    uint64_t start = 0UL;
    uint64_t end = 0UL;
    uint64_t current = 0UL;
    unsigned int radix = 16;
    unsigned int maxradix = 50;
    unsigned int maxmatch = 0;

    // check command line
    if (argc != 5) {
        fprintf(stderr, "Usage: %s start end minbase maxbase\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // decode arguments
    int argnum = 1;
    char *endptr = 0;
    start = strtoul(argv[argnum++], &endptr, 10);
    end = strtoul(argv[argnum++], &endptr, 10);
    radix = strtoul(argv[argnum++], &endptr, 10);
    maxradix = strtoul(argv[argnum++], &endptr, 10);
    if (!validateArguments(argv[0], start, end, radix, maxradix)) {
        exit(EXIT_FAILURE);
    }

    // set locale
    (void) setlocale(LC_NUMERIC, "en_US.utf8");   

    // convert starting point to 30k+7
    current = start;
    current = (30 * (current / 30)) + 7;

    // initialize fast prime lookup for digit sums
    initPrimes(maxradix);

    // initialize lookup for 4 digit sums
    initDigitSums(maxradix, 4);
    printf("Searching from %'lu to %'lu from base %u to %u\n", start, end, radix, maxradix);

    // start timing
    struct timeval timer;
    gettimeofday(&timer, 0);

    // main search algo only supports 30k+7 values so check here for 3 and 5 if in requested range
    // don't need to check 2 since digit sum in binary is not prime
    start |= 1UL;
    uint64_t tinyend = end;
    if (tinyend > 5) {
        tinyend = 5;
    }

    while (start <= tinyend && radix <= maxradix) {
        unsigned int r = radix;
        while (r > 2 && sumDigitsIsPrime(start, r)) {
            r--;
        }
        if (r == 2) {
            displayResult(start, radix);
            radix++;
        } else {
            start += 2;
        }
    }

    // check each number in the supplied range for each radix
    while (current <= end && radix <= maxradix) {
        // ensure current is in form 30k+7
        current = (30 * (current / 30)) + 7;

        // check the current range for the current radix
        if (radix < 16) {
            current = checkRangeSub16(current, end, radix);
        } else {
            if (radix < 32) {
                current = checkRange16To31(current, end, radix);
            } else {
                current = checkRange32Plus(current, end, radix);
            }
        }

        // if a ds(n) was found then display it
        if (current <= end) {
            displayResult(current, radix);
            maxmatch = radix;
        }

        // try next radix
        radix++;
    }

    // check if no matches were found
    if (current > end) {
        if (maxmatch == 0) {
            printf("No matches after -- primes\n");
        } else {
            printf("No matches after %u primes\n", maxmatch - 1);
        }
    }

    // display elapsed time
    struct timeval next;
    gettimeofday(&next, 0);
    unsigned int t = (next.tv_sec * 1000000 + next.tv_usec) - (timer.tv_sec * 1000000 + timer.tv_usec);
    printf("Time: %.2f seconds\n", (double)t / 1000000);

#ifdef METRICS
    // display metrics
    printf("Checks: %'lu\nSub16: %'lu\nPlus16: %'lu\nPlus32: %'lu\nGate2:  %'lu\nGate4:  %'lu\nGate8:  %'lu\nGate16: %'lu\nGate32: %'lu\nSums:   %'lu\nPrimes: %'lu\n", checks, sub16, plus16, plus32, gate2, gate4, gate8, gate16, gate32, sums, primes);
#endif

    // free digit sums lookup
    freeDigitSums(maxradix);

    // free fast prime lookup
    freePrimes();

    return EXIT_SUCCESS;
}

