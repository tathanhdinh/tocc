#include <stdio.h>

int isprime(long p) {
    long d = 1;
    int ok = 1;
    int found = 1;
    while (ok) {
        d++;
        if (d * d > p) {
            ok = 0;
        } else {
            if (p % d == 0) {
                found = 0;
                ok = 0;
            }
        }
    }
    return found;
}

long nprime(int n) {
    long p = 1;
    int i = 0;
    while (i < n) {
        p++;
        if (isprime(p)) {
            i++;
        }
    }
    return p;
}

int main() {
    // int i = isprime(8);
    // if (i == 1) {
    //     printf("prime\n");
    // } else {
    //     printf("not prime\n");
    // }
    long p = nprime(1);
    printf("p = %ld\n", p);
}
