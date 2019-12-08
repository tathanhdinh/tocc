int foo(int n) {
    int i;
    int sum;
    sum = 0;
    for (i = 0; i < n; i++) {
        sum = sum + 2 * i + 1;
    }
    return sum;
}

int bar() {
    return foo(4);
}
