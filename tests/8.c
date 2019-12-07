int foo(int x) {
    int y;
    y = 7;
    if (x) {
        y = 3;
    }

    return y;
}

int bar() {
    return foo(1);
}
