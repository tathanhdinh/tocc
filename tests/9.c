int foo(int x, int y) {
    int z;
    if (x > y) {
        if (x < 10) {
            z = 5;
        } else {
            z = 11;
        }
    } else {
        if (y >= 6) {
            z = 95;
        } else {
            if (x <= 7) {
                z = 25;
            }
        }
    }
    return z;
}

int bar() {
    int x;
    int y;
    x = 44;
    y = 3;
    return foo(x, y);
}