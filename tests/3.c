int foo() {
    int x;
    x = 7;
    int y;
    y = 0;
    {
        int x;
        x = 1;
        y = x + y;
    }
    return y - x;
}
