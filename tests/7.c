struct S {
    int x;
    int y;
};

int foo(struct S s) {
    return s.x + s.y;
}

int bar() {
    struct S s;
    s.x = 10;
    s.y = 15;
    return foo(s);
}
