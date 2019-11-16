struct S {
    int x;
    int y;
};

int foo(struct S s) {
    return s.x + s.y;
}