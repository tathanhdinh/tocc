struct S {
    int x;
    int y;
};

int foo(struct S *s) {
    int a;
    a = s->x + s->y;
    return a;
}

int bar() {
    struct S s;
    s.x = 30;
    s.y = 40;
    return foo(&s);
}