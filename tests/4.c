int foo() {
    struct Foo {
        int x;
    } foo;
    foo.x = 10;
    return foo.x;
}
