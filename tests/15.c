int foo(int foo, int j) {
	return foo + j;
}

int bar(int j) {
	return foo(j, 88);
}

int foobar(int j) {
	int i = bar(foo(j ,77));
	return i + bar(i);
}
