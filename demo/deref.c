int inc_deref(int *x) {
	int *p = x;
	p += 1;
	return *p;
}
