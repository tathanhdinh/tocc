long sum(short *a, int n) {
	long sum = 0;
	int i = 0;
	short *a_i;
	for (; i < n; i++) {
		a_i = a + i;
		sum += *a_i;
	}
	return sum;
}
