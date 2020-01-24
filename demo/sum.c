int sum(short *a, int n) {
	int sum = 0;
	int i = 0;
	int *a_i;
	for (; i < n; i++) {
		a_i = a + i;
		sum += *a_i;
	}
	return sum;
}
