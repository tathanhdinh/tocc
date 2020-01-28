long sum(short *a, int n) {
	long sum = 0;
	int i = 0;
	for (; i < n; i++) {
		a++;
		sum += *a;
	}
	return sum;
}
