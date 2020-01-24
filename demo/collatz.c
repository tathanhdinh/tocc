int collatz(int n) {
	int next = 3 * n + 1;
	if (n % 2 == 0) {
		next = n / 2;
	}

	if (next == 1) {
		return 1;
	} else {
		return collatz(next) + 1;
	}
	return 0;
}
