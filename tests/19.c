int collatz(int n) {
	int next;
	if (n % 2 == 0) {
		next = n / 2;
	} else {
		next = 3 * n + 1;
	}
	int result;
	if (next == 1) {
		result = 0;
	} else {
		result = collatz(next) + 1;
	}
	return result;
}
