int sum_0n(int n) {
	int result;
	if (n <= 0) {
		result = 0;
	} else {
		int i;
		for (i = 0; i <= n; i++) {
			result += i;
		}
	}
	return result;
}
