int djb2(char *s) {
	int hash = 5381;
	while (*s != 0) {
		hash = ((hash << 5) + hash) + *s;
		s++;
	}
	return hash;
}
