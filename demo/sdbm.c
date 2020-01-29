int sdbm(char *s) {
	int hash = 0;
	while (*s != 0) {
		hash = *s + (hash << 6) + (hash << 16) - hash;
		s++;
	}
	return hash;
}
