- get length of jitted code: `module.finalize_definitions()` generates code and needs to make read/write memory as executable, so SELinux (if exists) would not allow that; a workaround is to temporarily disable SELinux by `sudo setenforce 0`
- get AST of a program (e.g. `0.c`): `clang -cc1 -ast_dump 0.c`

echo "# uCc" >> README.md
git init
git add README.md
git commit -m "first commit"
git remote add origin git@github.com:tathanhdinh/uCc.git
git push -u origin master
