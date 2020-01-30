# uCc: untyped (or micro) C compiler

`uCc` is a small C compiler which presents the idea of *type-flattening obfuscation*.
Its objectives is to make the type reconstruction from binary code hard. To get the idea, try to decompile<sup>1</sup> some object files in [demo](./demo) to see the output.

`uCc` compiles with Rust 1.40.0 and is tested in Linux only, it should work on Windows in WSL but this is not tested.

## Compilation
```
cargo check
cargo test
```

and installation (optional)

```
cargo install --path .
```

or it can be used directly by invoking
```
cargo run --
```
instead of `ucc`.

## Usage

The help is given by:
```bash
ucc --help (or cargo run -- --help)

Positional arguments:
  src          source code file

Optional arguments:
  -h, --help   print usage
  -o output    output object file
  -l           lightweight obfuscation
  -v           verbose
  -f function  function to jit
  -j           jit
```

## Example
- Obfuscate the [`strlen`](./demo/slen.c) function:
```
ucc demo/slen.c -o slen_flat.o
```

- The IR code can be observed with `-v`
```
ucc demo/slen.c -o slen_flat.o -v
```

- The mode JIT<sup>2</sup> can be used to see immediately the machine code, the function
to jit must be given
```
ucc demo/slen.c -j -f slen
```

- Sometimes, the obfuscation is to *heavy* then Hex-Rays may complain "too big function" (other
decompilers like Ghidra or JEB have no such limit), then the mode *lightweight* can be used.
In this mode, most of obfuscation transformation are removed
```
ucc demo/slen.c -o slen_light.o -l
```

## Notes

The compiler is in active development, it lacks many features of a full C compiler, for example
it can generate object files only, executable is not yet possible. If you want to run the file, link
it using a C compiler:

```C
// create a main.c
#include <stdio.h>

extern int slen(char *s);

int main(int argc, char* argv[]) {
	char *hello = "hello world";
	printf("len = %d\n", slen(hello));
}

// compile and link with the obfuscated slen_flat.o
gcc main.c slen_flat.o -o slen

// then run
./slen
len = 11
```

___

<sup>1</sup> Some decent decompilers: [Hex-Rays](https://www.hex-rays.com/products/decompiler/index.shtml) (which provides an [evaluation](https://out7.hex-rays.com/demo/request)), [Ghidra](https://ghidra-sre.org/), [JEB](https://www.pnfsoftware.com/), etc.

<sup>2</sup> In some Linux distro with SELinux, JIT is forbidden because of [W^X protection](https://en.wikipedia.org/wiki/W%5EX), this can be temporarily disabled using `sudo setenforce 0`.
