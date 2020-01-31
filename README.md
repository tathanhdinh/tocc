# uCc: untyped (or micro) C compiler

`uCc` is a small C compiler which presents the idea of *type-flattening obfuscation*.
Its objectives is to make the type reconstruction from binary code hard. You may try to decompile<sup>1</sup> some obfuscated object files in [demo](./demo) to see the effect on function signatures.

`uCc` compiles with Rust >= 1.40.0 and is tested on Linux.

## Compilation
```
cargo check
cargo test
```

and installation (optional)

```
cargo install --path .
```

Otherwise, `ucc` can be used in the project's folder with
```
cargo run --
```


## Usage

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
to jit must be specified
```
ucc demo/slen.c -j -f slen
```

- Sometimes, the obfuscated code is to *heavy*<sup>4</sup> then Hex-Rays may complain "too big function" (other decompilers like Ghidra or JEB have no such limit), then the mode *lightweight* can be used. In this mode, most of obfuscation transformations are removed
```
ucc demo/slen.c -o slen_light.o -l
```

## Notes

 - The compiler is in development, in the current state it lacks *many features*<sup>3</sup> of a full C compiler, for example it can generate object files only, executable is not yet possible. If you want to run the file, please link it using a C compiler:

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

 - The compiler is probabilistic, it generates a different but computationally equivalent output each time invoked.

___

<sup>1</sup> Some decent decompilers: [Hex-Rays](https://www.hex-rays.com/products/decompiler/index.shtml) (which provides an [evaluation](https://out7.hex-rays.com/demo/request)), [Ghidra](https://ghidra-sre.org/), [JEB](https://www.pnfsoftware.com/), etc.

<sup>2</sup> In some Linux distro with SELinux, JIT is forbidden because of [W^X protection](https://en.wikipedia.org/wiki/W%5EX), this can be temporarily disabled using `sudo setenforce 0`.

<sup>3</sup> There is still no pre-processing so include, define, macro, etc. do not work yet, neither comments in source codes. Please look at examples in [tests](./tests/) and [demo](./demo/) for the kind of programs that `uCc` currently support.

<sup>4</sup> This is an unwanted effect, putting unnecessary noise into the machine code is not the goal of `uCc`.
