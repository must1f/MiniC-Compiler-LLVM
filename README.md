# MiniC Compiler

A full end-to-end compiler for **MiniC** — a statically-typed subset of C — written from scratch in **C++17** using the **LLVM 21.1.0** infrastructure. The compiler takes MiniC source code through lexing, parsing, semantic analysis, and LLVM IR code generation, producing executable binaries targeting x86.

---

## Features

### Frontend
- **Hand-written lexer** — tokenises MiniC source with precise line/column tracking
- **LL(2) recursive descent parser** — predictive, table-free, with a `std::deque`-based lookahead buffer enabling arbitrary token peeking
- **Left-recursion eliminated** — expression grammar transformed into a seven-level precedence hierarchy (`or → and → equality → relational → additive → multiplicative → unary`)
- **AST construction** — full abstract syntax tree with `unique_ptr` node ownership and virtual `codegen()` / `to_string()` dispatch

### Semantic Analysis & Type System
- **Three-type hierarchy**: `bool → int → float` mapped to LLVM `i1 → i32 → float`
- **Implicit widening conversions**: `bool→int` (`CreateZExt`), `int→float` (`CreateSIToFP`)
- **Narrowing conversions** rejected at compile time (except in boolean contexts, following C99 semantics)
- **Three-level symbol table**: local `AllocaInst*` map → global `GlobalVariable*` map → type metadata table, with full lexical scoping and shadowing support
- **Semantic checks**: undefined variables, argument count/type mismatches, duplicate global declarations, return type consistency

### Code Generation (LLVM IR)
- All locals use `alloca` in the entry block (enabling LLVM mem2reg promotion)
- Control flow: `if/else` (three basic blocks + `CreateCondBr`) and `while` loops (header / body / after blocks)
- **Multi-dimensional arrays (1D/2D/3D)**: nested LLVM array types, `GetElementPtr` with correct index lists, C-style pointer decay for array parameters
- Outputs valid `.ll` IR consumed directly by `lli` or `llc`

### Developer Experience
- **Four debug levels** (`user`, `parser`, `codegen`, `verbose`) via `-d` flag or `MCCOMP_DEBUG` env var
- **Colour-coded error output** with source-line display, caret pointer, and "Did you mean?" suggestions via Levenshtein distance (edit distance ≤ 2)
- Parser call-stack tracing with depth-indented entry/exit logging

---

## Language Support

MiniC supports: `int`, `float`, `bool` types · arithmetic and logical operators · relational operators · `if/else` · `while` · functions with typed parameters · `extern` declarations · global and local variable declarations · 1D, 2D, and 3D arrays

---

## Project Structure

```
mccomp.cpp      # Compiler source: lexer, parser, AST, semantic analysis, codegen
Makefile        # Build script (clang++ / LLVM)
report.pdf      # Design report: grammar, FIRST/FOLLOW sets, design decisions
```

---

## Build & Run

> Requires LLVM 21.1.0 and clang++ with C++17 support.

```bash
# Build
make

# Compile a MiniC program
./mccomp your_program.c

# Link and execute (provide your own driver that calls into the compiled code)
clang++ driver.cpp output.ll -o program
./program
```

### Debug mode

```bash
./mccomp myfile.c -d parser    # trace parser entry/exit
./mccomp myfile.c -d codegen   # trace IR generation
./mccomp myfile.c -d verbose   # full trace
```

---

## Example

```c
// fib.c
int fib(int n) {
    if (n <= 1) return n;
    return fib(n - 1) + fib(n - 2);
}
```

```bash
./mccomp fib.c
lli output.ll
```

---

## Design Notes

The grammar is **LL(2)** — a single token of lookahead is insufficient because `IDENT` at the start of an expression can lead to assignment (`x = ...`), array access (`x[i]`), function call (`x(...)`), or a plain variable reference. Full FIRST/FOLLOW set derivations and the transformed grammar are documented in `report.pdf`.

---

## Tech Stack

`C++17` · `LLVM 21.1.0` · `clang++` · `GNU make`
