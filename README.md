# stk-lang

## Intro
A [joy](https://www.latrobe.edu.au/humanities/research/research-projects/past-projects/joy-programming-language)-style, statically typed, purely-functional, stack-oriented, combinator language in Haskell EDSL.

Merely a simple project that allows me to play with haskell's type-level hacking & template haskell while learning it :)

## Getting started
```haskell
{-# LANGUAGE QuasiQuotes #-}
import qualified Language.Stk as STK

[stk|>STK 
    nine = 3 2 1 (+) (*) ! !;
    
    stop/1 = 1 ==
    sub1/1 = -1 +

    factorial/1 = 1 (step) (sub) (*) primrec

    fact10 = 10 factorial
|]

main = print $ STK.runStk fact10
```

```bash
> ghc main.c -o a.out; ./a.out
H[3628800]
```

## General Concepts

### Runtime Model
The runtime model of `stk-lang` is a heterogeneous stack (we will refer to this kind of stack as `Stk`. We will use `H[123, ...]` to denote the content of the `Stk`, and `[Int, ...]` to denote the type of the stack ). `Stk` may contain 0 or some values that can be in different types. That is, `H[]`, `H[1, 'c', "string"]`, `H[H[H[], 42]]` are all valid `Stk`s.

### Combinators
Symbols in `stk-lang` are all combinators.

## Combinator Tutorial
### Basic Combinators
#### `put` aka `()` - put a function to the stack
#### `call` aka `!` - call the function on the top of the stack

## `Stk`-related Combinators
#### `new` aka `[]` - create a sub-`Stk`
#### `cons` aka `:` - put an element to the top of the sub-`Stk`
#### `uncons` aka `~:`  
#### `flat`  