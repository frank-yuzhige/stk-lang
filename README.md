# stk-lang

## Intro
A [joy](https://www.latrobe.edu.au/humanities/research/research-projects/past-projects/joy-programming-language)-style, statically typed, purely-functional, stack-oriented, combinator language in Haskell EDSL.

Merely a simple project that allows me to play with haskell's type-level hacking & template haskell while learning it :)

## Getting started
```haskell
{-# LANGUAGE QuasiQuotes #-}
module SomeModule where
import Language.Stk
import qualified Prelude as P

[stk|
nine = 3 2 1 * +;

step/1 = 1 swap -;

fact/1 = 
    1 
    1 (eq) curry ! 
    (step) 
    (*) 
    primrec;

fact10 = 10 fact;

pythX/2= dup * swap dup * + sqrt round;

pyth345 = 3 4 pythX;

results = pyth345 fact10;
|]

main = print $ STK.runStk results
```

```bash
H[3628800,5]
```

## General Concepts

### Runtime Model
The runtime model of `stk-lang` is a __heterogeneous stack__. we will refer to this kind of stack as `Stk`. We will use `H[123, ...]` to denote the content of the `Stk`, and `[Int, ...]` to denote the type of the stack. `Stk` may contain 0 or some values that can be in different types. That is, `H[]`, `H[1, 'c', "string"]`, `H[H[H[], 42]]` are all valid `Stk`s.

### Combinators
Symbols in `stk-lang` are all __combinators__. A combinator consumes 0 or more elements from the top of the `Stk`, and pops 0 or more elements to the top of the `Stk`. 

We denote the type of any combinator to be `[a, ..as] -> [b, c, ..ds]`, where `a`, `b`, `c`, ..., are types. `..as` and `..ds` denotes a sequence of types. We define the __arity__ of a combinator to be the length of the argument stack (_e.g._ Combinators of type `[a, b, c] -> [d]` has an arity of 3).

A combinator of type `[Int, Char] -> [Bool]` can be, obviously, called on a `Stk` of type `[Int, Char]`, and yield a result `Stk` of type `[Bool]`. In addition, this combinator can also be called on any `Stk` of type `[Int, Char, ..rs]` and produces a result `Stk` of type `[Bool, ..rs]`. Generally, a combinator of arity X can be called on a `Stk`, if and only if, the top X elements on the `Stk` match the argument types of the combinator.

In `stk-lang`, Number literals like `1`, `42`, `3.14`, `-45`, ..., are all combinators of type `[] -> `

## Combinator Cheatsheet
### Basic Combinators
| Combinator | Symbol | Type            |  Explaination  |
| :----------| :----: | :-------------- |  :------------ |
| `pop`      | -      | `[a] -> []`     |  Remove the top element from the current stack |
| `call`     | `!`    | `[..a -> ..r, ..a] -> [..r]` |  Call the function on the remaining stack |
| `dup`      | -      | `[a] -> [a, a]` |  Duplicate the top element |
| `over`     | -      | `[a, b] -> [b, a, b]` |  Duplicate the 2nd-top element, and bring it over to the top |
| `swap`     | -      | `[a, b] -> [b, a]` |  Swap the top 2 elements |
| `rot`      | -      | `[a, b, c] -> [b, c, a]` |  Rotate the top 3 elements |


### Higher-order Combinators


### `Stk` Combinators

### Recursion Combinators
| Combinator | Type            |  Explaination  |
| :----------| :-------------- |  :------------ |
| `primrec`  | `[[a, a] -> a, a -> a, a -> Bool, a, a] -> [a]` | A more generalized joy's `primrec` |
| `catarec`  | `[[a, b] -> b, b, hom@a[..as]] -> [a]` | Fold, aka catamorphism |

### Core Combinators
These combinators are not normally used when coding in `stk-lang`. They are mainly used internally by the `Core` library.
| Combinator | Symbol | Type            |  Explaination  |
| :----------| :----: | :-------------- |  :------------ |
| `put`      | `()`   | `a -> [a]`      |  Put an arbitrary element to the stack |
