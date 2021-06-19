# stk-lang

A [joy](https://www.latrobe.edu.au/humanities/research/research-projects/past-projects/joy-programming-language)-style, statically typed, purely-functional, stack-oriented, combinator language in Haskell EDSL.

Merely a simple project that allows me to play with haskell's type-level hacking & template haskell while learning it :)

## Getting started
```haskell
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Lib where

import Language.Stk
import qualified Prelude as P

[stk|
step/1 = 1 swap -;

fact/1 =
    1
    </1 = 1 eq/>
    (step)
    (*)
    primrec;

20 10 5 1 $[] (fact) map "world" : "hello" : print
|]
```

```bash
H["hello","world",1,120,3628800,2432902008176640000]
```

## General Concepts

### Runtime Model
The runtime model of `stk-lang` is a __heterogeneous stack__. we will refer to this kind of stack as `Stk`. We will use `H[123, ...]` to denote the content of the `Stk`, and `[Int, ...]` to denote the type of the stack. `Stk` may contain 0 or some values that can be in different types. That is, `H[]`, `H[1, 'c', "string"]`, `H[H[H[], 42]]` are all valid `Stk`s.

### Combinators
#### Background Knowledge
Symbols in `stk-lang` are all __combinators__. A combinator consumes 0 or more elements from the top of the `Stk`, and pops 0 or more elements to the top of the `Stk`.

We denote the type of any combinator to be `[a, ..as] -> [b, c, ..ds]`, where `a`, `b`, `c`, ..., are types. `..as` and `..ds` denotes a sequence of types. We define the __arity__ of a combinator to be the length of the argument stack (_e.g._ Combinators of type `[a, b, c] -> [d]` has an arity of 3).

A combinator of type `[Int, Char] -> [Bool]` can be, obviously, evaluated on a `Stk` of type `[Int, Char]`, and yield a result `Stk` of type `[Bool]`. In addition, this combinator can also be evaluated on any `Stk` of type `[Int, Char, ..rs]` and produces a result `Stk` of type `[Bool, ..rs]`. Generally, a combinator of arity X can be evaluated on a `Stk`, if and only if, the top X elements on the `Stk` match the argument types of the combinator.

In `stk-lang`, Number literals like `1`, `42`, `3.14`, `-45`, ..., are all combinators of type `[] -> [a]` where `a` is either floating or `Int`. Similarly for char literals (`'a'`, `'c'`, etc.), and string literals (`"hello"`, `"world"`, etc.).

#### Definition
The syntax for defining a named combinator in `stk-lang` is:
```
<name>[/<arity>]? = <items>;
```
Where name is a string starting with a lower-case letter, arity is a natural number (can be omitted, if so, arity = 0), and items are a sequence of `stk-lang` expressions, separated by 1 or more spaces.

Upon defining a combinator, you may write the combinator body as if the arguments are already in the `Stk`. `stk-lang` performs auto type inference to the parameter types, so you do not need to give out the types explicitly.

#### Anonymous combinator
The syntax for defining a anonymous combinator (aka lambda) is:
```
</[<arity> =]? <items> />
```
Where arity is a natural number (can be omitted together with `=`, if so, arity = 0), and items are a sequence of `stk-lang` expressions, separated by 1 or more spaces.

A definition to a lambda will put the combinator onto the stack rather than evaluating it directly. You can use the `!` combinator to explicitly evaluate a combinator on top of the stack.

### `put` parentheses
A combinator, wrapped in 0 or more layers of parentheses, can be used as an expression item. Each layer of parentheses denotes the wrapped combinator is being `put`ed onto the `Stk`, rather than being evaluated directly.

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
| Combinator | Symbol | Type            |  Explaination  |
| :----------| :----: | :-------------- |  :------------ |
| `map`      | -      | ``     |  map |

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
