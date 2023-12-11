# hell

Welcome to Hell :smiling_imp:

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [hell](#hell)
    - [Description](#description)
        - [Informal description](#informal-description)
        - [Design philosophy](#design-philosophy)
        - [More formal description](#more-formal-description)
    - [Instructions](#instructions)
        - [Running](#running)
        - [Building](#building)
    - [Performance](#performance)

<!-- markdown-toc end -->

## Description

Hell is an interpreted, statically-typed, shell scripting language
based on Haskell.

It's a WIP.

### Informal description

See `examples/` for a list of example scripts.

Example program:

```haskell
main = do
  Text.putStrLn "Please enter your name and hit ENTER:"
  name :: Text <- Text.getLine
  Text.putStrLn "Thanks, your name is: "
  Text.putStrLn name
```

Supports:

* UTF-8 and binary file I/O
* UTF-8 text operations (via `text`)
* Stdout/stderr/stdin I/O
* Directory, arguments, environment variables
* Concurrency (via `async`)
* Recursion (via `fix`)
* Running processes (via `typed-process`)

### Design philosophy

Turtle, Shelly, shell-conduit and Shh are "do shell scripting in
Haskell", but lack something. GHC is a large dependency to require for
running scripts, and the Haskell ecosystem is not capable of the
stability required. Scripts written in them are brittle and clunky.

My definition of a shell scripting language:

* A small interpreted language capable of launching processes
* No abstraction or re-use capabilities from other
  files/modules/packages
* Small, portable binary
* Stable, does not change in backwards-incompatible ways

Hell satisfies these criteria.

The other design decisions are:

* Use existing Haskell naming convention, don't rename things for the
  sake of it. Even if the names Haskell chose aren't great, or are
  long.
* Lean on and re-use concepts in the host system, even if they're
  flawed. Haskell's standard libraries get a lot of things right, and
  some things wrong. But stick to the intuitions that already are
  there where possible.
* Don't break common shell understanding. Current directory and
  environment variables are process-wide, even if one would prefer
  otherwise. If you want "local" directories, carry a path around.
* Use established API patterns that already work. (In particular this
  applies to the process launching API, which "script in Haskell"
  always tend to re-invent. I'm just re-using the API of
  typed-process.)

Names mirror their equivalent Haskell names (typically the
package). `Data.Text` is `Text.*`, `Control.Concurrent.Async` is
`async`, etc.

One exception to this rule is avoiding `type String`. Sorry, it's hard
to justify when `Text` is established.

Also, avoiding operators, because operators are a bit harder to deal
with combined with type applications.

There is only one monad, `IO`. So all monadic actions are specialised
upon it.

`mapM`/`forM` are specialised on lists (like Haskell 98), and live
under the `IO.` namespace. In future, there could be `Maybe.mapM`,
etc. It's also possible to have `traverse @IO @[]` type of thing, but
that seems unnecessarily verbose. List is mostly fine, especially for
scripting purposes.

### More formal description

* The language is a simply-typed lambda calculus, with Haskell syntax.
* Some primitives that can be polymorphic (but require immediately
  applied type applications).
* Polymorphic primitives such as `id` require passing the type of the
  argument as `id @Int 123`. You cannot define polymorphic lambdas of
  your own. It's not full System-F.
* Recursion is not supported. Use `Function.fix`.
* Supports type-classes (`Eq`, `Ord` and `Show` only), but the type be
  explicitly supplied. You can't define classes, or data types, of
  your own.
* The types and functions available lean directly on the host language
  (Haskell) and are either directly lifted, or a simplified layer over
  the original things.
* There is presently no type inference (but I will add it). All
  parameters of lambdas, or do-notation let bindings, must have their
  type declared via a pattern signature: `\(x :: Int) -> x`
* Globals of any kind must be fully qualified (`Main.foo` and
  `Text.putstrLn`), including the current module.

## Instructions

### Running

Presently the `hell` binary type-checks and interprets immediately a
program in `IO`.

    $ hell examples/01-hello-world.hell
    Hello, World!

See https://github.com/chrisdone/hell/releases for a statically-linked
amd64 Linux binary.

### Building

Build statically for Linux in a musl distribution:

    stack build --ghc-options="-static -optl-static"

## Performance

I did a quick `fib` test and it does fine compared with
`runhaskell`. There might be some undue strictness or something; I
haven't looked deeply into it. What's important is that it's not dog
slow, and it isn't.

```haskell
import Data.Function
import Data.Bool
main = print $ fib (30::Int)

fib :: Int -> Int
fib = fix (\fib i ->
    bool
        (bool
           ( (fib (subtract 1 i))
            + (fib (subtract 2 i)))
          1
          (i == 1))
        0
        (i == 0)
    )
```
```haskell
main = do
  Text.putStrLn (Int.show (Main.fib 30))

fib =
  Function.fix @(Int -> Int)
    (\(fib :: Int -> Int) -> \(i :: Int) ->
      Bool.bool @Int
        (Bool.bool @Int
           (Int.plus (fib (Int.subtract 1 i))
                     (fib (Int.subtract 2 i)))
           1
           (Int.eq i 1))
        0
        (Int.eq i 0)
    )
```

```
$ GHCRTS='-s' runhaskell test.hs
832040
     962,232,208 bytes allocated in the heap
      30,899,272 bytes copied during GC
       9,916,872 bytes maximum residency (4 sample(s))
         187,960 bytes maximum slop
              24 MiB total memory in use (0 MB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0       109 colls,     0 par    0.022s   0.022s     0.0002s    0.0037s
  Gen  1         4 colls,     0 par    0.067s   0.067s     0.0168s    0.0216s

  TASKS: 5 (1 bound, 4 peak workers (4 total), using -N1)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.001s elapsed)
  MUT     time    3.758s  (  3.804s elapsed)
  GC      time    0.089s  (  0.089s elapsed)
  EXIT    time    0.001s  (  0.007s elapsed)
  Total   time    3.849s  (  3.900s elapsed)

  Alloc rate    256,067,353 bytes per MUT second

  Productivity  97.6% of total user, 97.5% of total elapsed

$ stack run -- examples/12-fib.hell +RTS -s
832040
   1,892,556,080 bytes allocated in the heap
       1,588,368 bytes copied during GC
         150,208 bytes maximum residency (2 sample(s))
          87,360 bytes maximum slop
              41 MiB total memory in use (0 MB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0       451 colls,   451 par    0.299s   0.158s     0.0004s    0.0006s
  Gen  1         2 colls,     1 par    0.001s   0.001s     0.0004s    0.0006s

  Parallel GC work balance: 4.14% (serial 0%, perfect 100%)

  TASKS: 18 (1 bound, 17 peak workers (17 total), using -N8)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.004s  (  0.002s elapsed)
  MUT     time    1.971s  (  1.588s elapsed)
  GC      time    0.300s  (  0.159s elapsed)
  EXIT    time    0.002s  (  0.001s elapsed)
  Total   time    2.278s  (  1.750s elapsed)

  Alloc rate    960,062,184 bytes per MUT second

  Productivity  86.5% of total user, 90.8% of total elapsed


```
