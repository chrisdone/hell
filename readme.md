# hell

Hell is a statically-typed shell scripting language and
implementation, which re-uses Haskell's standard library and runtime.

## Running

Presently the `hell` binary type-checks and interprets immediately a
program in `IO`.

    $ hell examples/01-hello-world.hell
    Hello, World!

See https://github.com/chrisdone/hell/releases for a statically-linked
amd64 Linux binary.

## Informal description

See `examples/` for a list of example scripts.

Example program:

```haskell
main = do
  Text.putStrLn "Please enter your name and hit ENTER:"
  name :: Text <- Text.getLine
  Text.putStrLn "Thanks, your name is: "
  Text.putStrLn name
```

## More formal description

The language is a DSL, it's the simply-typed lambda calculus, plus
some syntactic sugar and some primitives that can be polymorphic (but
require immediately applied type applications). Recursion is not
supported.

Polymorphic primitives such as `id` require passing the type of the
argument as `id @Int 123`. You cannot define polymorphic lambdas of
your own. It's not full System-F.

It will support type-classes (for equality, dictionaries, etc), but
the dictionaries must be explicitly supplied. You can't define
classes, or data types, of your own.

The types and functions available lean directly on the host language
(Haskell) and are either directly lifted, or a simplified layer over
the original things.

There is (presently) no type inference. All parameters of lambdas, or
do-notation let bindings, must have their type declared via a pattern
signature.

```haskell
\(x :: Int) -> x
```

## Building

Build statically for Linux in a musl distribution:

    stack build --ghc-options="-static -optl-static"
