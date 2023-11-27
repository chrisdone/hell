Working example:

```haskell
foo = Main.bar

main = Main.foo

bar = Text.putStrLn "Hello, World!"
```