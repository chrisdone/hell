Working example:

```haskell
foo = Main.bar

main = Main.foo

bar =
  Text.putStrLn "Hello," >>
  Text.putStrLn ((\(x :: Text) -> x) " World!")
```