Working example:

```haskell
foo = Main.bar

main = Main.foo

bar =
  Text.putStrLn "Hello," >>
  Text.putStrLn ((\(x :: Text) -> x) " World!")
```

```
bash-3.2$ ./hell demo.hell
Hello,
 World!
```