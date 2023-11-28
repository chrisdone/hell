Working example:

```haskell
foo = Main.bar

main = Main.foo

bar = do
  x :: () <- Text.putStrLn "Hello, please enter your name"
  line :: Text <- Text.getLine
  Text.putStrLn "Hello, "
  Text.putStrLn ((\(x :: Text) (y :: Int) -> x) line 5)
```

```
$ ./hell foo.hell
Hello, please enter your name
Dabe
Hello, 
Dabe
```