Working example:

```haskell
foo = Main.bar

main = Main.foo

bar = do
  x :: () <- Text.putStrLn "Hello, please enter your name"
  line :: Text <- Text.getLine
  Text.putStrLn "Hello, "
  let msg :: Text = ((\(x :: Text) (y :: Int) -> x) line 5)
  Text.putStrLn msg
```

```
$ ./hell foo.hell
Hello, please enter your name
Dabe
Hello, 
Dabe
```
