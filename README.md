# Hell: A Haskell shell

Here lies a prototype/experiment for the following question:
[can the normal Haskell REPL make a passable shell if it has file
completion and directory
awareness?](http://www.reddit.com/r/haskell/comments/1qzhce/using_haskell_to_write_deceptively_powerful/cdidvav?context=3)

It's a simple read-eval-print loop for Haskell that has some simple
awareness of the current directory and completion works. I whipped
this up in a few hours, it's only a couple hundred lines of code.

## What's it like?

It looks like this:

    Welcome to Hell!
    chris:~/$ ls
    Backups
    Books
    Desktop
    Documents
    Downloads
    Dropbox
    Emacs
    Hackerspace
    Mail
    Music
    Org
    Papers
    Pictures
    Projects
    Public

It has some UNIX basics:

    chris:~/$ cd "Projects/hell/"
    chris:~/Projects/hell$ ls
    .
    ..
    LICENSE
    README.md
    TAGS
    dist
    hell.cabal
    src
    chris:~/Projects/hell$ ls A
    .ghci
    .git
    .gitignore
    LICENSE
    README.md
    TAGS
    dist
    hell.cabal
    src
    chris:~/Projects/hell$ ls R
    /home/chris/Projects/hell/LICENSE
    /home/chris/Projects/hell/README.md
    /home/chris/Projects/hell/TAGS
    /home/chris/Projects/hell/dist
    …
    chris:~/Projects/hell$ cd
    chris:~/$

Functions like `cd` and `ls` are overloaded.

## How does it work?

It uses the GHC API (so please submit a pull request if it doesn't
work with your GHC version) and the Haskeline package to make a simple
read-eval-print loop, keeping track of any current directory
changes. The Haskeline package does completion at the prompt built-in.

It tries to run the line as an `IO a` statement, if that's the wrong
type, it evaluates it as an expression, printing the result with
`print`.

The functions like `cd`, `ls`, etc. are defined in `Hell.Unix`
which is imported in the default configuration (this is
configurable). There wasn't much thinking gone into these, I'm still
feeling my way around what I would prefer.

The commands of GHCi like `:t` and `:k` are not supported at this
time. Top-level bindings are not yet supported either. It does not
support completion of function names yet.

## Configuration

It is intended to be configured like XMonad, you `import Hell` and
then run `startHell` with the appropriate configuration.

There is an example in `src/main/Main.hs`, which you can run as
`hell-example` if you install this package.

``` haskell
-- | A sample Hell configuration.

module Main where

import Hell

-- | Main entry point.
main :: IO ()
main = startHell def
```

The default configuration as of writing is:

``` haskell
instance Default Config where
  def = Config
    { configImports =
        map ("import "++)
            ["Prelude"
             ,"GHC.Types"
             ,"System.IO"
             ,"Data.List"
             ,"Control.Monad"
             ,"Control.Monad.Fix"
             ,"System.Directory"
             ,"System.Process"
             ,"System.Environment"
             ,"Hell.Unix"]
    , configWelcome = "Welcome to Hell!"
    , configPrompt = \username pwd -> return (username ++ ":" ++ pwd ++ "$ ")
    , configRun = Nothing
    }
```

## Using shell libraries

Most shell libraries require running their own monad that runs ontop
of IO. For that, you can specify the `configRun` field to the
configuration.

* There's an example for the
  [shelly](http://hackage.haskell.org/package/shelly) package
  [here](https://github.com/chrisdone/hell/blob/master/src/main/Shelly.hs).

* There's an example for the
  [shellish](http://hackage.haskell.org/package/shellish) package
  [here](https://github.com/chrisdone/hell/blob/master/src/main/Shellish.hs).

## Why “Hell”? Surely a Haskell shell would be heaven!

It's an ironic name, like Little John. And who knows, a Haskell shell
_might_ be hell.

## You should add loads of custom syntax!

Mmm, maybe later. Please fork the project if you want to do that.

## Going forward…

I do have other things to be working on. But this is the kind of
project that you can make a start on and then start using it
immediately, incrementally adding little tidbits over the following
days and weeks. Getting `:t` and identifier completion would be my
next tidbits.

I would like to support more convenient piping, environment variables,
and I would like to start making type-safe wrappers to all my
favourite commands (e.g. grep, cabal, find, ghc, emacs).
