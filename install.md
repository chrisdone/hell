Bootstrap (do this once):

    $ stack build
    $ cp .stack-work/dist/x86_64-linux/ghc-9.4.8/build/hell/hell ./hell

Build static binary (do from docker image):

    ./hell scripts/static-build.hell

Install static binary to /usr/bin/ (do from host OS):

    sudo ./hell scripts/install-hell.hell
