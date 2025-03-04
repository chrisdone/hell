# docker run -d --name hell -it -v`pwd`:`pwd` -w`pwd` ghcr.io/chrisdone/hell-build:2025-03-04 sh

FROM alpine:20250108

RUN apk add stack ghc

ADD stack.yaml /stack.yaml
ADD package.yaml /package.yaml

RUN stack setup && stack update

ADD src/Hell.hs /src/Hell.hs

RUN apk add musl-dev

RUN stack build

RUN apk add pandoc

RUN apk add gmp-static

RUN apk add git

RUN apk add ncurses-dev
