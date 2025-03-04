## Build a distributable

This builds a fully static musl x86-64 Linux binary.

Outside of docker (because it uses Docker):

    hell scripts/static-build.hell

At the end you should have:

    hell-linux-x86-64bit

## Docs

Regenerate docs:

    stack run scripts/gen-docs.hell

Or within the docker container:

    docker exec hell stack run scripts/gen-docs.hell

Example:

    25-03-04 21:41:39.839 $ docker exec hell stack run scripts/gen-docs.hell
    Generating docs ...
    Rendering examples/01-hello-world.hell
    Rendering examples/02-interaction.hell
    Rendering examples/03-press-any-key.hell
    Rendering examples/04-writing-files.hell
    Rendering examples/05-lists.hell
    Rendering examples/06-polymorphism.hell
    Rendering examples/07-loops.hell
    Rendering examples/08-tuples.hell
    Rendering examples/09-processes.hell
    Rendering examples/10-current-directory.hell
    Rendering examples/11-env-vars.hell
    Rendering examples/12-fib.hell
    Rendering examples/13-concurrency.hell
    Rendering examples/14-text.hell
    Rendering examples/15-type-classes.hell
    Rendering examples/16-if.hell
    Rendering examples/17-reuse.hell
    Rendering examples/18-monads.hell
    Rendering examples/19-blog-generator.hell
    Rendering examples/20-dollar.hell
    Rendering examples/21-json.hell
    Rendering examples/22-records.hell
    Rendering examples/23-args.hell
    Rendering examples/24-exitcode.hell
    Rendering examples/25-sum-types.hell
    Rendering examples/26-reference-other-types.hell
    Rendering examples/27-discussion-64.hell
    Rendering examples/28-trees.hell
    Rendering examples/29-temp-files.hell
    Rendering examples/30-process-handlers.hell
    Rendering examples/31-open-file-handle.hell
    Rendering examples/32-optparse.hell
    Rendering examples/33-null-stream.hell
    Rendering examples/34-field-puns.hell
    Rendering examples/35-type-sigs.hell
    Generated docs.
