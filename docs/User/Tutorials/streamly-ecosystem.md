# Streamly Ecosystem

Streamly ecosystem consists of package built on top of streamly to provide
higher level functionality.

## streamly-process

Use operating system (OS) commands in Haskell programs as if they were
native Haskell functions, by treating their inputs and outputs as
Haskell streams. This allows you to write high-level Haskell scripts
that can perform tasks similar to shell scripts, but with C-like
performance, and with strong safety guarantees, refactorability, and
modularity.

The shell command `echo "hello world" | tr [a-z] [A-Z]` can be written as
follows using this package:

```haskell
>>> :{
   Command.toBytes [str|echo "hello world"|] -- Stream IO Word8
 & Command.pipeBytes [str|tr [a-z] [A-Z]|]   -- Stream IO Word8
 & Stream.fold Stdio.write                   -- IO ()
:}
HELLO WORLD
```

## streamly-coreutils

https://github.com/composewell/streamly-coreutils

GNU coreutils utilities implemented as Haskell functions using streamly. For
example: test, cp, ls, ln, mv, rm, touch, mkdir, pwd, cd, stat, readlink,
which, sleep etc.

## streamly-statistics

Similar to the `statistics` package but with streaming APIs.

## streamly-bytestring

Package for streamly and bytestring interoperation.

## streamly-lz4

Streaming APIs for lz4 compression and decompression.
