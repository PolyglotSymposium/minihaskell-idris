# MiniHaskell in Idris

Blatantly ported from the excellent [plzoo](https://github.com/andrejbauer/plzoo/tree/master/src/minihaskell).

## Compiling

```bash
idris MiniHaskell.idr -o mh
```

## Tests
After compiling run

```bash
./tests.sh
```

New tests need
  1. a test file under [tests](tests)
  2. the file's name (w/o ext) added to [tests.sh](tests.sh)
  3. an expectation file (file-name-exp.mh) in [tests](tests)
