# Semantic Types Mechanization

- [`refinement_types/`](refinement_types/): mechanization of System F with refinement and dependent function types in Rocq, using a definitional interpreter and semantic types.

## Build

```bash
make
```

## Docker

The top-level artifact image includes Rocq 9.2. From the repository root:

```bash
docker build -t refinement-artifact .
docker run --rm refinement-artifact mechanization
```
