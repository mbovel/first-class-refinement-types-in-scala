# Semantic Types Mechanization

- [`refinement_types/`](refinement_types/): mechanization of System F with
  refinement and dependent function types in Rocq, using a definitional
  interpreter and semantic types.

## Build

Requires [Rocq](https://rocq-prover.org/) (tested with 9.0 and 9.2):

```bash
make
```

A successful build (exit code 0) means all proofs are machine-checked.

## Docker

The top-level artifact image includes Rocq 9.2. From the repository root:

```bash
docker run --rm --platform linux/amd64 refinement-artifact mechanization
```
