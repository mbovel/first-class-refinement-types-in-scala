# Semantic Types Mechanization

- [`refinement_types/`](refinement_types/): mechanization of System F with refinement and dependent function types in Rocq, using a definitional interpreter and semantic types.

## Build

```bash
make
```

## Docker

To build and check the mechanization under Rocq 9.2 in a container:

```bash
docker build -t refinement-mech .
docker run --rm refinement-mech
```
