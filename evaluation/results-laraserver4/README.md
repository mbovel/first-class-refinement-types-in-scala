# laraserver4 results

Date: 2026-07-20T15:35Z

Commit: 3fde85d277495653309caa004f800230ea79f7db

Command:

```bash
bovel@laraserver4:/localhome/bovel/first-class-refinement-types-in-scala/evaluation$ docker run --rm --cpuset-cpus="16-19,64-67" --cpuset-mems=0 --memory=16g --memory-swap=16g -v "$PWD/results-laraserver4:/work/evaluation/results" refinement-bench evaluation --suite all --runs 10 2>&1 | tee "run-$(date +%Y-%m-%d-%H%M).log"
```

Shortcomings:

- `qualifiedTypes` feature always enabled in the first-class baseline (fixed in 602512a3707771eaaaf8a921d1c876ffd11766a3).
- `infer-measures = false` not set in Stainless benchmarks (unfaire extra work for Stainless, fixed in 1028bf6ba829e203deed8a0f933b29673e47f3ae).
