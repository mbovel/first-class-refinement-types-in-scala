# laraserver4-2 results

Date: 2026-07-30T15:21Z

Commit: ba7724e5fc05dc0c1767df30e03bd641b92a6a3e

First-class Scala version: 3.10.0-RC1-bin-20260730-0cb7a4c-NIGHTLY

Commands:

```bash
git submodule update --init implementation
git submodule update --init --recursive evaluation/stainless/stainless
git submodule update --init evaluation/schmid/refined-dotty
docker build --platform linux/amd64 -t refinement-artifact .
cd evaluation
mkdir results-laraserver4-2
chmod 777 results-laraserver4-2
docker run --rm --cpuset-cpus="16-19,64-67" --cpuset-mems=0 --memory=16g --memory-swap=16g -v "$PWD/results-laraserver4-2:/work/evaluation/results" refinement-artifact evaluation bench --suite all --runs 10 2>&1 | tee results-laraserver4-2/output.log
# interrupted due to a permission problem after 5 runs; re-running 5 runs
docker run --rm --cpuset-cpus="16-19,64-67" --cpuset-mems=0 --memory=16g --memory-swap=16g -v "$PWD/results-laraserver4-2:/work/evaluation/results" refinement-artifact evaluation bench --suite all --runs 5 2>&1 | tee results-laraserver4-2/output2.log
```

Table generated with:

```bash
./make_table.py --results-dir results-laraserver4-2  --output ../paper/bench_table.tex
```
