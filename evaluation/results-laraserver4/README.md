# Paper results

The benchmark results used in the paper (`make_table.py` reads this
directory by default). Collected with the artifact image on `laraserver4`,
an x86-64 Linux server, otherwise idle, with the container pinned to four
physical cores (and their SMT siblings) on one NUMA node and 16 GB of
memory:

```bash
docker run --rm --cpuset-cpus=16-19,64-67 --cpuset-mems=0 --memory=16g --memory-swap=16g \
  -v "$PWD/evaluation/results-laraserver4:/work/evaluation/results" \
  refinement-artifact evaluation bench --suite all --runs 10
```

The campaign was started on 2026-07-20; suites are interleaved (runs are the
outer loop), one timestamped JMH result file per suite per run. `output.log`
is the console log of the campaign.
