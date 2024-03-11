# Benchmarks

Running the benchmarks assumes an intel-based Linux machine.
First you need to run the following commands on the host machine (i.e. when docker is used, outside of docker) to ensure that processor speed stays constant through benchmarking, e.g. that no thermal throttling occurs.

```bash
echo performance | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor
sudo cpupower idle-set -D 0
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

You need to have installed `core_bench.v0.16.0``.

Then on the client (i.e. when docker is used, inside of docker)

```bash
make
```
