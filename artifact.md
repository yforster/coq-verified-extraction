# Artifact guidelines

The artifact is a virtual machine, that can be run with qemu, see e.g. [this page](https://wiki.gentoo.org/wiki/QEMU/QEMU_front-ends) for front-ends.

The username is `coq`, no password is necessary.

The artifact consists of the Coq implementation and proofs of extraction and the benchmarks. The code can also be found [here](https://github.com/MetaCoq/metacoq/tree/v1.3-8.17) for the general MetaCoq framework and [here](https://github.com/yforster/coq-malfunction/tree/db5240e9f4fb54ee0057c947d29aa2e59920ef91) for verified extraction.

We recommend checking three central parts:

## Theorem from section 2.3

The central theorem on extraction for first-order values is `verified_malfunction_pipeline_theorem` in line 982 of file `theories/Pipeline.v`.

## Theorem from section 2.4

The central theorem on extraction for first-order functions is `interoperability_firstorder_function` in line 2579 of file `theories/Firstorder.v`.

Issuing `make -f Makefile.coq theories/Firstorder.vo` in the directory `coq-malfunction` of the home directory of the `coq` user re-checks this proof, and prints the results of the `Print Assumptions` command at the end of the file.

## Benchmarks

The `coq-malfunction/benchmarks` directory contains the benchmarks discussed in section 6. They can be run with the command `make`. The `README.md` file in this directory contains more instructions how to ensure that processor speed stays constant during the execution.

Note that the exact implementation of timing for benchmarks was slightly changed since the submitted version by request of the reviewers.
