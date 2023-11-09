Building benchmark files in Coq
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml'
OCaml with extraction optimisations on. Bytecode:
./main 50
demo0 execution time: 0.001907 miliseconds
demo1 execution time: 1.345873 miliseconds
demo2 execution time: 0.609875 miliseconds
list_sum execution time: 5.150080 miliseconds
vs_easy execution time: 1196.338892 miliseconds
vs_hard execution time: 5572.000027 miliseconds
binom execution time: 971.048117 miliseconds
sha_fast execution time: 3076.499939 miliseconds
OCaml with extraction optimisations on. Native:
./mainopt 50
demo0 execution time: 0.000000 miliseconds
demo1 execution time: 1.197815 miliseconds
demo2 execution time: 0.411034 miliseconds
list_sum execution time: 1.753092 miliseconds
vs_easy execution time: 59.525013 miliseconds
vs_hard execution time: 707.523823 miliseconds
binom execution time: 182.524920 miliseconds
sha_fast execution time: 1089.809895 miliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml-noopt'
OCaml with extraction optimisations off. Bytecode:
./main 50
demo0 execution time: 0.001907 miliseconds
demo1 execution time: 1.357079 miliseconds
demo2 execution time: 0.618935 miliseconds
list_sum execution time: 4.220009 miliseconds
vs_easy execution time: 1390.561819 miliseconds
vs_hard execution time: 6331.865788 miliseconds
binom execution time: 963.052988 miliseconds
sha_fast execution time: 3167.626143 miliseconds
OCaml with extraction optimisations off. Native:
./mainopt 50
demo0 execution time: 0.000000 miliseconds
demo1 execution time: 1.112938 miliseconds
demo2 execution time: 0.326872 miliseconds
list_sum execution time: 1.699924 miliseconds
vs_easy execution time: 74.374914 miliseconds
vs_hard execution time: 684.942961 miliseconds
binom execution time: 141.510963 miliseconds
sha_fast execution time: 914.949179 miliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml-noopt'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction'
Malfunction with no optimisations
./mainopt 50
demo0 execution time: 0.000000 miliseconds
demo1 execution time: 1.184940 miliseconds
demo2 execution time: 0.385046 miliseconds
list_sum execution time: 2.251863 miliseconds
vs_easy execution time: 192.233086 miliseconds
vs_hard execution time: 1721.196890 miliseconds
binom execution time: 162.120104 miliseconds
color xecution time: 9.726379 seconds
sha_fast execution time: 1134.437084 miliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-o2'
Malfunction with -O2 optimisations
./mainopt 50
demo0 execution time: 0.000000 miliseconds
demo1 execution time: 1.029968 miliseconds
demo2 execution time: 0.390053 miliseconds
list_sum execution time: 1.731873 miliseconds
vs_easy execution time: 64.817905 miliseconds
vs_hard execution time: 953.161001 miliseconds
binom execution time: 155.874014 miliseconds
color xecution time: 5.510898 seconds
sha_fast execution time: 986.850023 miliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-o2'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified'
Bootstrapped Malfunction with no optimisations
./mainopt 50
demo0 execution time: 0.000954 miliseconds
demo1 execution time: 1.096010 miliseconds
demo2 execution time: 0.367165 miliseconds
list_sum execution time: 1.991987 miliseconds
vs_easy execution time: 181.107044 miliseconds
vs_hard execution time: 1634.962082 miliseconds
binom execution time: 150.362015 miliseconds
color xecution time: 9.617011 seconds
sha_fast execution time: 1239.794016 miliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified-o2'
Bootstrapped Malfunction with -O2 optimisations
./mainopt 50
demo0 execution time: 0.000000 miliseconds
demo1 execution time: 1.156092 miliseconds
demo2 execution time: 0.355959 miliseconds
list_sum execution time: 1.696110 miliseconds
vs_easy execution time: 65.499067 miliseconds
vs_hard execution time: 951.756001 miliseconds
binom execution time: 150.038958 miliseconds
color xecution time: 5.393737 seconds
sha_fast execution time: 985.840797 miliseconds
