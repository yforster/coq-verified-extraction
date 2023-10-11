type ('a, 'b) prod =
| Pair of 'a * 'b

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

val def_MetaCoq_VerifiedExtraction_Benchmarks_lib_tests_color : unit -> (z, z) prod
