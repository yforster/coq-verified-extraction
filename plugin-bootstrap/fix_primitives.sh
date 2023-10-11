#!/bin/bash

gsed -i -e "s/\$land/\$l\_and/g" -e "s/\$lsr/\$l\_sr/g" -e "s/\$lsl/\$l\_sl/g" -e "s/\$lor/\$l\_or/g" -e "s/(global \$PrimFloat/(global \$Coq_float64/g" -e "s/(global \$PrimInt63/(global \$Coq_uint63/g" -e "s/(global \$Float64 \$ltb)/(global \$Coq_float64 \$lt)/g" -e "s/(global \$Float64 \$eqb)/(global \$Coq_float64 \$eq)/g" -e "s/(global \$Uint63 \$ltb)/(global \$Coq_uint63 \$lt)/g" -e "s/(global \$Uint63 \$eqb)/(global \$Coq_uint63 \$equal)/g" -e "s/(global \$Uint63/(global \$Coq_uint63/g" -e "s/(global \$Float64/(global \$Coq_float64/g" $@
