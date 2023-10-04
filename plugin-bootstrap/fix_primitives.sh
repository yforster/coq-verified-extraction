#!/bin/bash

gsed -i -e "s/\$land/\$l\_and/g" -e "s/\$lsr/\$l\_sr/g" -e "s/\$lsl/\$l\_sl/g" -e "s/\$lor/\$l\_or/g" -e "s/(global \$PrimFloat/(global \$Float64/g" -e "s/(global \$PrimInt63/(global \$Uint63/g" -e "s/(global \$Float64 \$ltb)/(global \$Float64 \$lt)/g" -e "s/(global \$Float64 \$eqb)/(global \$Float64 \$eq)/g" -e "s/(global \$Uint63 \$ltb)/(global \$Uint63 \$lt)/g" -e "s/(global \$Uint63 \$eqb)/(global \$Uint63 \$equal)/g" $@
