#!/bin/bash

gsed -i -e "s/\$land/\$l\_and/g" -e "s/\$lsr/\$l\_sr/g" -e "s/\$lsl/\$l\_sl/g" -e "s/\$lor/\$l\_or/g" -e "s/\(global \$PrimFloat \$ltb\)/global \$PrimFloat \$lt/g" -e "s/\(global \$PrimFloat \$eqb\)/global \$PrimFloat \$eq/g" -e "s/\(global \$PrimInt63 \$eqb\)/global \$PrimInt63 \$equal/g" $@
