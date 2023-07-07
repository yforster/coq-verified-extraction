#!/bin/bash

sed -i -e "s/\$lsl/\$l\_sl/g" -e "s/\$lor/\$l\_or/g" -e "s/\(global \$PrimFloat \$ltb\)/global \$PrimFloat \$lt/g" -e "s/\(global \$PrimFloat \$eqb\)/global \$PrimFloat \$eq/g" $@
