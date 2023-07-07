#!/bin/bash

sed -e "s/\$lsl/\$l\_sl/g" -e "s/\$lor/\$l\_or/g" $@
