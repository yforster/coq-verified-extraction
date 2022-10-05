#!/usr/bin/env bash

echo "Cleaning result of extraction"

if [ ! -d "extraction" ]
then
    mkdir src
fi

shopt -s nullglob # make the for loop do nothnig when there is no *.ml* files

files=`cat template.files`

if [[ ! -f "metacoq_malfunction_plugin.cmxs" ||
           "metacoq_malfunction_plugin.cmxs" -ot "../theories/Extraction.vo" ]]
then
    cd extraction
    # Move extracted modules to build the plugin
    # Uncapitalize modules to circumvent a bug of coqdep with mllib files
    for i in *.ml*
      do
      newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
      if [ $i != $newi ]
      then
          # echo "Moving " $i "to" $newi;
          mv $i tmp;
          mv tmp $newi;
      fi
    done
    cd ..

    # Remove extracted modules already linked in template_coq_plugin, checker and pcuic.
    echo "Removing:" $files
    rm -f $files
else
    echo "Extraction up-to date"
fi
