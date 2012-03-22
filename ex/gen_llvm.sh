#!/bin/bash

name=${1%.c}

echo "Compilation de $1 ..."
llvm-gcc -c -emit-llvm ${name}.c

opt -f -mem2reg -o  ${name}_opt.o ${name}.o


llvm-dis -f ${name}_opt.o

# on supprime les fichiers intermediaires
rm ${name}.o 

echo "terminé"
# Cela genere un fichier ${name}_opt.o.ll
