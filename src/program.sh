#!/bin/bash


name=${1%.c}

dir=`dirname $1`
nam=`basename $1`
name=${nam%.c}

echo $dir
echo $nam
echo $name

echo "Compilation de $1 ..."
llvm-gcc -c -emit-llvm $dir/$nam

echo "Optimisation mem2reg ..."
opt -f -mem2reg -o  ${name}_opt.o ${name}.o

echo "Génération du fichier SMT-Lib ..."
./llvm2smt ${name}_opt.o

echo "Résolution avec z3 ..."

../z3/bin/z3 out.smt   

echo "terminé"
