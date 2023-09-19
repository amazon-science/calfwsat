#!/bin/sh

DIR="$(dirname "${BASH_SOURCE[0]}")"
DIR="$(realpath "${DIR}")"

FORMULAS=$1
PARALLELCNT=$2
COUNT=$3
OUTNAME=$4

rm -r logs
mkdir logs

rm tmp_num.txt
touch tmp_num.txt
for i in $(seq 1 $COUNT); do echo $i >> tmp_num.txt; done


cat tmp_num.txt | xargs -L1 -P$PARALLELCNT sh $DIR/run-config.sh $FORMULAS

cat logs/* > $OUTNAME

rm tmp_num.txt 
