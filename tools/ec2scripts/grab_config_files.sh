#!/bin/sh

DIR="$(dirname "${BASH_SOURCE[0]}")"
DIR="$(realpath "${DIR}")"

START=$1
END=$2
OUTNAME=$3

# rm $OUTNAME.sol
# touch $OUTNAME.sol
# rm $OUTNAME.log
# touch $OUTNAME.log

touch $OUTNAME

for i in $(seq $START $END); 
do 
  cat logs/$i.log >> $OUTNAME
done

