#!/bin/sh

DIR="$(dirname "${BASH_SOURCE[0]}")"
DIR="$(realpath "${DIR}")"

COUNT=$1

for i in $(seq 1 $COUNT); 
do 
  rm -r $i-temp
done

rm -r logs