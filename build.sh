#!/bin/sh

DEBUGGING=0
if [ $# -eq 1 ]
  then
  DEBUGGING=$1
fi

if [ $DEBUGGING -gt 0 ]
then 


# build solver
cd solver
./configure.sh -g && make
cp yalsat ../ddfw-card-sat
cd ../

else

# build solver
cd solver
./configure.sh && make 
cp yalsat ../ddfw-card-sat
cd ../

fi

# build checker
cd tools/check-sat
g++ --std=c++11 check-sat.cpp -o check-sat
mv check-sat ../../
