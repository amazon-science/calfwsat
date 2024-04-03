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
cd ../

else

# build solver
cd solver
./configure.sh && make 
cd ../

fi

# build checker
cd tools/check-sat
g++ --std=c++11 check-sat.cpp -o check-sat
mv check-sat ../../
