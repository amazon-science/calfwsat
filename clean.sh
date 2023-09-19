#!/bin/sh

# remove executable
rm ddfw-card-sat

# clean solver
cd solver
make clean
cd ../

# clean tools
# cd tools
rm check-sat
