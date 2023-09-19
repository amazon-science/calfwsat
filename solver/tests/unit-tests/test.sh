# build
gcc --std=c99 -I../../../solver propagation.c -o propagation

./propagation

rm propagation