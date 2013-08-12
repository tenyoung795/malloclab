#!/bin/bash
if [ $1 ]
then
    cp mm-$1.c mm.c
fi
make $2

