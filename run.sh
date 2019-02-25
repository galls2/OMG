#!/bin/bash

rm logs/*
rm nohup.out

git clone https://github.com/galls2/OMG

nohup python OMG/main.py no-qe
