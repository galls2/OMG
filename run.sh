#!/bin/bash

rm logs/*
rm nohup.out

nohup python main.py no-qe
