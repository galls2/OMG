#!/bin/bash
pyinstaller --clean --noupx -F main.py
nohup ./dist/main `cat runconfig.omg` &
