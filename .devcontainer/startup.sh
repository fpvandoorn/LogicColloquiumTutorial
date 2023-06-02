#!/usr/bin/env bash
echo "Downloading the Lean 4 mathematical library..."
lake exe cache get!
lake build +LCTutorial.Library.Basic
echo "Finished setup! Open a file using the Explorer in the top-left of your screen."