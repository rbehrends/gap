#/usr/bin/env bash

set -e

# This script should be run as ./run_gap.sh gap gapfile.g
gap="$1"
gfile="$2"

# It provides the following features:
# 1) Stop GAP from attaching to the terminal (which it will
#    use in the break loop)
# 2) Combine stderr and stdout
# 3) Rewrite the root of gap with the string GAPROOT,
#    so the output is usable on other machines
# 4) Set lower and upper memory limits, for consistency
GAPROOT=$(cd ../..; pwd)
( echo "LogTo(\"${outfile}.tmp\");" ; cat "$gfile" ; echo "QUIT;" ) |
    "$gap" -r -A -b -m 256m -o 512m -x 800 2>/dev/null >/dev/null
sed -E -e "s:${GAPROOT//:/\\:}:GAPROOT:g" -e "s;(GAPROOT(/[^/]+)+):[0-9]+;\1:LINE;g" < "${outfile}.tmp"
rm "${outfile}.tmp"
