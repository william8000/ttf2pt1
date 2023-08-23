#!/bin/sh
# nightly_build.sh -- build ttf2pt1 from git

cd "$(dirname "$0")" || { echo "$0: Error: Initial cd $(dirname "$0") failed" ; exit 1 ; }

rm -f nightly_build.log

(
 echo "Starting nightly_build $* at $(date) in $(pwd)"
 cd ttf2pt1 && make "$@" all
) 2>&1 | tee nightly_build.log
