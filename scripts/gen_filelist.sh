#!/bin/sh

PATHCMD=realpath
if [ `uname -o` == "Cygwin" ]; then
   PATHCMD="cygpath -w -a"
fi

for f in $@
do
    for l in `cat $f`
    do
        ${PATHCMD} -w -a $l
    done
done
