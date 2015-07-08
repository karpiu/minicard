#!/bin/sh

CPU_LIMIT=300
MINICARD_PATH=~/latex/minicard
LINGELING_PATH=~/lingeling
if [ $# -eq 0 ] ; then ENCODINGS="7 8 9"; else ENCODINGS="$@"; fi

# ============= minicard_encoding  =========
if [ -f me-results ] ; then rm me-results; fi
for f in *cnfp.gz; do cp $f /tmp/; for e in ${ENCODINGS}; do echo === $f encoding=$e ===;  ${MINICARD_PATH}/minicard_encodings/minicard_encodings_static -encode-type=$e -verb=1 -dt-clause -warn=0  -cpu-lim=${CPU_LIMIT} /tmp/$f | grep "Number\|CPU\|SATISF\|INDETER">>me-results; done; rm /tmp/$f; done

# == CNF generation by minicard_encoding  ===
for f in *.cnfp.gz; do for e in ${ENCODINGS} ; do if [ ! -f `basename $f .cnfp`-${e}.cnf.gz ]; then echo === $f encoding=$e ===;  ${MINICARD_PATH}/minicard_encodings/minicard_encodings_static -encode-type=$e -dt-clause -warn=0  -verb=0  -convert-to=1 $f >`basename $f .cnfp`-${e}.cnf; gzip `basename $f .cnfp`-${e}.cnf; fi;  done

# ============= lingeling ===================
if [ -f ll-results ] ; then rm ll-results; fi
for e in ${ENCODINGS} ; do for f in test*-${e}*; do echo === $f ===; cp $f /tmp/; ${LINGELING_PATH}/lingeling -t ${CPU_LIMIT} -n -f /tmp/$f |grep "headerc\|100%\|SATISF\|reached"; rm /tmp/$f; done >>ll-results; done

# ============= minicard  ===================
if [ -f mc-results ] ; then rm mc-results; fi
for e in ${ENCODINGS} ; do for f in test*-${e}*; do echo === $f ===; cp $f /tmp; ${MINICARD_PATH}/minicard/minicard_static -cpu-lim=${CPU_LIMIT} /tmp/$f |grep "Number\|CPU\|SATIS\|INDETERF"; rm /tmp/$f; done >>mc-results; done

