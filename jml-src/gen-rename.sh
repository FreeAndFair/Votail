#!/bin/sh
for i in `find jml-src -name "*.gen"`; do mv $i `dirname $i`/`basename $i .gen`; done
