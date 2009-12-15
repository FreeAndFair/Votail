#!/bin/bash
# @(#)$Id: insert.sh,v 1.1 2004/11/26 11:12:14 wdietl Exp $

# Copyright (C) 2004 Swiss Federal Institute of Technology Zuerich
# Copyright (C) 2004 Daniel Schregenberger
# License: GPL

# This file is part of JML

# JML is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2, or (at your option)
# any later version.

# JML is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with JML; see the file COPYING.  If not, write to
# the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

if [ -z "$1" ] ; then
	echo "usage: $0 insertID"
	exit
fi


ls *.1 | grep -v ".insert.1$" | while read file; do
	match=`grep "$1" "$file"`
	if [ -z "$match" ]; then
		continue
	fi
	
	let start_line=(`nl -b a "$file" | grep "START $1" | sed -e "s/ *\([0-9]*\).*/\1/"`)
	let end_line=(`nl -b a "$file" | grep "END $1" | sed -e "s/ *\([0-9]*\).*/\1/"`)

	if [ -z "$start_line" ] || [ -z "$end_line" ]; then
		echo "$file has invalid marks!"
		exit
	fi
	
	echo "inserting the contents of $1.insert.1 into $file ..."
	mv -f "$file" "$file.old"
	head -n $start_line "$file.old" > "$file"
	cat "$1.insert.1" >> "$file"
	tail -n +$end_line "$file.old" >> "$file"
	rm -f "$file.old"
done

