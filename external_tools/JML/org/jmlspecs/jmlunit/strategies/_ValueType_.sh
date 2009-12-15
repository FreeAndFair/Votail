#! /bin/sh
# @(#)$Id: _ValueType_.sh,v 1.7 2004/01/26 07:22:28 leavens Exp $

# Copyright (C) 1998, 1999, 2002 Iowa State University

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

# return code
ret=0

for T in byte short int long float double char boolean
do
  # set capitalized version of the type name, CAPT
  case "$T" in
      byte)
	  CAPT=Byte
	  ;;
      short)
	  CAPT=Short
	  ;;
      int)
	  CAPT=Int
	  ;;
      long)
	  CAPT=Long
	  ;;
      float)
	  CAPT=Float
	  ;;
      double)
	  CAPT=Double
	  ;;
      char)
	  CAPT=Char
	  ;;
      boolean)
	  CAPT=Boolean
	  ;;
      *)
	  echo "Missing basic value type in setting CAPT" 2>&1
	  exit 2
	  ;;
  esac

  # set java.lang version of the type name, LANGTYPE
  case "$T" in
      int)
	  LANGTYPE=Integer
	  ;;
      char)
	  LANGTYPE=Character
	  ;;
      *)
	  LANGTYPE="$CAPT"
	  ;;
  esac

  # set the NUMERIC flag
  case "$CAPT" in
      Char|Boolean)
	  NUMERIC=false
	  ;;
      *)
	  NUMERIC=true
	  ;;
  esac

  # set the DEFAULTVALUE flag
  case "$CAPT" in
      Boolean)
	  DEFAULTVALUE='false'
	  ;;
      *)
	  DEFAULTVALUE='0'
	  ;;
  esac

  # create all the files
  for f in ArrayIterator AbstractIterator Iterator \
           AbstractStrategy ExtensibleStrategy StrategyType \
           CompositeStrategy CompositeIterator ExtensibleStrategyDecorator \
           AbstractFilteringIteratorDecorator \
           AbstractFilteringStrategyDecorator \
           StrategyTypeTest \
           NonNegativeIteratorDecorator \
           NonNegativeStrategyDecorator
  do
    if test "$NUMERIC" = true -o \
            \( "$f" '!=' "NonNegativeIteratorDecorator" \
              -a "$f" '!=' "NonNegativeStrategyDecorator" \
              -a "$f" '!=' "StrategyTypeTest" \
	    \)
    then
	rm -f "${CAPT}${f}.java"
	sed -e 's/_ValueType_/'"$T"'/g
	    s/_ValueTypeCap_/'"$CAPT"'/g
            s/_LangType_/'"$LANGTYPE"'/g
            s/_ValueTypeDefault_/'"$DEFAULTVALUE"'/g
           ' "_ValueType_${f}.java-generic" > "${CAPT}${f}.java" || ret=1
	chmod a-w "${CAPT}${f}.java" || ret=1
    fi
  done
done

exit "$ret"
