#!/bin/sh
# @(#) $Id: collect-grammar.sh,v 1.4 2004/12/29 15:59:48 leavens Exp $

sed -e '1,/^\@chapter Lexical Conventions/d' "$@" |
 sed -n -e '
	/^\@chapter/p
	/^\@iftex/p
	/^\@end iftex/p
	/^\@ifinfo/p
	/^\@end ifinfo/p
	/^\@var.*::=/p
	/^      *\[ /p
	/^      *\@var/p
	/^ *| /p' |
 awk 'BEGIN {print "@appendixsec Lexical Conventions\n@display\n"}
      {if ($1 == "@chapter") {
           $1 = "@appendixsec";
	   print "@end display\n";
	   print;
	   print "@display\n"; 
       }
       else
	   print 
      }
      END {print "@end display\n"}
     ' | sed -e '/^\@appendixsec Grammar Summary/,$d'
