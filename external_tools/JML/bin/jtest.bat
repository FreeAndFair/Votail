@ECHO OFF
rem  @(#)$Date: 2004/01/27 03:18:38 $
rem
rem jtest -- generate and compile JML/JUnit tester and test case classes
rem
rem option --{javac|make} tool for compiling the generated tester class.
rem        --quiet quiet mode
rem
rem AUTHOR: Gary T. Leavens with help from Fermin R. Da Costa Gomez
rem and Johan Stuyts

call jmlenv.bat

rem save the old CLASSPATH
set OLDCLASSPATH=%CLASSPATH%
set CLASSPATH=%CLASSPATH%;%JUNITDIR%\junit.jar;%JMLDIR%\bin\jmlruntime.jar;%JMLDIR%\bin\jmljunitruntime.jar;%JMLDIR%\bin\jmlmodels.jar

set USAGE="Usage: jtest [--quiet] [--javac] file1.java [file2.java] ..."

set QUIET=false

:processoptions
if not "%1"=="--javac" goto endjavac2
:seenjavac
shift
set COMPILER=javac
goto processoptions
:endjavac2

if not "%1"=="-javac" goto endjavac1
goto seenjavac
:endjavac1

if not "%1"=="--make" goto endmake2
:seenmake
echo this version of jtest does not support make
shift
set COMPILER=make
goto processoptions
:endmake2

if not "%1"=="-make" goto endmake1
goto seenmake
:endmake1

if not "%1"=="--quiet" goto endquiet2
:seenquiet
shift
set QUIET=true
goto processoptions
:endquiet2

if not "%1"=="-quiet" goto endquiet1
goto seenquiet
:endquiet1

if not "%1"=="-Q" goto endquiet3
goto seenquiet
:endquiet3

if not "%1"=="" goto endargcheck
echo %USAGE%
set ERRORLEVEL=2
goto :done
:endargcheck

:getargs
if "%1"=="" goto endgetargs
if not "%QUIET%"=="true" goto noisycompile
call jmlc -Q %1
call jmlunit %1
goto argloopend

:noisycompile
echo jmlc %1
call jmlc %1
echo jmlunit %1
call jmlunit %1

:argloopend
shift
goto getargs
:endgetargs

rem don't know how to slice off parts of file names, so we just compile all
if not "%QUIET%"=="true" echo javac *_JML_Test*.java
call javac *_JML_Test*.java

:done

rem restore the old CLASSPATH
set CLASSPATH=%OLDCLASSPATH%
set OLDCLASSPATH=

rem Copyright (C) 2004 Iowa State University
rem
rem This file is part of JML
rem
rem JML is free software; you can redistribute it and/or modify
rem it under the terms of the GNU General Public License as published by
rem the Free Software Foundation; either version 2, or (at your option)
rem any later version.
rem
rem JML is distributed in the hope that it will be useful,
rem but WITHOUT ANY WARRANTY; without even the implied warranty of
rem MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
rem GNU General Public License for more details.
rem
rem You should have received a copy of the GNU General Public License
rem along with JML; see the file COPYING.  If not, write to
rem the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
