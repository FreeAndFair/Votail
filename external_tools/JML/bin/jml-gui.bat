@ECHO OFF
rem  @(#)$Date: 2004/01/27 20:20:12 $
rem
rem jml -- script for invoking the JML checker
rem
rem SYNOPSIS: set CLASSPATH and run JML

call jmlenv.bat

rem save the old CLASSPATH
set OLDCLASSPATH=%CLASSPATH%
set CLASSPATH=.;%JMLDIR%\bin\jml-release.jar;%JMLDIR%\specs;%CLASSPATH%

set CMDLINE_ARGS=%1
:getargs
shift
if "%1"=="" goto endgetargs
set CMDLINE_ARGS=%CMDLINE_ARGS% %1
goto getargs
:endgetargs

rem You can use `java' or `jre -cp %CLASSPATH%' below
rem but these have to be in your PATH

java -mx128m org.jmlspecs.checker.JmlGUI %CMDLINE_ARGS%

rem restore the old CLASSPATH
set CLASSPATH=%OLDCLASSPATH%
set CMDLINE_ARGS=
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
