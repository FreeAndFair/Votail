@ECHO OFF
rem  @(#)$Date: 2004/01/27 03:18:38 $
rem Configuration parameters for JML batch files
rem AUTHOR: Johan Stuyts

rem If needed, change the following configuration parameters for your system

set JUNITDIR=c:\JUnit
set JMLDIR=c:\JML

rem The following is needed because jmldoc only works with the
rem JDK 1.4.1 or 1.4.2 tools.jar.
rem Edit the path so that it points to tools.jar in your JDK 1.4 install.
set JDKTOOLS=c:\jdk1.4\lib\tools.jar

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
