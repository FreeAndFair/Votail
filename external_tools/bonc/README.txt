Copyright (c) 2007, Fintan Fairmichael, University College Dublin
All rights reserved.

This file is the readme that accompanies the bonc tool.

Contents:

  1. Description
  2. Requirements
  3. Using the tool
     3.1 Commandline options
     3.2 Printing
         3.2.1 Class dictionary generation
         3.2.2 Pretty-printing
         3.2.3 HTML printing
         3.2.4 Graphs
  4. Source
  5. Bug Reports


1. DESCRIPTION
==============

  Bonc is a parser and typechecker for the Business Object Notation (BON).
  
  This tool reads one or more files and/or input from standard input in the BON
  textual format, parses all this input and typechecks it. A number of options
  are available to modify the typechecking that is performed. Pretty-printing
  input is also available, as well as creating fancy html pages for informal 
  charts.

  More information can be found on BON at the website 
  http://www.bon-method.com/, and by reading the book "Seamless object-oriented
  software architecture: analysis and design of reliable systems" which is 
  freely available on the site since it is out of print.


2. REQUIREMENTS
===============

  Since this tool has been written in Java, the only real requirements are a
  system that has a Java Runtime Environment (JRE) capable of running Java
  version 5 bytecode. The tool has been developed and tested primarily using
  Sun's official releases of Java, version 1.5/5.0 and 1.6/6.0. Whilst it might
  work with some of the alternative JRE implementations that support Java 5
  code, it has not been tested on these at all.

  The tool utilises the ANTLR parser generator, and releases of the tool
  include the appropriate ANTLR runtime as well as the StringTemplate library.
  ANTLR and StringTemplate are Copyright (c) 2003-2007, Terence Parr, under the
  BSD licence.

3. USING THE TOOL
===================

  Note that in this section we assume that you have successfully completed an 
  installation procedure as described in INSTALLATION.txt. We will use the tool
  as if it is on the path (i.e. simply "bonc"), but you can substitute for 
  ./bonc, /path/to/bonc, or similar, if necessary.

  Firstly, to see the available options type:
    bonc --help

  Standard usage is:
    bonc [options] file1 [file2 ...]

  For example:
    bonc file1

  The tool will then parse and typecheck the input, and report any errors. If
  the tool does not output any messages, then no errors were found.

  You can read from standard input by adding the option "-" (single-dash). This
  can be given as a file, or an option. For example, the following three
  commands will all produce the same result:
    bonc - file1 file2
    bonc file1 - file2
    bonc file1 file2 -
    
3.1 Commandline Options
-----------------------

  The tool recognises the following options:

  -                             Read from standard input.
  -d, --debug                   Print debugging output.
  -f, -formal, --formal         Only check formal charts.
  -g, -graph, --graph=TYPE      Display the chosen graph type. ICG for
                                informal clustering graph, IIG for informal
                                inheritance graph.
  -h, --help                    Print this help message
  -i, -informal, --informal     Only check informal charts.
  -nc, --no-consistency         Do not check consistency between levels.
  -ngcd, --no-gen-class-dic     Do not generate the class dictionary when
                                printing.
  -ntc, --no-typecheck          Do not typecheck the input.
  -p, -print, --print=TYPE      Print the parsed input in the given format.
                                TXT for plain-text, HTML for html generation
                                of informal charts, DIC to generate the class
                                dictionary, IIG for the informal class
                                inheritance graph. See the manpage or README.
                                txt for more information and a list of all
                                printing options.
  -po, --print-output=FILE      Print output to the given file instead of to
                                stdout.
  -pp, --pretty-print           Pretty-print the parsed input. This is
                                equivalent to -p=TXT.
  -t, -time, --time             Print timing information.
  -v, --version                 Print BONc version and exit.

3.2 Printing
------------

  The printing framework allows parsed source to be printed to a variety of 
  formats. The general syntax for printing to standard out is:
    bonc -p <print-type> file1 [file2 ...]

  In the above "<print-type>" is one of the allowed printing types. These are
  detailed below.

  Alternatively, to print the output to a file, use this syntax:
    bonc -p <print-type> -po <output-file> file1 [file2 ...]

  "<output-file>" should be the path to the file you wish to print to. Note
  that if the path is to an existing file, it will be overwritten.

3.2.1 Class dictionary generation

  It is possible to automatically generate a class dictionary for the given 
  input. In order to print the generated textual BON to stdout(1), or to a 
  file(2) use the following:
    (1) bonc -p dic file1 [file2 ...]
    (2) bonc -p dic -po <output-file> file1 [file2 ...]

  Class dictionaries can also be computed on the fly and included when 
  performing other printing operations. In fact, this is the default behaviour.
  To prevent automatic class dictionary generation, provide the option
  "-ngcd"/"--no-gen-class-dic". For example:
    bonc -ngcd -p <print-type> [-po <output-file>] file1 [file2 ...]

3.2.2 Pretty-printing

  This is the most basic printing type. The parsed text will be pretty-printed
  in plain text. In order to pretty-print to stdout(1), or to a file(2) use the
  following:
    (1) bonc -p txt file1 [file2 ...]
    (2) bonc -p txt -po <output-file> file1 [file2 ...]

  The option "-pp"/"--pretty-print" is a synonym for "-p txt", thus the below 
  is equivalent to the above, and will pretty-print to stdout(1), or to a 
  file(2):
    (1) bonc -pp file1 [file2 ...]
    (2) bonc -pp -po <output-file> file1 [file2 ...]

3.2.3 HTML printing

  This printing option generates a fancy XHTML version of the informal charts
  included in the input. It will generate a single HTML page, with the charts
  styled to emulate those given in the BON book. To generate the HTML to 
  stdout(1), or to a file(2) use the following:
    (1) bonc -p html file1 [file2 ...]
    (2) bonc -p html -po <output-file> file1 [file2 ...]

3.2.3 Graph printing

  It is possible to create graphs representing the clustering and inheritance
  relationships in the given BON source. For the chosen graph type, the output
  will be in the DOT language (see http://www.graphviz.org/doc/info/lang.html).
  
  The available graph printing options currently are:
    (1) icg - Informal cluster graph
              A graph showing the cluster hierarchy from the system cluster
              down to the leaf cluters. This graph will also show which 
              cluster(s) each class is contained in.
    (2) iig - Informal inheritance graph
              A graph showing the class hierarchy for the given system.

  An example of printing one of these graphs (subsititute print-type for other 
  graph types):
    bonc -i -p icg -po icg.dot file1 [file2 ...]

  There are numerous pieces of software available for viewing/working with .dot
  files. Some of the most popular of these are available from Graphviz 
  (http://www.graphviz.org/).

  For those working on Ubuntu, simply install the "graphviz" package (should be
  similarly available on other linux flavours. For an example of usage, assume
  we have created a graph "graph.dot". We can use the graphviz to convert to 
  svg:
    dot -Tsvg -o graph.svg graph.dot

  The above will create an svg file "graph.svg" that can be viewed/used as you 
  wish. The dot command can also output to postscript, png, and several other 
  types. See the graphviz documentation for more information (or "man dot").  


4. SOURCE
=========

  All source for this tool is available from the subversion repository. The
  repository is located at: 
    https://mobius.ucd.ie/repos/src/bon/bonc

  You can browse the source in your web browser:
    https://mobius.ucd.ie/browser/src/bon

   For more information on how to download and build this software, please read
   INSTALLATION.txt.


5. BUG REPORTS
==============

  Bug tracking is handled on the Mobius Trac (https://mobius.ucd.ie/). 

  To create a new ticket either complete the form at:
    https://mobius.ucd.ie/newticket?owner=fintan&component=BON
  or send an email to:
    bon-ticket@mobius.ucd.ie

  Please include the following details (where possible):
  - The commandline arguments with which you invoked the tool 
    (e.g. "bonc -i test.bon").
  - The operating system and java version you are using.
  - Any input files used to recreate the bug.  
  - The output generated when you detected the bug.

  Filing bugs will help to improve this software, so if you notice something
  amiss please do report it!

