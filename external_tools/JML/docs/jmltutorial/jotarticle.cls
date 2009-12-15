% file jotarticle.cls
% Susanne Cech, Departement Informatik, ETH Zurich
% 30 April 2002, version 1.0
% 26 June 2002, version 1.1
% 21 Oct 2002
% 2003-02-27: r
%---------------------------------------------------------------------
% IDENTIFICATION PART
%---------------------------------------------------------------------
\NeedsTeXFormat{LaTeX2e}
%\ProvidesClass{jotarticle}[2002/04/30 1.0 (SU)]
%\ProvidesClass{jotarticle}[2002/06/26 1.1 (SU)]
\ProvidesClass{jotarticle}[2003/01/21 1.2 (SU)]
\typeout{(c) 2002 Susanne Cech, ETH Zurich, Switzerland}
\typeout{ }
%---------------------------------------------------------------------
% DECLARATION OF OPTIONS
%---------------------------------------------------------------------
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
%---------------------------------------------------------------------
% EXECUTION OF OPTIONS
%---------------------------------------------------------------------
\ProcessOptions
%---------------------------------------------------------------------
% SPECIAL CLASS FILE COMMANDS
%---------------------------------------------------------------------
\LoadClass[12pt,a4paper,notitlepage,twoside]{article}
%---------------------------------------------------------------------
% PACKAGE LOADING
%---------------------------------------------------------------------
\RequirePackage[dvipdf]{graphicx}
\RequirePackage{color}
\RequirePackage{alltt}
\RequirePackage{ifthen}
\RequirePackage[bookmarks=false, colorlinks=true, pdfstartview=FitV, 
           linkcolor=black, citecolor=black, urlcolor=blue]{hyperref}
%---------------------------------------------------------------------
% SPECIAL COMMANDS FOR CLASS FILES
%---------------------------------------------------------------------
\AtBeginDocument{\maketitle}
%---------------------------------------------------------------------


%=====================================================================
% STUFF
%=====================================================================

%---------------------------------------------------------------------
% DELCARE VARIOUS LENGTHS, COUNTERS
%---------------------------------------------------------------------
\setlength{\parskip}{0.2cm}
\setcounter{secnumdepth}{1}
\graphicspath{{png/}}
\newlength{\jotpagewidth}\setlength{\jotpagewidth}{150mm}
%---------------------------------------------------------------------
% PAGE SETTINGS
%---------------------------------------------------------------------
% horizontal
\setlength{\hoffset}{0pt}
\setlength{\marginparwidth}{0pt}
\setlength{\evensidemargin}{6.3mm} 
\setlength{\oddsidemargin}{\evensidemargin}
\setlength{\textwidth}{\the\jotpagewidth}
% vertical
\addtolength{\topmargin}{-15mm}
\addtolength{\textheight}{20mm}
%---------------------------------------------------------------------
% DECLARE COLORS
%---------------------------------------------------------------------
\definecolor{darkblue}{rgb}{0,0.1992,0.59765}     %%   0  51 153 
\definecolor{darkgreen}{rgb}{0,0.59765,0.1992}    %%   0 153  51 
\definecolor{lightblue}{rgb}{0.23,0.21,0.90}      %%  61  55 232
%---------------------------------------------------------------------
% DECLARE FONTS
%---------------------------------------------------------------------
\newcommand{\FontSection}{\color{darkgreen}\large\sf\uppercase}
\newcommand{\FontSubsection}{\color{darkblue}\large\sf}
\newcommand{\FontSubsubsection}{\color{black}\sf}
\newcommand{\textssit}[1]{\textsf{\textit{#1}}}
%---------------------------------------------------------------------
% Source code font 
\renewcommand{\verbatim@font}{\normalfont\ttfamily\color{lightblue}}
%---------------------------------------------------------------------
\renewcommand{\and}{ \\ }
%---------------------------------------------------------------------
% Draw a rule of width \jotpagewidth
\newcommand{\pagewidthrule}{\rule{\the\jotpagewidth}{0.5pt}}
%---------------------------------------------------------------------


%---------------------------------------------------------------------
\makeatletter
%=====================================================================
% CONFIGURATION COMMANDS
%=====================================================================
\newcommand{\jotvolume}[1]{\renewcommand{\JOT@volume}{#1}}
\newcommand{\jotnumber}[1]{\renewcommand{\JOT@number}{#1}}
\newcommand{\jotmonth}[1]{\renewcommand{\JOT@month}{#1}}
\newcommand{\jotyear}[1]{\renewcommand{\JOT@year}{#1}}
\newcommand{\filename}[1]{\renewcommand{\JOT@filename}{#1}}
\newcommand{\jotmonths}[1]{\renewcommand{\JOT@months}{#1}}
\newcommand{\authornames}[1]{\renewcommand{\JOT@authornames}{#1}}
%---------------------------------------------------------------------
% Starting page number of the article/column
%---------------------------------------------------------------------
\newcommand{\firstpage}[1]{\renewcommand{\JOT@firstpage}{#1}}
%---------------------------------------------------------------------
% Lasts page number of the article/column
%---------------------------------------------------------------------
\newcommand{\lastpage}[1]{\renewcommand{\JOT@lastpage}{#1}}
%---------------------------------------------------------------------
% Type of paper, i.e. article, column, book review, product review
\newcommand{\papertype}[1]{\renewcommand{\JOT@papertype}{#1}}
%---------------------------------------------------------------------
\newcommand{\howtocite}[1]{\renewcommand{\JOT@howtocite}{#1}}
%---------------------------------------------------------------------
\renewcommand{\title}[2][xx]{%
\renewcommand{\JOT@pagetitle}{#2}
\ifthenelse{\equal{#1}{xx}}{
\renewcommand{\JOT@headtitle}{#2}} %then
{\renewcommand{\JOT@headtitle}{#1}} %else
}
%---------------------------------------------------------------------
% Configuration is only possible before \begin{document}
%---------------------------------------------------------------------
\@onlypreamble{\howtocite}
\@onlypreamble{\firstpage}
\@onlypreamble{\lastpage}
\@onlypreamble{\papertype}
\@onlypreamble{\filename}
\@onlypreamble{\jotvolume}
\@onlypreamble{\jotnumber}
\@onlypreamble{\jotmonth}
\@onlypreamble{\jotmonths}
\@onlypreamble{\jotyear}
\@onlypreamble{\authornames}
%---------------------------------------------------------------------


%=====================================================================
% USER COMMANDS 
%=====================================================================

%---------------------------------------------------------------------
% Produce a HTML-link
%---------------------------------------------------------------------
\newcommand{\htmllink}[1]{\href{#1}{#1}}
\newcommand{\maillink}[1]{\href{mailto:#1}{#1}}
%---------------------------------------------------------------------
% Write source code
%---------------------------------------------------------------------
\newcommand{\code}[1]{\texttt{\textcolor{lightblue}{#1}}}
\let\oldtt\tt
\renewcommand{\tt}{\color{lightblue}\oldtt}
%---------------------------------------------------------------------
\newcommand{\abouttheauthor}[3][no]{\ \\
\ifthenelse{\equal{#1}{no}}{\textbf{#2} #3}
{\hbox{\includegraphics[width=26mm, height=26mm]{#1}%
      \hspace{5mm}%
      \parbox[b]{121.5mm}{\textbf{#2} #3}}
}}
%---------------------------------------------------------------------



%=====================================================================
% INTERNAL COMMANDS
%=====================================================================

%---------------------------------------------------------------------
\newcommand{\jottitle}{\textsf{\uppercase{Journal of Object Technology}}}
\newcommand{\jotpage}{\textsf{\textbf{\thepage}}}
\newcommand{\jotno}{\textsf{\uppercase{Vol \JOT@volume, no. \JOT@number}}}
%---------------------------------------------------------------------
\newcommand{\JOT@volume}{0}
\newcommand{\JOT@number}{0}
\newcommand{\JOT@month}{}
\newcommand{\JOT@months}{}
\newcommand{\JOT@year}{Z}
\newcommand{\JOT@filename}{}
\newcommand{\JOT@headtitle}{}
\newcommand{\JOT@pagetitle}{}
\newcommand{\JOT@firstpage}{1}
\newcommand{\JOT@lastpage}{99}
\newcommand{\JOT@papertype}{article}
\newcommand{\JOT@authornames}{}
%---------------------------------------------------------------------
\renewcommand{\JOT@months}{%
\ifthenelse{\JOT@number = 1}{January--February}{}%
\ifthenelse{\JOT@number = 2}{March--Aprile}{}%
\ifthenelse{\JOT@number = 3}{May--June}{}%
\ifthenelse{\JOT@number = 4}{July--August}{}%
\ifthenelse{\JOT@number = 5}{September--October}{}%
\ifthenelse{\JOT@number = 6}{November--December}{}%
\ifthenelse{\JOT@number < 1}{}{}%
}
%---------------------------------------------------------------------
\newcommand{\JOT@howtocite}{\JOT@authornames: \textit{\JOT@headtitle}, 
in Journal of Object Technology, vol. \JOT@volume, no. \JOT@number, 
\JOT@months~\JOT@year, pages \JOT@firstpage--\JOT@lastpage, \par
\href{http://www.jot.fm/issues/issues_\JOT@year_\JOT@month/\JOT@filename}%
{http://www.jot.fm/issues/issues\_\JOT@year\_\JOT@month/\JOT@filename}}
%---------------------------------------------------------------------


%=====================================================================
% OVERALL DOCUMENT STYLE 
%=====================================================================

%---------------------------------------------------------------------
% SECTION LAYOUT
%---------------------------------------------------------------------
\renewcommand{\sectionmark}[1]{\markboth{\uppercase{\thesection~~#1}}{}}
\renewcommand{\section}{\@startsection{section}{1}{\z@}%
                      {-3.5ex \@plus -1ex \@minus -.2ex}%
                      {2.3ex \@plus.2ex}%
                      {\hspace{-6mm}\reset@font\FontSection}}
%---------------------------------------------------------------------
% SUBSECTION LAYOUT
% \textcolor{darkblue}  no uppercasse
%---------------------------------------------------------------------
\renewcommand{\subsection}{\@startsection{subsection}{2}{\z@}%
                      {-3.25ex\@plus -1ex \@minus -.2ex}%
                      {1.5ex \@plus .2ex}%
                      {\hspace{-6mm}\reset@font\FontSubsection}}
%---------------------------------------------------------------------
% SUBSUBSECTION LAYOUT
% \textcolor{black}  no uppercasse
%---------------------------------------------------------------------
\renewcommand{\subsubsection}{\@startsection{subsubsection}{3}{\z@}%
                      {-3.25ex\@plus -1ex \@minus -.2ex}%
                      {1.5ex \@plus .2ex}%
                      {\hspace{-6mm}\reset@font\FontSubsubsection}}
%---------------------------------------------------------------------
% PLAIN PAGESTYLE
%---------------------------------------------------------------------
\renewcommand{\ps@plain}{%
  \renewcommand{\@evenhead}{}
  \renewcommand{\@oddhead}{}
  \renewcommand{\@evenfoot}{}
  \renewcommand{\@oddfoot}{%
	\begin{sloppypar}
	\hspace{-1mm}
	\vbox{\vspace{8mm}\pagewidthrule\par
	\vspace{-5mm}%
	\begin{minipage}[t]{\the\jotpagewidth} \small\sf%
	Cite this \JOT@papertype~as follows:~\JOT@howtocite%
	\end{minipage}}%
	\end{sloppypar}
  }
}

%---------------------------------------------------------------------
% HEADINGS PAGESTYLE
%---------------------------------------------------------------------
\renewcommand{\ps@headings}{%
  \renewcommand{\@evenhead}{%  % left page
	\begin{sloppypar}
	\hspace{-32mm}%
	\raisebox{-25mm}[0pt][0pt]{\includegraphics{jotleft}} 
	\hspace{-11mm}\parbox[b]{\the\jotpagewidth}{\vspace{-5mm}
	\flushright\hfill\scriptsize\sf\MakeUppercase\JOT@headtitle\\
	\raisebox{2mm}[0pt][0pt]{\pagewidthrule}}
	\end{sloppypar}%
  }
  \renewcommand{\@oddhead}{% % right page
	\begin{sloppypar}%
	\hspace{140mm}\raisebox{-25mm}[0pt][0pt]{\includegraphics{jotright}}%
	\hspace{-181.5mm}\vbox{\scriptsize\sf\leftmark\hfill\\%
	\raisebox{2mm}[0pt][0pt]{\pagewidthrule}}%
	\end{sloppypar}%
  }
  \renewcommand{\@evenfoot}{\vbox{\pagewidthrule\\
	\scriptsize\jotpage\hfill\jottitle\hfill\jotno}}
  \renewcommand{\@oddfoot}{\vbox{\pagewidthrule\\
	\scriptsize\jotno\hfill\jottitle\hfill\jotpage}}}
%---------------------------------------------------------------------
% TITLEPAGE
%---------------------------------------------------------------------
\renewcommand{\@maketitle}{}
\renewcommand{\maketitle}{%
	\setcounter{page}{\JOT@firstpage}%
	\thispagestyle{plain}%
	\hspace{-43mm}%
	\raisebox{-40mm}[0pt][0pt]{\includegraphics{bigjot}}\par%
	\hspace{-6.5mm}%
	\raisebox{12mm}[0pt][0pt]{%
	\begin{minipage}{\the\jotpagewidth}%
	\begin{flushright}%
	\includegraphics[width=149mm]{title}\vspace{-2mm}
	\pagewidthrule\par
	\scriptsize\textsf{%
		Vol. \JOT@volume, No. \JOT@number, \JOT@months~\JOT@year}%
	\end{flushright}%
	\vspace{5mm}%
	\end{minipage}
        }
	{\color{darkblue}\huge\bf\sf\JOT@pagetitle}\par
	\vspace{6mm}\hspace{7mm}\parbox{136.5mm}{\textsf{\@author}}
	\pagestyle{headings}%
}
%---------------------------------------------------------------------
\renewenvironment{titlepage}{}{}
%---------------------------------------------------------------------
% ABSTRACT
%---------------------------------------------------------------------
\renewenvironment{abstract}{
	\sf\small
	\vspace{5mm}\hspace{7mm}%
	\begin{minipage}{136.5mm}%
}{%
	\end{minipage}%
}
%---------------------------------------------------------------------
% BIBLIOGRAPHY
%---------------------------------------------------------------------
\renewcommand{\refname}{REFERENCES}
%---------------------------------------------------------------------
% ABOUT THE AUTHOR
%---------------------------------------------------------------------
\newcommand{\abouttheauthors}{\section*{About the authors}}
%---------------------------------------------------------------------

%---------------------------------------------------------------------
%\AtEndDocument{\clearpage%
%  \addtocounter{page}{-1}%
%  \immediate\write\@auxout{%
%    \string\newlabel{lastpage}%
%    {{}{\thepage}}}%
%  \addtocounter{page}{1}%
%}
%---------------------------------------------------------------------


\makeatother
