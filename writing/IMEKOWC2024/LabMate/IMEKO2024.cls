% Created by A B Forbes, NPL, based on the 2015 IMEKO.cls file

%Class for IMEKO World Congress

\message{*****Class for the IMEKO World Congress *****}
\message{(c) Vladimir Horyna, inspired by templates for Poster2014 (Frantisek Rund)\dots}
\NeedsTeXFormat{LaTeX2e}%[1996/12/01]
\ProvidesClass{IMEKO}
\RequirePackage{graphicx}
\RequirePackage{times}
\RequirePackage{fancyhdr}
\LoadClass[twocolumn,a4paper,twoside,10pt]{article}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\hoffset=-28mm % 
\voffset=-21.5mm % 
\oddsidemargin=22.6mm %
\evensidemargin=17.6mm % 
\topmargin=10mm % 
\textwidth=175mm %
\textheight=241mm % 
\headsep=9mm 
\parindent=7.5mm %
%\parskip=2mm %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\widowpenalty 10000
\clubpenalty 10000
\displaywidowpenalty 10000

\def\@seccntformat#1{\csname the#1\endcsname.\space}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\headerfont}{\sffamily\selectfont}
\newcommand{\abstractfont}{\fontsize{10pt}{1}\selectfont}
\newcommand{\titlefont}{\fontseries{b}\fontshape{n}\fontsize{14pt}{14pt}\selectfont}
\newcommand{\titleautfont}{\large\itshape\selectfont}
\newcommand{\titleaddfont}{\normalsize\selectfont}
\newcommand{\sectionfont}{\fontsize{10pt}{1}\fontseries{b}\selectfont\center}
\newcommand{\subsectionfont}{\fontsize{10pt}{1}\fontseries{b}\selectfont\itshape}
\newcommand{\captionfont}{\small\selectfont}
\newcommand{\tablefont}{\small\bfseries\sffamily\selectfont}
\newcommand{\reffont}{\small\selectfont}
\pagenumbering{gobble}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\columnsep=6mm
\emergencystretch=4em
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\fancypagestyle{first}{
\fancyhead[LO]{}
\fancyhead[CO]{\small{XXIV IMEKO World Congress ``Think Metrology''\\ August 26 - 29, 2024, Hamburg, Germany\\[-10mm]}}
\fancyhead[RO]{}
\fancyhead[LE]{}
\fancyhead[CE]{}
\fancyhead[RE]{}
}
\fancypagestyle{other}{
\fancyhead[LO]{}
\fancyhead[CO]{}
\fancyhead[RO]{}
\fancyhead[LE]{}
\fancyhead[CE]{}
\fancyhead[RE]{}
}
\renewcommand{\headrulewidth}{0pt}
%\newcommand*\headtitle[1]{\fancyhead[RE]{\headerfont {#1} \\ [-3mm]}}
\pagestyle{other}

%%%%%%title

\newcommand*\affiliation[1]{\def\@affiliation{#1}}
\newcommand*\affiliationmark[1]{\textsuperscript{#1}}
%\newcommand*\email[1]{\def\em@il{#1}}
\title{TITLE here}
\author{AUTHOR here}
\affiliation{AFFILIATION here}
%\email{email}

\newbox\temp@box

\renewcommand\maketitle{%
  \par
  \begingroup
    \gdef\@thanks{}%
    \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
    \def\@makefnmark
        {\rlap{\@textsuperscript{\normalfont\@thefnmark}}}%
    \long\def\@makefntext##1{\parindent 1em\noindent
            \normalfont\@thefnmark~##1}%
    \twocolumn[\@maketitle]%
    \@thanks
  \endgroup
  \setcounter{footnote}{0}%
  \setcounter{section}{0}%
  \thispagestyle{first}%
}
\renewcommand\@maketitle{%
  \newpage
  \null
  \begin{center}% 
  \vspace*{-1.5mm}
%  \let \footnote \thanks
  {\titlefont 
	\fontdimen2\font=2\fontdimen2\font
  \@title \par}
  \vspace{2em}
  {
   \titleautfont
    \ignorespaces
   \@author
   \par}%
\vspace{1em}
  {
   \titleaddfont
   \ignorespaces
   \@affiliation\par}%
   
  %{\titleaddfont
  %\em@il\par}%
  \vspace{2em}
  %\unhbox\temp@box
    \end{center}%
  \par
  \vspace{-5mm}
  }
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\renewenvironment{abstract}
  {\parindent=0pt%
   \abstractfont%\
  \setlength{\baselineskip}{2.8ex}
  \textup{\textbf{\textsl{Abstract} -}}
}
  {}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\addtocounter{secnumdepth}{-1}
\renewcommand\section{\@startsection {section}{1}{\z@}%
                                   {5mm}
				   {3mm}
                                   {
				    \sectionfont
				   }}
\renewcommand\subsection{\@startsection{subsection}{2}{\z@}%
				    {4mm}
				    {0.8mm}
                                    {
				    \subsectionfont
				    }}
\renewcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
				    {4mm}
				    {0.8mm}
				    {\normalsize\fontseries{b}\selectfont}
				    }

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewenvironment{thebibliography}[1]
     {\section*{REFERENCES}%      
      \reffont
      \list{\@biblabel{\@arabic\c@enumiv}}%
           {\settowidth\labelwidth{\@biblabel{#1}}%
            \leftmargin\labelwidth
            \itemsep\z@
            \advance\leftmargin\labelsep
            \@openbib@code
            \usecounter{enumiv}%
            \let\p@enumiv\@empty
            \renewcommand\theenumiv{\@arabic\c@enumiv}}%
      \sloppy
\renewcommand\baselinestretch{0.9}%
      \clubpenalty4000
      \@clubpenalty \clubpenalty
      \widowpenalty4000%
      \sfcode`\.\@m}
     {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
      \endlist} 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\newenvironment{authorcv}[1]{\parindent=0pt
\begin{center}\section*{About Authors\dots}\end{center}
\textbf{#1}}{}				    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%\noindent
%\newenvironment{keywords}{\section*{Keywords} 
%\hspace{0.75cm}\begin{minipage}[t]{22em}}{\end{minipage}}
\newenvironment{keywords}{\parindent=0pt
\bigskip
\textsl{\textbf{Keywords:}}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand{\belowcaptionskip}{0em}

\long\def\@makecaption#1#2{%
  \vskip\abovecaptionskip
  \begin{center}
{\parbox[t]{1.5cm}{\hspace{5mm}{\captionfont \bfseries #1.}}%
\parbox[t]{.75\columnwidth}{ \captionfont {#2}}}%
    \end{center}
  \vskip\belowcaptionskip\vspace{-0.8cm}
  } 

\newcommand\captionwide[1]{
\vskip\abovecaptionskip
  \begin{center}
{\parbox[t]{1.5cm}{\hspace{5mm}{\refstepcounter{figure} \captionfont \bfseries \figurename \thefigure.}}%
\parbox[t]{.8\textwidth}{ \captionfont {#1}}}%
    \end{center}
  \vskip\belowcaptionskip\vspace{-0.8cm}
  } 
%\small\refstepcounter{figure}%
%   \centering\figurename\ \thefigure :\ #1} 
%\long\def\@makecaption#1#2{%
%  \vskip\abovecaptionskip
%  \begin{center}
%{\parbox[t]{1.5cm}{\hspace{5mm}#1.}\parbox[t]{63mm}{ \captionfont {#2}}}
%    \end{center}
%  \vskip\belowcaptionskip\vspace{-0.8cm}
%  } 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\pagestyle{fancy}
\setcounter{tocdepth}{0}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand{\figurename}{{Fig.}}
%\renewcommand{\thefigure}{{\captionfont\bfseries \arabic{figure}}}
\renewcommand{\tablename}{{Table}}
%\renewcommand{\thetable}{{\captionfont\bfseries\arabic{table}}}

