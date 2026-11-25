%% charlie.cls -- Charlie O'Neill's personal note/essay class.
%%
%% A quiet, single-column look: Palatino text, Computer Modern math,
%% Courier for code and URLs, standard article measure (345pt) on US letter,
%% no running heads, a bare page number in the footer.
%% Compiles with pdflatex on a standard TeX Live (Overleaf's default).
%%
%% Usage:   \documentclass{charlie}
%%          \documentclass[a4paper,11pt,spaced,colorlinks]{charlie}
%%
%% Class options (anything else is passed to article, e.g. 11pt, a4paper):
%%   spaced      blank line between paragraphs (indent kept)
%%   pazo        Palatino-matched math (mathpazo) instead of Computer Modern
%%   colorlinks  coloured link text instead of hyperref's on-screen boxes
%%   hidelinks   links with no colour and no boxes
%%   nomicrotype turn microtype off
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{charlie}[2026/11/20 v1.0 Charlie's personal template]

\newif\ifch@spaced
\newif\ifch@pazo
\newif\ifch@microtype \ch@microtypetrue
\def\ch@links{boxes}

\DeclareOption{spaced}{\ch@spacedtrue}
\DeclareOption{pazo}{\ch@pazotrue}
\DeclareOption{colorlinks}{\def\ch@links{color}}
\DeclareOption{hidelinks}{\def\ch@links{hide}}
\DeclareOption{nomicrotype}{\ch@microtypefalse}
\newif\ifch@paper
\DeclareOption*{%
  \edef\ch@tmp{\noexpand\in@{paper}{\CurrentOption}}\ch@tmp
  \ifin@\ch@papertrue\fi
  \PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax
\ifch@paper\else\PassOptionsToClass{letterpaper}{article}\fi

\LoadClass{article}

%% --- Fonts ------------------------------------------------------------------
\RequirePackage[T1]{fontenc}
\RequirePackage{textcomp}
\ifch@pazo
  \RequirePackage[sc]{mathpazo}      % Palatino text + Palatino math
  \linespread{1.05}
\else
  \renewcommand{\rmdefault}{ppl}     % Palatino text, Computer Modern math
\fi
\renewcommand{\ttdefault}{pcr}       % Courier for \texttt and URLs
\ifch@microtype
  \RequirePackage[final]{microtype}
\fi

%% --- Maths ------------------------------------------------------------------
\RequirePackage{amsmath,amssymb,amsthm,mathtools}

% Space around theorems and proofs: amsthm's usual amounts, or exactly one
% blank line under `spaced', matching the gap between paragraphs.
\ifch@spaced
  \def\ch@thmskip{\baselineskip}\def\ch@proofskip{\baselineskip}
\else
  \def\ch@thmskip{\topsep}\def\ch@proofskip{6\p@\@plus6\p@}
\fi
\renewenvironment{proof}[1][\proofname]{\par
  \pushQED{\qed}%
  \normalfont \topsep\ch@proofskip\relax
  \trivlist
  \item[\hskip\labelsep\itshape #1\@addpunct{.}]\ignorespaces
}{%
  \popQED\endtrivlist\@endpefalse
}
\newtheoremstyle{chplain}{\ch@thmskip}{\ch@thmskip}{\itshape}{}{\bfseries}{.}{.5em}{}
\newtheoremstyle{chdefinition}{\ch@thmskip}{\ch@thmskip}{\normalfont}{}{\bfseries}{.}{.5em}{}
\newtheoremstyle{chremark}{\ch@thmskip}{\ch@thmskip}{\normalfont}{}{\itshape}{.}{.5em}{}

\theoremstyle{chplain}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{conjecture}[theorem]{Conjecture}
\theoremstyle{chdefinition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\theoremstyle{chremark}
\newtheorem*{remark}{Remark}

%% --- Page -------------------------------------------------------------------
% Plain article geometry: 345pt measure, no running heads, page number
% centred in the footer.
\pagestyle{plain}

% Widows and orphans: never leave a single line of a paragraph alone at the
% top or bottom of a page.
\clubpenalty=10000
\widowpenalty=10000
\displaywidowpenalty=10000

%% --- Footnotes --------------------------------------------------------------
% More air between the text and the footnote rule (article default is 10pt),
% a little more between notes, and a small gap after the footnote number.
\setlength{\skip\footins}{1.6\baselineskip plus 4pt minus 2pt}
\setlength{\footnotesep}{1.15\footnotesep}
\renewcommand\@makefntext[1]{%
  \parindent 1em\noindent
  \hb@xt@1.8em{\hss\@makefnmark\kern2pt}#1}

\ifch@spaced
  \parskip=1\baselineskip plus 2pt minus 1pt\relax
  % With a blank line between paragraphs, article's heading skips would stack
  % on top of \parskip. Trim them so headings sit evenly.
  \renewcommand\section{\@startsection{section}{1}{\z@}%
    {-2.5ex \@plus -1ex \@minus -.2ex}{0.4ex}{\normalfont\Large\bfseries}}
  \renewcommand\subsection{\@startsection{subsection}{2}{\z@}%
    {-2ex \@plus -.5ex \@minus -.2ex}{0.2ex}{\normalfont\large\bfseries}}
\fi

%% --- Sections ---------------------------------------------------------------
% \section{} (empty title) prints just the bold number, as in a letter or
% remark split into numbered parts. \section{Title} works as usual.
\RequirePackage{enumitem}
\setlist{itemsep=2pt,topsep=4pt}

%% --- Title block ------------------------------------------------------------
% Optional. Left-aligned and small, so a document can also start straight in.
\renewcommand{\maketitle}{%
  \begingroup
    \noindent{\Large\bfseries\@title\par}%
    \ifx\@author\@empty\else\vspace{4pt}\noindent{\@author\par}\fi
    \ifx\@date\@empty\else\vspace{2pt}\noindent{\small\@date\par}\fi
    \vspace{18pt}%
  \endgroup
  \thispagestyle{plain}%
  \global\let\maketitle\relax
}
\author{}
\date{}

%% --- Links ------------------------------------------------------------------
\RequirePackage{xcolor}
\definecolor{chlink}{HTML}{1F4E8C}
\RequirePackage{url}
\RequirePackage{hyperref}
\def\ch@tmp{color}\ifx\ch@links\ch@tmp
  \hypersetup{colorlinks=true,linkcolor=chlink,citecolor=chlink,urlcolor=chlink}
\fi
\def\ch@tmp{hide}\ifx\ch@links\ch@tmp
  \hypersetup{hidelinks}
\fi
\hypersetup{pdfcreator={LaTeX with charlie.cls}}

\endinput
