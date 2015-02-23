% -*- mode: LaTeX; compile-command: "runghc Shake" -*-
\documentclass[authoryear,preprint]{sigplanconf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lhs2tex setup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt
%include lhs2TeX.sty
%options ghci

%%format `mplus` = "\oplus"
%format <$> = "\mathbin{\langle \$ \rangle}"

\arrayhs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Package imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[authoryear]{natbib}

\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{tikz}
\usepackage{prettyref}
\usepackage{xspace}
\usepackage{url}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Semantic markup
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\term}[1]{\emph{#1}}

\newcommand{\pkg}[1]{\texttt{#1}}
\newcommand{\ext}[1]{\texttt{#1}}
\newcommand{\module}[1]{\texttt{#1}}

\newcommand{\ie}{i.e.\xspace}
\newcommand{\eg}{e.g.\xspace}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Prettyref
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newrefformat{fig}{Fig.~\ref{#1}}
\newrefformat{sec}{Sect.~\ref{#1}}
\newrefformat{eq}{Equation~\eqref{#1}}
\newrefformat{prob}{Problem~\ref{#1}}
\newrefformat{tab}{Table~\ref{#1}}
\newrefformat{thm}{Theorem~\ref{#1}}
\newrefformat{lem}{Lemma~\ref{#1}}
\newrefformat{prop}{Proposition~\ref{#1}}
\newrefformat{defn}{Definition~\ref{#1}}
\newrefformat{cor}{Corollary~\ref{#1}}
\newcommand{\pref}[1]{\prettyref{#1}}

% \Pref is just like \pref but it uppercases the first letter; for use
% at the beginning of a sentence.
\newcommand{\Pref}[1]{%
  \expandafter\ifx\csname r@@#1\endcsname\relax {\scriptsize[ref]}
    \else
    \edef\reftext{\prettyref{#1}}\expandafter\MakeUppercase\reftext
    \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Notes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newif\ifcomments\commentstrue

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\bay}[1]{\authornote{blue}{BAY}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Main document
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country}
\copyrightyear{2015}
\copyrightdata{[to be supplied]}
% \doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish,
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers,
                                  % short abstracts)

\titlebanner{DRAFT --- do not distribute}
% \preprintfooter{short description of paper}

\title{Upgrading Booleans}
% \subtitle{Subtitle Text, if any}

\authorinfo{Brent A. Yorgey}
           {Williams College}
           {byorgey@@gmail.com}

\maketitle

\begin{abstract}
Take functions that return boolean values and upgrade them to other
useful stuff!
\end{abstract}

\category{CR-number}{subcategory}{third-level}

\keywords
keyword1, keyword2


%if false
\begin{code}
import Control.Monad (mplus)
import Control.Applicative
\end{code}
%endif

\section{Introduction}

The classic \term{subset sum} problem asks, given a set of integers
and another target integer, whether there is some subset of the given
set which sums to the target integer.  This problem turns out to be
NP-complete \cite{XXX}, but that will not concern us; consider the
following brute-force solution in Haskell:

\begin{code}
subSum :: (Num a, Eq a) => [a] -> a -> Bool
subSum _       0  = True
subSum []      _  = False
subSum (a:as)  t  = subSum as t || subSum as (t - a)
\end{code}

We can always sum to $0$ (by choosing the empty subset); we cannot sum
to a nonzero value given the empty set; otherwise, we try both using
and not using the first element in the set, and try the rest
recursively.

This code works, but suffers from an obvious deficiency: |subSum|
tells us \emph{only whether} an appropriate subset exists, without
actually exhibiting one.  Observe: \[ |subSum [12, 1, 3, 8, 20, 50, 7,
19, -8, -23] 14
= | \eval{subSum [12, 1, 3, 8, 20, 50, 7, 19, -8, -23] 14} \]
Quick, what is the subset of $\{12, 1, 3, 8, 20, 50, 7, 19, -8, -23\}$
that sums to $14$?

The problem, of course, is that |subSum| throws away information.
While it is evaluating, a particular subset summing to the target is
encoded in the pattern of recursive calls it makes, but we
deliberately ignore that information and return a single |Bool|.  We
can alter it to actually return a satisfying subset as follows:

\begin{code}
findSubSum :: (Num a, Eq a) => [a] -> a -> Maybe [a]
findSubSum _       0  =  Just []
findSubSum []      _  =  Nothing
findSubSum (a:as)  t  =  findSubSum as t
                         `mplus`
                         ((a:) <$> findSubSum as (t - a))
\end{code}
%$
The first two cases are very similar to |subSum|: to sum to $0$, we
can choose the empty subset, and no subset of the empty set will sum
to a nonzero number.  The |`mplus`| operation implements left-biased
choice, choosing the first |Just| value.  |(a:) <$> ...|  % $
prepends |a| to the front of the result (if any) returned by the
recursive call to |findSubSum|.

With this code, we can find that \[ |findSubSum [12, 1, 3, 8, 20, 50, 7,
19, -8, -23] 14
= | \eval{findSubSum [12, 1, 3, 8, 20, 50, 7, 19, -8, -23] 14}. \]
A few observations are in order.
\begin{itemize}
\item The code for |findSubSum| is structurally very similar to the
  code for |subSum|.
\item Yet the code is a bit harder to write
\item If we wanted to get yet different output (e.g. the complete list
  of \emph{all} subsets summing to the target) we would have to change
  the code again
\end{itemize}

\todo{In this case we could easily implement |subSum| in terms of
  |findSubSum| (|isJust|), but that might not always be so easy}

\acks

\todo{Thanks!}

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}
\bibliography{upgrading}

% The bibliography should be embedded for final submission.

% \begin{thebibliography}{}
% \softraggedright

% \bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
% P. Q. Smith, and X. Y. Jones. ...reference text...

% \end{thebibliography}


\end{document}
