/-
 Numeric

 The Art

 Harvard

 §

 Department

 W

 EXXON

 CAMBRIDGE

 Cambridge  New
 Published by the Press Syndicate of the University of Cambridge
 The Pitt Building, Trumpington Street, Cambridge CB2 1RP
 40 West 20th Street, New York, NY 10011-4211
 477 Williamstown Road,  Port Melbourne, VIC 3207, Australia

 Copyright © Cambridge University Press 1986, 1992
 except for §13.10 and Appendix C, which are copyright © Numerical Recipes Software 1986, 1992
 and except for all other contributions.

 Copyright © Numerical Recipes Software 1986, 1992
 All Rights Reserved.

 Some sections of this book originally appeared in slightly different form in *Physics Today* and *Physics magazine*, Copyright © American Institute of Physics.

 First Edition originally published 1988
 Reprinted with corrections 1992
 This reprinting is corrected to the second edition

 Printed in the United States of America
 Typeset in $\TeX$

 Without an additional charge, we supply, with the book, a
 text and reference book, and also the complete set of C source code routines—as machine-readable files on MS-DOS diskettes—
 software by the individual user. We are able to bundle these routines into a single compressed file, and to offer it for purchase under the
 “License Information” (pp. xvi–xvii) that is contained within the book, at low cost.

 Machine-readable material can be supplied only to purchasers of the book. The
 for use on a single screen is given at the back of this book.  To order the software, please use the form at the back of this book or send an e-mail to
 “directcustserv@cambridge.org” or write to Cambridge University Press,
 110 Midland Avenue, Port Melbourne, VIC 3207, Australia.

 The software may not be copied onto any media. For specific details, please see pp. xvi–xvii. It is also
 also possible, from the Network Theory Limited, to purchase the software on magnetic tape.

 Unlicensed transfer of Numerical Recipes software to any computer except one that is your personal computer is illegal.  For corrections, and requests
 for the latest version of the software, contact Numerical Recipes Software, P.O. Box 38024, Cambridge, MA 02138, USA.
 or fax 781 863-1739.

 Library of Congress Cataloging-in-Publication Data
 Numerical recipes in C : the art of scientific computing / William H. Press ... [et al.]. — 2nd ed.
 Includes bibliographic references and index.
 ISBN 0-521-43108-5

 1. Numerical analysis—Computer programs. 2. C (Computer program language) I. Press, William H. II. Title.
 QA297.N866 1992
 519.4′0285′53—dc20 91-43721 CIP

 A catalog record for this book is available from the British Library.

 ISBN 0 521 43108 5   Book and Diskette
 ISBN 0 521 43720 2   Book only
 ISBN 0 521 75037 7   C Diskette only
 ISBN 0 521 75035 0   FORTRAN Diskette only
 ISBN 0 521 75036 9   PASCAL Diskette only


 Preface to the S
 Preface to the F
 License Informa
 Computer Prog
 1 Preliminaries
 1.0 Introduction
 1.1 Program Organization
 1.2 Some C Conventions
 1.3 Error, Accuracy, and Stability
 2 Solution of Linear Equations
 2.0 Introduction
 2.1 Gauss-Jordan Elimination
 2.2 Gaussian Elimination
 2.3 LU Decomposition
 2.4 Tridiagonal and Banded Systems
 2.5 Iterative Improvement
 2.6 Singular Value Decomposition
 2.7 Sparse Linear Systems
 2.8 Vandermonde Matrices
 2.9 Cholesky Decomposition
 2.10 QR Decomposition
 2.11 Is Matrix Inversion Necessary?
 3 Interpolation and Approximation
 3.0 Introduction
 3.1 Polynomial Interpolation
 3.2 Rational Function Interpolation
 3.3 Cubic Spline Interpolation
 3.4 How to Search an Interval
 3.5 Coefficients of the Interpolating Polynomial
 3.6 Interpolation in Two or More Variables
 --- OCR Start ---
 vi
 4 Integration of Functions
 4.0 Introduction
 4.1 Classical Formulas
 4.2 Elementary Algorithms
 4.3 Romberg Integration
 4.4 Improper Integrals
 4.5 Gaussian Quadratures
 4.6 Multidimensional

 5 Evaluation of Functions
 5.0 Introduction
 5.1 Series and Their Convergence
 5.2 Evaluation of Continued Fractions
 5.3 Polynomials and Rational Functions
 5.4 Complex Arithmetic
 5.5 Recurrence Relations
 5.6 Quadratic and Cubic Equations
 5.7 Numerical Derivatives
 5.8 Chebyshev Approximations
 5.9 Derivatives or Integrals of Polynomials
 5.10 Polynomial Approximations
 5.11 Economization of Polynomials
 5.12 Padé Approximations
 5.13 Rational Chebyshev Approximations
 5.14 Evaluation of Functions

 6 Special Functions
 6.0 Introduction
 6.1 Gamma Function, Gamma Function
 6.2 Incomplete Gamma Functions,
 Probability Functions
 6.3 Exponential Integrals
 6.4 Incomplete Beta Functions,
 Cumulative Binomial Distribution
 6.5 Bessel Functions of the First Kind
 6.6 Modified Bessel Functions
 6.7 Bessel Functions of the Second Kind
 Bessel Functions
 6.8 Spherical Harmonics
 6.9 Fresnel Integrals, Cosine and Sine Integrals
 6.10 Dawson's Integral
 6.11 Elliptic Integrals
 6.12 Hypergeometric Functions

 7 Random Numbers
 7.0 Introduction
 7.1 Uniform Deviates
 --- OCR End ---
 7.2 Transformation M
 7.3 Rejection Method=
 7.4 Generation of Ran
 7.5 Random Sequence
 7.6 Simple Monte Car
 7.7 Quasi- (that is, Sub
 7.8 Adaptive and Recu
 8 Sorting
 8.0 Introduction
 8.1 Straight Insertion a
 8.2 Quicksort
 8.3 Heapsort
 8.4 Indexing and Rank
 8.5 Selecting the $M$th
 8.6 Determination of E
 9 Root Finding ar
 9.0 Introduction
 9.1 Bracketing and Bis
 9.2 Secant Method, Fa
 9.3 Van Wijngaarden-
 9.4 Newton-Raphson
 9.5 Roots of Polynom
 9.6 Newton-Raphson
 9.7 Globally Converge
 10 Minimization or
 10.0 Introduction
 10.1 Golden Section S
 10.2 Parabolic Interpo
 10.3 One-Dimensiona
 10.4 Downhill Simple
 10.5 Direction Set (Po
 10.6 Conjugate Gradie
 10.7 Variable Metric M
 10.8 Linear Programm
 10.9 Simulated Annea
 11 Eigensystems
 11.0 Introduction
 11.1 Jacobi Transform
 11.2 Reduction of a S
 Givens and Hous
 11.3 Eigenvalues and
 11.4 Hermitian Matric
 11.5 Reduction of a G
 viii
 11.6 The QR Algorithm
 11.7 Improving Eigenvalues
 Inverse Iteration
 12 Fast Fourier Transform
 12.0 Introduction
 12.1 Fourier Transform
 12.2 Fast Fourier Transform
 12.3 FFT of Real Functions
 12.4 FFT in Two or More Dimensions
 12.5 Fourier Transform Properties
 12.6 External Storage
 13 Fourier and Spectral Analysis
 13.0 Introduction
 13.1 Convolution and Correlation
 13.2 Correlation and Autocorrelation
 13.3 Optimal (Wiener) Filtering
 13.4 Power Spectrum Estimation
 13.5 Digital Filtering in the Frequency Domain
 13.6 Linear Prediction and Spectral Estimation
 13.7 Power Spectrum Estimation
 (All Poles) Method
 13.8 Spectral Analysis Techniques
 13.9 Computing Fourier Transforms
 13.10 Wavelet Transforms
 13.11 Numerical Use of Wavelet Transforms
 14 Statistical Description of Data
 14.0 Introduction
 14.1 Moments of a Distribution,
 and So Forth
 14.2 Do Two Distributions Differ Significantly?
 14.3 Are Two Distributions the Same?
 14.4 Contingency Tables
 14.5 Linear Correlation and Regression
 14.6 Nonparametric or Rank Correlation
 14.7 Do Two-Dimensional Distributions Differ?
 14.8 Savitzky-Golay Smoothing
 15 Modeling of Data
 15.0 Introduction
 15.1 Least Squares as a Method of Fitting
 15.2 Fitting Data to a Straight Line
 15.3 Straight-Line Data with Errors in Both Variables
 15.4 General Linear Least Squares
 15.5 Nonlinear Model Fitting
 15.6 Confidence Limit
 15.7 Robust Estimation
 16 Integration of ODEs
 16.0 Introduction
 16.1 Runge-Kutta Methods
 16.2 Adaptive Stepsize Control
 16.3 Modified Midpoint Rule
 16.4 Richardson Extrapolation
 16.5 Second-Order Convergence
 16.6 Stiff Sets of Equations
 16.7 Multistep, Multivalue Methods
 17 Two Point Boundary Value Problems
 17.0 Introduction
 17.1 The Shooting Method
 17.2 Shooting to a Fitted Boundary
 17.3 Relaxation Methods
 17.4 A Worked Example
 17.5 Automated Allocation of Resources
 17.6 Handling Internal Boundary Conditions
 18 Integral Equations
 18.0 Introduction
 18.1 Fredholm Equations
 18.2 Volterra Equations
 18.3 Integral Equation Methods
 18.4 Inverse Problems
 18.5 Linear Regularization
 18.6 Backus-Gilbert Method
 18.7 Maximum Entropy Method
 19 Partial Differential Equations
 19.0 Introduction
 19.1 Flux-Conservative Schemes
 19.2 Diffusive Initial Value Problems
 19.3 Initial Value Problems
 19.4 Fourier and Cyclic Reduction for Initial Value Problems
 19.5 Relaxation Methods
 19.6 Multigrid Methods
 20 Less-Numerical Methods
 20.0 Introduction
 20.1 Diagnosing Machine Precision
 20.2 Gray Codes
 --- OCR Start ---
 x
 20.3 Cyclic Redundancy Check
 20.4 Huffman Coding
 20.5 Arithmetic Coding
 20.6 Arithmetic at Arbitrary Precision
 References
 Appendix A: Tables of Huffman Codes
 Appendix B: Utility Programs
 Appendix C: Codes for the Examples
 Index of Programs
 General Index
 --- OCR End ---
 --- OCR Start ---
 Preface

 Our aim in writing the
 book was to combine general
 actual working programs.
 Though hardly unenviable,
 that is informal, fearlessly
 balanced, scholarly, and both
 It is a mixed blessing that, if we are not careful,
 we were making educated guesses
 about which numerical techniques
 the benefit of direct feedback from
 enterprise. Numerical Recipes
 telephone us.) Our post-publication plan is
 that we have omitted some
 particular field of science and
 carefully, especially when the
 The inevitable result is that
 Recipes is substantially larger
 words and number of included
 "Don't let the book grow in
 colleagues. We have tried not to
 violate the letter of it. We have
 principal discussions of many topics at the
 same accessible level. Some topics, such as those that
 one, are now set in smaller type, and
 who ignores such advanced material will lose
 continuity in the shorter versions.

 Here are some highlights of the additions:
 • a new chapter on integral equations
 • a detailed treatment of stiff ordinary
 differential equations
 • routines for band diagonal and sparse matrices
 • improved routines for the solution of linear equations
 • Cholesky and QR decompositions
 • orthogonal polynomials
 functions
 • methods for calculating continued fractions
 • Padé approximants
 • Bessel functions, and
 several other new special functions
 • improved random number generators
 • quasi-random sequences
 • routines for adaptive quadrature in high-
 dimensional spaces
 • globally convergent multidimensional minimization routines

 --- OCR End ---
 xiii
 • simulated annealing
 • fast Fourier transforms
 • improved fast cosine transforms
 • wavelet transforms
 • Fourier integrals with singularities
 • spectral analysis on unevenly sampled data
 • Savitzky-Golay smoothing
 • fitting straight lines and polynomials
 • a two-dimensional fast Fourier transform
 • the statistical bootstrap
 • embedded Runge-Kutta methods
 • high-order methods for ODEs
 • a new chapter on arithmetic coding, and much more
 Consult the Preface to the First Edition for a list of the more "basic" subjects.

 Acknowledgments

 It is not possible for us to acknowledge all the useful suggestions; we are especially grateful for attribution for ideas that appear in this book. We apologize in advance for any omissions.  Some readers and colleagues have been particularly helpful with ideas, comments, and support. We especially want to thank  David Lupton, Douglas Eardley, Robert Lupton, Baliunas, Scott Tremaine,  John Loredo, Matthew Choptuik,  Jeffrey Lewis, Peter Weinberger,  David Keister, and William Gould  for help with many aspects of a complicated TEX manuscript. Cowles and Alan Harvey at the University of Chicago Press, and Russell Hahn. We remain grateful for their help.  Special acknowledgment goes to Seth Wolpert, who wrote, rewrote, or influenced almost all of the FORTRAN-language twin routines. We benefited enormously from his good programming sense and his work; even the very slight anomalies (often stylistic) in his approach to coding in C has a more graceful and powerful style. A significant amount of the credit goes to Seth for catching many lapses that still remain.  We prepared this book using the UNIX operating system (mostly) and MS-DOS 5.0/Windows 3.0.


 program tests.) We enthusiastically use
 Emacs, $\TeX$, Perl, Adobe Illustrator, and many other
 compilers — too numerous to
 ment. It is a sobering fact that this book) has uncovered
 possible, we work with developers at WHP and SAT acknowledged for their research.
 interested compiler developers at
 WHP and SAT acknowledge
 Foundation for their research; we are
 acknowledged for $\pounds 13.10$
 June, 1992
 --- OCR Start ---
 Prefac
 We call this book Num
 is indeed a "cookbook" on
 distinction between a cookbook
 among complete dishes in
 disguised. The former
 explains how they are prepared.
 Another purpose of this book is
 techniques. This book is used
 a certain amount of general
 a certain amount of discussion
 mentations of these ideas in
 been to find the right balance.
 find that for some topics we
 have felt there to be gaps in
 where the mathematical prerequisites
 more in-depth discussion of
 practical questions of importance.
 We admit, therefore, to
 of it is suitable for an advanced
 science or engineering major's
 course to that of a professional
 varying levels of complexity. Even inexperienced
 the reader can use the book as
 grows. Even inexperienced
 as black boxes. Having done so,
 back and learn what secrets
 If there is a single doctrine
 of numerical computation of
 clear. The alternative
 necessarily be so arcane and
 we firmly reject.
 Our purpose in this book is
 black boxes to your scrutiny
 and to put them back together.
 We assume that you are not
 mathematical preparation in
 science, or engineering, or
 that you know how to program.
 prior formal knowledge of
 The scope of Numerics is
 not including, partial differential
 we do have one introductory
 (Chapter 19). Second, we omit
 "standard" topics of a numerical
 --- OCR End ---
 linear equations (Chapter 2
 (Chapter 4), nonlinear root
 ordinary differential equations
 beyond their standard treatment
 to be particularly important.
 Some other subjects that
 numerical analysis texts. The
 special functions of higher
 Monte Carlo methods (Chapter
 multidimensional methods
 methods and other spectral
 statistical description and
 boundary value problems, but
 The programs in this
 book in FORTRAN, Pascal,
 to say about the C language
 routines, in §1.1 (Introduction
 Acknowledgments

 Many colleagues have
 and computational experience
 the manuscript, or in general
 Rybicki, Douglas Eardley,
 Musicus, Irwin Shapiro, Stan
 Muller, John Bahcall, and
 We also wish to acknowledge
 Acton, whose 1970 textbook
 (Row) has surely left its style
 of books on The Art of Computing
 and for TEX, the computer
 of this book.

 Research by the author
 the U.S. National Science
 October, 1985
 --- OCR Start ---
 Lic

 Read this section if you
 You'll need to read the following
 computer, and acquire a Numerical
 which can be the free “immutable”
 intended as a text and reference

 Disclaimer of Warranty

 We make no warranty that
 in this volume are free of
 of merchantability, or that
 application. They should
 solution could result in incorrect
 programs in such a manner. We
 disclaim all liability for consequences of
 use of the programs.

 How to Get the Code

 Pick one of the following:
 • You can type the programs. In this
 case, the only kind of distribution
 (see below). You are not allowed to
 copy to any other person or to any
 computer on your behalf. If you
 choose this option, be warned that errors
 in such cases are typical.
 • You can download
 Numerical Recipes Online from the
 Web site. All the files are delivered as
 a single compressed archive; you must
 unpack them. Any multiple-user license
 (with discount for multiple-user) applies
 on your operating system, regardless of
 whether you are affiliated with any
 screen license is also available for
 or corporate) licenses; there are no
 any later license upgrades.
 • You can purchase media.
 A CD-ROM version
 contains the complete source code,
 ROMs in ISO-9660 format. Floppy disks are
 also available; these include versions for DOS,
 (as well as versions in various formats)
 are available with a single-user license (ISBN
 0 521 750350), or (for multiple users)
 UNIX/Linux workstations. You can order
 Cambridge University Press, either by mail
 or by email to orders@cup.cam.ac.uk
 (rest of world). Or, via phone
 --- OCR End ---
 --- OCR Start ---
 Types of License O
 Here are the types of
 automatically acquired with
 Press, or of an unlocking procedure from the
 Store, while other types of licenses are obtained from our
 Numerical Recipes Software
 Web site http://www.nr.com.  These are:

 • ["Immediate License": This license is activated when
 you type one or more registration numbers for it into
 them on that computer. Persons other than you
 are not authorized to use the program on that machine
 person, or to use the registered programs containing them.

 • ["Single-Screen License": Use of our routines is governed by our
 terms governed by our standard single-screen license
 terms available through our web site.  These terms state that (i) you may not
 Recipes routines on a single screen. You may not (i) sell, give away, or otherwise transfer
 also, under this license, you may not transfer any part of
 our routines to other users (unless explicitly authorized
 application is noncommercial use (or made available for use
 for a fee), (ii) the program must be run and used only
 on a licensed screen, and (iii) the program must be used in such a
 manner that they cannot be easily copied, and that they may not
 be unbound and used apart from the licensed package (e.g., a
 user must not be able to extract the routines and use them in a
 match" workbench. Copyright protection for our Numerical Recipes Software
 distribution may be further restricted by other terms

 • ["Multi-Screen, Server, or Site License": A Multi-
 Screen License can be obtained for any desired
 number of screens, including servers. We offer substantial
 discounts from the cost of multiple single-screen licenses based on the
 estimated number of screens required. Contact us at
 (email: orders@nr.com)

 • ["Course Right-to-Copy License":  This license is offered to educational institutions
 who have adopted this course as part of their curriculum. It provides a
 Screen License (either single screen or multi-screen).

 Recipes On-Line Software licenses can be obtained
 as follows: Mail your course syllabus, an estimated class size,
 and estimated enrollment to: Numerical Recipes Software, P.O. Box 11300,
 02238 (USA). You will receive the necessary registration
 copies of the program and will be given instructions on how to obtain
 a machine accessible copy of the software.

 About Copyrights c
 Like artistic or literary works, computer programs are subject to
 copyright. Generally it is illegal to copy a computer
 program from a copyrighted source without permission. Doing so
 deprives the program's author of compensation for his or her work, and it harms
 --- OCR End ---
 xviii
 copyright law, all "derivative
 computer language) also co
 Copyright does not protect
 a particular form. In the
 program's methodology and
 adopted by the programme
 code (particularly any arbitrary
 code, and any other derivative
 If you analyze the ideas
 ideas in your own complete
 implementation belongs to
 this book that are not entirely
 said to be "based" on program
 ideas are the same. The experts
 believe that no material in this
 Trademarks
 Several registered trademarks
 trademark of Sun Microsystems, Inc.
 of SPARC International, Inc.,
 and MS are trademarks of
 ULTRIX are trademarks of
 International Business Machines
 of Apple Computer, Inc. Unix is a
 Co. Ltd. IMSL is a trademark of
 computer software of Numerical
 Adobe Illustrator are trademarks of
 least, Numerical Recipes (Cam-
 Recipes Software.
 Attributions
 The fact that ideas are
 requirement that ideas be clear
 this book are based on knowledge
 published or "handed-down"
 tunately, the lineage of many
 would be grateful to readers
 which we will attempt to improve


 --- OCR Start ---
 Cor
 by CI
 1.0
 flmoon
 1.1
 julday
 1.1
 badluk
 1.1
 caldat
 2.1
 gaussj
 2.3
 ludcmp
 2.3
 lubksb
 2.4
 tridag
 2.4
 banmul
 2.4
 bandec
 2.4
 banbks
 2.5
 mprove
 2.6
 svbksb
 2.6
 svdcmp
 2.6
 pythag
 2.7
 cyclic
 2.7
 sprsin
 2.7
 sprsax
 2.7
 sprstx
 2.7
 sprstp
 2.7
 sprspm
 2.7
 sprstm
 2.7
 linbcg
 2.7
 snrm
 2.7
 atimes
 2.7
 asolve
 2.8
 vander
 2.8
 toeplz
 2.9
 choldc
 2.9
 cholsl
 2.10 qrdcmp
 2.10 qrsolv
 2.10
 rsolv
 2.10 qrupdt
 2.10
 rotate
 3.1
 polint
 3.2
 ratint
 3.3
 spline
 3.3
 splint
 3.4
 locate
 --- OCR End ---
 --- OCR Start ---
 XX
 Com
 3.4
 hunt
 3.5
 polcoe
 3.5
 polcof
 3.6
 polin2
 3.6
 bcucof
 3.6
 bcuint
 3.6
 splie2
 3.6
 splin2
 4.2
 trapzd
 4.2
 qtrap
 4.2
 qsimp
 4.3
 qromb
 4.4
 midpnt
 4.4
 qromo
 4.4
 midinf
 4.4
 midsql
 4.4
 midsqu
 4.4
 midexp
 4.5
 qgaus
 4.5
 gauleg
 4.5
 gaulag
 4.5
 gauher
 4.5
 gaujac
 4.5
 gaucof
 4.5
 orthog
 4.6
 quad3d
 5.1
 eulsum
 5.3
 ddpoly
 5.3
 poldiv
 5.3
 ratval
 5.7
 dfridr
 5.8
 chebft
 5.8
 chebev
 5.9
 chder
 5.9
 chint
 5.10
 chebpc
 5.10
 pcshft
 5.11
 pccheb
 5.12
 pade
 5.13
 ratlsq
 6.1
 gammln
 6.1
 factrl
 6.1
 bico
 6.1
 factln
 --- OCR End ---
 --- OCR Start ---
 Computer
 6.1	beta
 6.2	gammp
 6.2	gammq
 6.2	gser
 6.2	gcf
 6.2	erff
 6.2	erffc
 6.2	erfcc
 6.3	expint
 6.3	ei
 6.4	betai
 6.4	betacf
 6.5	bessj0
 6.5	bessy0
 6.5	bessj1
 6.5	bessy1
 6.5	bessy
 6.5	bessj
 6.6	bessio
 6.6	bessk0
 6.6	bessi1
 6.6	bessk1
 6.6	bessk
 6.6	bessi
 6.7	bessjy
 6.7	beschb
 6.7	bessik
 6.7	airy
 6.8	sphbes
 6.9	plgndr
 6.9	frenel
 6.9	cisi
 6.10	dawson
 6.11	rf
 6.11	rd
 6.11	rj
 6.11	rc
 6.11	ellf
 6.11	elle
 6.11	ellpi
 6.11	sncndn
 6.12	hypgeo
 6.12	hypser
 6.12	hypdrv
 7.1	rano
 7.1	ran1
 --- OCR End ---
 --- OCR Start ---
 xxii
 7.1	ran2
 7.1	ran3
 7.2	expdev
 7.2	gasdev
 7.3	gamdev
 7.3	poidev
 7.3	bnldev
 7.4	irbit1
 7.4	irbit2
 7.5	psdes
 7.5	ran4
 7.7	sobseq
 7.8	vegas
 7.8	rebin
 7.8	miser
 7.8	ranpt
 8.1	piksrt
 8.1	piksr2
 8.1	shell
 8.2	sort
 8.2	sort2
 8.3	hpsort
 8.4	indexx
 8.4	sort3
 8.4	rank
 8.5	select
 8.5	selip
 8.5	hpsel
 8.6	eclass
 8.6	eclazz
 9.0	scrsho
 9.1	zbrac
 9.1	zbrak
 9.1	rtbis
 9.2	rtflsp
 9.2	rtsec
 9.2	zriddr
 9.3	zbrent
 9.4	rtnewt
 9.4	rtsafe
 9.5	laguer
 9.5	zroots
 9.5	zrhqr
 9.5	qroot
 Com
 --- OCR End ---
 --- OCR Start ---
 Computer F
 9.6	mnewt
 9.7	Insrch
 9.7	newt
 9.7	fdjac
 9.7	fmin
 9.7	broydn
 10.1	mnbrak
 10.1	golden
 10.2	brent
 10.3	dbrent
 10.4	amoeba
 10.4	amotry
 10.5	powell
 10.5	linmin
 10.5	f1dim
 10.6	frprmn
 10.6	dlinmin
 10.6	df1dim
 10.7	dfpmin
 10.8	simplx
 10.8	simp1
 10.8	simp2
 10.8	simp3
 10.9	anneal
 10.9	revcst
 10.9	reverse
 10.9	trncst
 10.9	trnspt
 10.9	metrop
 10.9	amebsa
 10.9	amotsa
 11.1	jacobi
 11.1	eigsrt
 11.2	tred2
 11.3	tqli
 11.5	balanc
 11.5	elmhes
 11.6	hqr
 12.2	four1
 12.3	twofft
 12.3	realft
 12.3	sinft
 12.3	cosft1
 12.3	cosft2
 --- OCR End ---
 --- OCR Start ---
 xxiv
 Con
 12.4	fourn
 12.5	rlft3
 12.6	fourfs
 12.6	fourew
 13.1	convlv
 13.2	correl
 13.4	spctrm
 13.6	memcof
 13.6	fixrts
 13.6	predic
 13.7	evlmem
 13.8	period
 13.8	fasper
 13.8	spread
 13.9	dftcor
 13.9	dftint
 13.10	wt1
 13.10	daub4
 13.10	pwtset
 13.10	pwt
 13.10	wtn
 14.1	moment
 14.2	ttest
 14.2	avevar
 14.2	tutest
 14.2	tptest
 14.2	ftest
 14.3	chsone
 14.3	chstwo
 14.3	ksone
 14.3	kstwo
 14.3	probks
 14.4	cntab1
 14.4	cntab2
 14.5	pearsn
 14.6	spear
 14.6	crank
 14.6	kendl1
 14.6	kend12
 14.7	ks2d1s
 14.7	quadct
 14.7	quadvl
 14.7	ks2d2s
 14.8	savgol
 --- OCR End ---
 --- OCR Start ---
 Computer
 15.2	fit
 15.3	fitexy
 15.3	chixy
 15.4	lfit
 15.4	covsrt
 15.4	svdfit
 15.4	svdvar
 15.4	fpoly
 15.4	fleg
 15.5	mrqmin
 15.5	mrqcof
 15.5	fgauss
 15.7	medfit
 15.7	rofunc
 16.1	rk4
 16.1	rkdumb
 16.2	rkqs
 16.2	rkck
 16.2	odeint
 16.3	mmid
 16.4	bsstep
 16.4	pzextr
 16.4	rzextr
 16.5	stoerm
 16.6	stiff
 16.6	jacobn
 16.6	derivs
 16.6	simpr
 16.6	stifbs
 17.1	shoot
 17.2	shootf
 17.3	solvde
 17.3	bksub
 17.3	pinvs
 17.3	red
 17.4	sfroid
 17.4	difeq
 17.4	sphoot
 17.4	sphfpt
 18.1	fred2
 18.1	fredin
 18.2	voltra
 18.3	wwghts
 18.3	kermom
 --- OCR End ---
 --- OCR Start ---
 xxvi
 Con
 18.3
 quadmx
 18.3
 fredex
 19.5
 sor
 19.6
 mglin
 19.6
 rstrct
 19.6
 interp
 19.6
 addint
 19.6
 slvsml
 19.6
 relax
 19.6
 resid
 19.6
 copy
 19.6
 fill0
 19.6
 mgfas
 19.6
 relax2
 19.6
 slvsm2
 19.6
 lop
 19.6
 matadd
 19.6
 matsub
 19.6
 anorm2
 20.1
 machar
 20.2
 igray
 20.3
 icrc1
 20.3
 icrc
 20.3
 decchk
 20.4
 hufmak
 20.4
 hufapp
 20.4
 hufenc
 20.4
 hufdec
 20.5
 arcmak
 20.5
 arcode
 20.5
 arcsum
 20.6
 mpops
 20.6
 mpmul
 20.6
 mpinv
 20.6
 mpdiv
 20.6
 mpsqrt
 20.6
 mp2dfr
 20.6
 mppi
 --- OCR End ---
 Chapter 1.
 1.0 Introduction
 This book, like its predecessors, is about numerical computing that aims to get things done. We view computation as a process, and if it looks like we may try to reroute you through some long and arduous theoretical landscape, we will guide you along a shorter path. Throughout this book we make many decisions for you; what you should and should not do. This is a conscious decision on our part, and we will state openly and explicitly when we claim that our advice is informed by—and consistent with—the textbook literature of computational physics and numerical analysis. We assume that essentially all of what you need to know has either been invented, without recourse to arcane and advanced mathematics; therefore, we offer you our combined experience, and we hope that, as you read and work through this book, you will form your own views. We presume that you are already familiar with programming in either C or C++; the language of this version of Numerical Recipes.  If you prefer to program in that language, we offer you the book *Numerical Recipes in C++*, and *Numerical Recipes in FORTRAN* versions are available; these are essentially the same books as this one, but not containing the additional C++-specific material.  FORTRAN, these versions are also available. The choice is yours; that language is a matter of personal choice.
 When we include programs, we will use the following conventions.

 #include <math.h>
 #define RAD (3.14159265/180.0)
 void flmoon(int n, int nph)
 Our programs begin with an introductory comment that specifies the calling sequence. This routine calculates the phase of the moon (a code nph for the phase desired: 0 for new moon, 1 for first quarter), the routine returns the number of days after the epoch to be added to it, of the nth such phase.
 {
 void nrerror (char error_text[])
 int i;
 float am, as,c,t,t2, xtr
 c=n+nph/4.0;


 --- OCR Start ---
 2
 }
 t=c/1236.85;
 t2=t*t;
 as=359.2242+29.105356*
 am=306.0253+385.816918
 *jd=2415020+28L*n+7L*n
 xtra=0.75933+1.5305886
 if (nph == 0 || nph ==
 xtra += (0.1734-3.
 else if (nph == 1 || n
 xtra += (0.1721-4.
 else nrerror("nph is u
 i=(int) (xtra >= 0.0 ?
 *jd += i;
 *frac=xtra-i;
 If the syntax of the function is
 probably used to the older K&R
 the newer ANSI C. In this example
 to look ahead to §1.2 where
 Note our convention of
 like nrerror("some error")
 small file of utility programs in
 book. This Appendix includes
 this chapter. Function nrerror
 device (usually your terminal)
 terminates execution. The
 you find it missing, you can
 halt execution. For example
 then manually interrupt execution
 nrerror() to do more sophisticated
 somewhere else, with an error
 and style, in §1.1 and §1.2.
 Computational Env
 Our goal is that the program
 different platforms (models and
 across different C compilers in
 mind. Nevertheless, we have
 all programs on a variety of
 library structure or contents.
 surrogates for the large number of
 programs in this book on
 compilers shown on the accompanying
 run without modification on
 as described for example in
 modifications, our programs
 de facto K&R standard [2]
 watch out for is that ANSI
 --- OCR End ---
 Hardware
 IBM PC compatible 486/3
 IBM PC compatible 486/3
 IBM RS/6000
 DECstation 5000/25
 DECsystem 5400
 Sun SPARCstation 2
 DECstation 5000/200
 Sun SPARCstation 2
 *compiler version does not
 and free() to be declared
 them to be declared with
 inherent in the language and
 In validating the programs
 from the machine-readable
 of propagating typographic
 used as part of our validation
 Example Book (C), as well
 than a few of the programs
 on more than one different
 of these demonstration programs
 Of course we would be
 and we do not make such a
 from the experience of the
 bug, please document it as
 Compatibility with the
 If you are accustomed
 assured: almost all of them
 often with major improvements
 will soon become equally familiar
 routines that are new to the
 We have retired a small
 to be clearly dominated by
 following, lists the retired
 First Edition users should
 editions have alterations in
 ible." A fairly complete list
 memcof, mrqcof, mrqmin,
 may be others (depending
 for the comparison). If you
 --- OCR Start ---
 4
 \begin{tabular}{|l|l|}
 \hline
 Name(s) & Prev \\
 \hline
 adi & m \\
 cosft & c \\
 cel, e12 & r \\
 des, desks & r \\
 mdian1, mdian2 & s \\
 qcksrt & s \\
 rkqc & r \\
 smooft & us \\
 sparse & 1 \\
 \hline
 \end{tabular}
 that is dependent on First E
 them by the corresponding
 programming efforts use th
 About References
 You will find references at the
 end of most sections of this book.
 Numbers like this [3].
 Because computer algorithms
 before appearing in a publication
 is sometimes quite difficult to get
 to any degree of bibliographic
 substantial secondary literature. We
 have consciously limited our
 sources, especially those which are
 existing secondary literature. The
 sources that are intended to be
 complete bibliographies for
 The order in which references
 promise between listing them and
 for further reading in a rough
 The remaining three:
 programming (control structures),
 that we have adopted in this book;
 numerical analysis (rounding
 material of the book.
 CITED REFERENCES AND FURTHER READING
 Harbison, S.P., and Steele, G.
 NJ: Prentice-Hall). [1]
 --- OCR End ---
 --- OCR Start ---
 1.1 Program
 Kernighan, B., and Ritchie, D.
 Prentice-Hall). [2] [Reference
 to the ANSI C standard.
 Meeus, J. 1982, Astronomical
 mond, VA: Willmann-Bell

 1.1 Program Or
 Structures

 We sometimes like to present
 on the one hand, and write
 three present themselves as a
 computer screen. Yet, in all
 representation communication
 different, namely a process
 played; a program, executed
 In all three cases, the task is
 being. The goal is to translate
 the greatest degree of understanding
 time. In poetry, this human
 programming, it is the process
 Now, you may object that this is
 a human but a computer, that is
 a lackey who feeds the machine,
 the business executive points to a
 computer a black-box program. In this
 case, doesn't much care whether this
 practice" or not.

 We envision, however, a different
 situation. You need, or want to know
 it does it, so that you can tinker with
 You need others to be able to
 admire. In such cases, where the
 targets of a program's components
 One key to achieving this
 gramming, music, and poetry--
 brain -- are naturally structured in
 levels. Sounds (phonemes)
 form words; words group into
 paragraphs, and these are
 musical phrases, which form
 movements, which form compositions.
 The structure in programming practice brings different
 level is the ascii character
 --- OCR End ---
 --- OCR Start ---
 6
 Then program statements,
 advice is simply be clear.
 momentarily be proud of y
 k=(2-j)*(1+3*j)/2;
 if you want to permute cyc
 k = (1,2,0). You will re
 line. Better, and likely al
 k=j+1;
 if (k == 3) k=0;
 Many programming stylists
 switch (j) {
 case 0: k=1; break
 case 1: k=2; break
 case 2: k=0; break
 default: {
 fprintf(stderr
 exit(1);
 }
 }
 on the grounds that it is both
 tions about the possible va
 is for the middle one.
 In this simple exampl
 Statements frequently com
 as a whole. The middle fra
 swap=a[j];
 a[j]=b[j];
 b[j]=swap;
 which makes immediate se
 while
 ans=sum=0.0;
 n=1;
 is very likely to be an initia
 level of hierarchy in a prog
 practice to put in comments
 The next level is that
 construction in the exampl
 important, and relevant to
 we will come back to it j
 At still higher levels i
 whole "global" organizatio
 analogy, we are now at the
 --- OCR End ---
 --- OCR Start ---
 1.1 Program
 modularization and encapsulation: the
 general idea being that programs are built
 clearly defined and narrowly circumscribed
 is an essential prerequisite, especially for
 especially those employing a more formal
 practice (if not quite as essential a
 individual scientist, or reader of
 Some computer languages offer modular-
 ization with higher-level language
 functions, type definitions, and other features
 that communicate through well-defined
 are hidden from the rest of the program.
 is "class," a user-definable data
 automatic initialization of data, and data
 overloading (i.e., the user-defined
 appropriate to operands in a particular
 structures that are passed between
 these units' public interfaces. This
 allowing a considerable degree of
 Beyond modularization, object-
 oriented programming.  Here,
 5.5 [6], allows a module's procedures
 and these redefinitions become
 hierarchy (so-called polymorphism).
 of real numbers could—dynamically—
 numbers by overloading conventional
 arithmetic operations. Additionally, a
 type that "inherits" all the features of its
 own), and object extensibility (i.e.,
 access to its source code, etc.) are available.
 We have not attempted to create a set
 book, for at least two reasons. First, it is
 this possible. Second, we
 the algorithms in this book are presented in
 of your own choosing. The use
 of "classes" for scientific objects is not
 invent such a set, doing so would detract from
 book (which is its raison d'être). Thus, our
 of choices regarding class structure are
 On the other hand, we do make use of
 oriented programming. We encourage
 our programs to be "object-oriented," meaning
 C with its function prototypes, is a suitable
 our implementation section shows the
 structured programming, a
 --- OCR End ---
 --- OCR Start ---
 8
 Control Structures
 An executing program
 which the statements are where
 statements are executed, or
 control statements. Control
 make sense only in the context
 control. If you think of the
 control statements are perhaps
 and the punctuation between
 We can now say what
 program control manifestly
 see that this goal has nothing
 As already remarked, comp
 or not. Human readers, however,
 discover how much easier it is to
 one whose control structures
 You accomplish the goal in two
 ways. First, you acquaint yourself with
 structures that occur over and over again.
 given convenient representations
 to think about your program's structure,
 these standard control structures,
 of representing these standard
 "Doesn't this inhibit
 as Mozart's creativity was
 metrical requirements of the
 communicate, does well under
 Second, you avoid, in
 blocks or objects are difficult to
 must try to avoid named labels. They
 are dangerous (although the
 statement labels are the hazard, a
 label while reading a program,
 feeling in the pit of your stomach
 habit, immediately spring to
 label? It could be anywhere
 to this label? They could be
 dissolves into a morass of
 Some examples are now
 (see Figure 1.1.1).
 Catalog of Standard
 Iteration. In C, simply
 for (j=2;j<=1000;j++)
 {
 b[j]=a[j-1];
 a[j-1]=j;
 }
 --- OCR End ---
 --- OCR Start ---
 1.1 Program
 iteration
 complete?
 no
 block
 increment
 index
 FOR iteration
 (a)
 block
 true
 while
 condition
 false
 DO WHILE iteration
 (c)
 Figure 1.1.1. Standard control statements; (a) for iteration; (c) do while iteration;
 --- OCR End ---
 --- OCR Start ---
 10
 if
 condition
 false
 else
 condition
 true
 block
 block
 condition
 match
 no
 condition
 match
 no
 Figure 1.1.1. Standard control structures.
 --- OCR End ---
 --- OCR Start ---
 1.1 Program
 Notice how we always indent the
 structure, leaving the structure's
 initial curly brace on the same line.
 This saves a full line of whitespace.
 FORTRAN and other languages use an
 IF structure. This is different from
 if (...) {
 ...
 }
 else if (...) {
 ...
 }
 else {
 }
 Since compound-statements are more than
 one statement in a block, the code is more
 explicit than the corresponding logic
 exercised in constructing nested IFs.
 if (b > 3)
 if (a > 3) b += 1;
 else b -= 1;
 As judged by the indentation,
 this code is the following: if $b$ is
 increment $b$. If $b$ is not greater than 3,
 of C, however, the actual meaning is that
 greater than 3, then increment $b$. The
 point is that an else clause is not needed;
 no matter how you lay it out in C, it's
 resolved by the inclusion of the curly braces.
 superfluous; nevertheless, the above
 above fragment should be written as:
 if (b > 3) {
 } else {
 if (a > 3) b += 1;
 b -= 1;
 }
 Here is a working program:
 #include <math.h>
 #define IGREG (15+31L*(10+
 long julday(int mm, int id, int iyyy)
 In this routine julday returns the
 specified by month mm, day id, and year iyyy.
 negative, B.C. Remember that
 {
 void nrerror(char erro
 --- OCR End ---
 --- OCR Start ---
 12
 long jul;
 int ja, jy=iyyy,jm;
 if (jy == 0) nrerror("
 if (jy < 0) ++jy;
 if (mm > 2) {
 jm=mm+1;
 } else {
 --jy;
 jm=mm+13;
 }
 jul = (long) (floor(36
 if (id+31L*(mm+12L*iyy
 ja=(int)(0.01*jy);
 jul += 2-ja+(int)
 }
 return jul;
 (Astronomers number
 a unique integer, the Julia
 time ago; a convenient ref
 of May 23, 1968. If you
 given calendar date, then
 1 and taking the result mo
 Monday, ..., 6 to Saturd
 While iteration.
 for structures like the follo
 while (n < 1000) {
 n *= 2;
 j += 1;
 }
 It is the particular feature
 n < 1000) is evaluated be
 statements will not be exec
 when n is greater than or equ
 Do-While iteration.
 structure that tests its con
 like this:
 do {
 n *= 2;
 j += 1;
 } while (n < 1000);
 In this case, the enclosed
 of the initial value of n.
 Break. In this case
 condition tested somewher
 --- OCR End ---
 --- OCR Start ---
 1.1 Program
 than one place) becomes true
 with what comes after it. In
 statement, which terminate
 construction and proceeds to
 FORTRAN, this structure requires
 programming.) A typical use is
 for(;;) {
 [statements before
 if (...) break;
 [statements after
 }
 [next sequential instruction
 Here is a program that
 once asked, for a scavenger hunt, how many times the
 moon was full. This is a program to compute the number of
 all other Fridays the 13th
 #include <stdio.h>
 #include <math.h>
 #define ZON -5.0
 #define IYBEG 1900
 #define IYEND 2000
 int main(void) /* Program to count full moons on Friday the 13th */
 {
 void flmoon(int n, int *j, int *ic);
 long julday(int mm, int id, int iy);
 int ic, icon, idwk,im,iy,iyyy,n;
 float timzon = ZON/24.;
 long jd, jday;
 printf("\nFull moons on Friday the 13th since 1900:\n");
 for (iyyy=IYBEG;iyyy<=IYEND;iyyy++) {
 for (im=1;im<=12;im++) {
 jday=julday(im,13,iyyy);
 idwk=(int) ((julday(im,13,iyyy)-1)%7);
 if (idwk == 5) {
 n=(int) (12.37*iyyy-3673.5);
 This value n is an approximation to the number of full moons
 since 1900.
 until we determine the precise number in the following steps.
 variable icon
 icon=0;
 for (;;) {
 flmoon(n,&j,&ic);
 frac=24.*(j-n);
 if (frac < 0.) {
 --j;
 frac=24.*(j-n);
 }
 if (frac >= 12.) {
 ++j;
 frac=24.*(j-n);
 } else
 frac=frac;
 if (jd == jday)
 printf("%d %d\n",iyyy,im);
 printf("%d\n",icon);
 }
 --- OCR End ---
 --- OCR Start ---
 14
 } else
 {
 ic=
 if
 ico
 n+
 }
 }
 }
 }
 }
 return 0;
 }
 If you are merely curious about dates like Friday the 13th (time zone is irrelevant), then consider these dates: 1/13/1922, 11/13/1970, 2/13/1981.
 Other "standard" structures in many programming languages have some sort of resist throwing in. They seem simple enough but they don't stand the test of time as well as some other languages, and difficult to read (or to understand the reader). You can almost always find other ways to construct structures in other ways.
 In C, the most problematic is the if...else construction (see Figure 1.1). The differences go from compiler to compiler, and even within one compiler, Data types char and int are sometimes treated differently than the structure should be from if...else construction. A few compilers allow the continue; construction, but many older compilers do not understand the if construction with no logical test.
 About "Advanced Techniques"
 Material set in smaller type is intended for the main argument of the chapter, or for readers with a strong mathematical background, or for readers who already have a detailed understanding of the algorithm that is less well-tested; such material is usually omitted from topics on a first reading of the book.
 You may have noticed that all of the examples in the book avoids using any algorithm for converting the Gregorian calendar date to a Julian day, and the routine for doing just this is not described here.
 #include <math.h>
 #define IGREG 2299161
 void caldat (long julian, int *mm, int *id, int *iy)
 {
 Inverse of the function julday (see Appendix A), and the routine outputs mm, id, and iy, where Julian Day started at noon.
 {
 long ja, jalpha,jb,jc,j
 --- OCR End ---
 --- OCR Start ---
 1.2 Some C
 if (julian >= IGREG) {
 jalpha=(long) (((do-
 ja=julian+1+jalpha
 } else if (julian < 0)
 ja=julian+36525*(1
 } else
 ja=julian;
 jb=ja+1524;
 jc=(long) (6680.0+((dou
 jd=(long) (365*jc+(0.25
 je=(long) ((jb-jd)/30.6
 *id=jb-jd-(long) (30.6
 *mm=je-1;
 if (*mm > 12) *mm = 1
 *iyyy=jc-4715;
 if (*mm > 2) --(*iyyy)
 if (*iyyy <= 0) --(*iy
 if (julian < 0) *iyyy
 }
 (For additional calendric
 CITED REFERENCES AND F
 Harbison, S.P., and Steele, G.
 NJ: Prentice-Hall).
 Kernighan, B.W. 1978, The Ele
 Yourdon, E. 1975, Techniques
 Hall). [2]
 Jones, R., and Stewart, I. 1987
 Hoare, C.A.R. 1981, Communi
 Wirth, N. 1983, Programming i
 Stroustrup, B. 1986, The C++
 Borland International, Inc. 1985
 Valley, CA: Borland Inter
 Meeus, J. 1982, Astronomical
 mond, VA: Willmann-Bell
 Hatcher, D.A. 1984, Quarterly
 also op. cit. 1985, vol. 26
 1.2 Some C Co
 Computing
 The C language was de
 scientific computing. Rela
 the programmer "very clos
 giving direct access to mo
 has a large variety of intr
 integers; floating and dou
 syntax for effecting convers
 (addresses) that relates grac
 the index register structure
 --- OCR End ---
 --- OCR Start ---
 16
 Portability has always
 underlying language of the
 operating system have by reason
 computers. The language's
 increasing numbers of scientists
 real-time control of experiments
 UNIX kernel is less than ideal.
 The use of C for high-level
 modeling, and floating-point
 In part this is due to the experience of
 virtually all scientists and engineers; in
 part, also, the slowness of C and the
 deficiencies in the language make it
 slow to recognize. Examples are
 integer powers, and the "in-line"
 below. Many, though not all, are non-
 Standard. Some remaining
 Yet another inhibition
 up to the time of writing,
 libraries. That is the lacunae in
 We certainly do not claim
 to inspire further efforts, and
 conventions for scientific computation
 The need for programs
 of overcoming constraints
 Pascal), the problem in C is that the
 multiple opportunities — a
 from program to program.
 and describe the adopted conventions
 Function Prototype

 ANSI C allows function
 the type of each function
 a prototype is visible, the
 the function with the correct
 are in ANSI C prototype form.  For
 K&R" C compilers, the numerous
 programs, one in ANSI, the
 The easiest way to understand
 that would be written in the
 int g(x,y,z)
 int x,y;
 float z;
 becomes in ANSI C
 --- OCR End ---
 --- OCR Start ---
 1.2 Some C
 int g(int x, int y, float)
 A function that has no parameters.
 A function declaration, or "prototype", is a way to
 "introduce" a function to a compiler before the
 to know the number and types of its parameters.  In
 a function declaration, you need only to list the
 declaration for the above function would be
 int g(int, int, float)
 If a C program consists of more than one source file, the
 consistency of each function's declaration and definition, or the
 way to proceed is as follows:
 • Every external function must be declared in a
 header (.h) file.
 • The source file will then include this header file and
 include the header file's declaration and definition.
 • Every source file that contains a function definition must
 header (.h) file.
 • Optionally, a routine might also have a secondary
 prototype declaration within the source file where it is used. This is especially
 developing a program that must go through a preprocessor, and also
 the compiler through separate passes.
 Later, after your program is compiled, you may find the use of
 supernumary intermediate files to be cumbersome and inconvenient.
 For the routines in this book, the single-source file method
 listed in Appendix A. You should organize your program so that
 every source file that contains a routine definition also contains the
 than not, you will want to create a separate source file for each routine.
 single source file, we have adopted the single-source file method because
 book's individual program development methodology. This makes the
 your programs.
 As backup, and in accordance with the single-source file approach,
 we declare the function prototypes.  This is also done because
 by other Numerical Recipes programs.  The single-source file approach
 makes our routines much more easily portable.  The number of lines is also reduced
 the small number of utility routines which might be needed for each individual program.  These utilities are
 declared in the additional header files. The names of these utilities
 is explicitly printed whenever the routine that uses them is compiled.
 A final important point that should be emphasized is that
 the diskette, it contains both ANSI and NRANSI versions of this source code.  The
 ANSI forms are invoked if the code is being compiled with an
 ANSI, or NRANSI. (The purpose of having both forms of this code is that
 does not conflict with other user-defined variable names.  For all those who use an
 ANSI compiler, it is essential to compile using this particular standard.
 --- OCR End ---
 --- OCR Start ---
 18
 defined. The typical mean
 the compiler command lin
 Some further details a
 Vectors and One-Di
 There is a close, and e
 The value referenced by a
 that is, "the contents of t
 j." A consequence of thi
 the array element a[0] is
 or "zero-offset." An array
 references b [0], b[1], b[
 Right away we need a
 index. (The issue comes
 example, the index range
 borrowed from Pascal.
 a[M]; is a [0.. M-1],
 One problem is that
 from 0 to M-1. Sure, yo
 a baggage of additional ari
 better to use the power of t
 disappear. Consider
 float b[4], *bb;
 bb=b-1;
 The pointer bb now points
 the array elements bb [1],
 range of bb is bb [1..4].
 B for some additional disc
 It is sometimes conver
 to use unit-offset vectors i
 natural to the problem at
 $a_0 + a_1 x + a_2 x^2 + ... +$
 a vector of N data points 2
 routine in this book has an
 the expected index range.
 void someroutine (float
 This routine does somethi
 Now, suppose you wa
 of length 7, say. If your ve
 aa [1..7]), then you can in
 the recommended procedur
 or at least aesthetic, reasor
 --- OCR End ---
 --- OCR Start ---
 1.2 Some C
 But suppose that your
 zero-offset array (has range
 with our aesthetic prejudice
 copy a's contents element by
 have to declare a new point
 someroutine(a-1,7);.
 a[0] as seen from your program,
 the "fly" with just a couple of
 Forgive us for belaboring
 thinking that C encourages
 is that the utility file nrutil.c
 for allocating (using malloc)
 synopses of these functions:
 float *vector(long nl,
 Allocates a float vector
 int *ivector(long nl,
 Allocates an int vector with
 unsigned char *cvector
 Allocates an unsigned char
 unsigned long *lvector
 Allocates an unsigned long
 double *dvector(long m
 Allocates a double vector
 A typical use of the array
 b = vector(1,7);, which may
 b to be passed to any function.
 The file nrutil.c also
 void free_vector(float
 void free_ivector(int
 void free_cvector(unsigned
 void free_lvector(unsigned
 void free_dvector(double
 with the typical use being
 Our recipes use the above
 of vector workspace. We also
 other procedures. Note that
 on an IBM PC-compatible
 in nrutil.c by your compiler.
 applies also to matrix allocation.
 --- OCR End ---
 --- OCR Start ---
 20
 Matrices and Two-Dimensional Arrays
 The zero- versus unit-
 a moment in favor of an evident
 arrays (FORTRAN terminology)
 are arrays that need to be
 about their two-dimensional
 dimensional arrays, and almost all
 is variable and known only
 butter of scientific computing
 that could work with only
 There is no technical reason.
 void someroutine(a,m,n)
 float a[m][n];
 and emit code to evaluate the
 expression) each time some
 forbidden by the C language
 in C instead requires some
 rewarded for the effort.
 There is a subtle nearness of
 references. Let us elucidate
 array reference to a (say)
 that evaluate to type int.
 this reference, depending
 declared as a fixed-size array
 the address a add 9 times i
 the constant 9 needs to be
 multiplication is required
 Suppose, on the other
 the machine code for a[i]
 addressed as a new address
 address." Notice that the usual
 at all, and that there is no
 thus have, in general, a fast
 price that we pay is the storage
 of a [][] ), and the slight increase
 when we declare an array
 Here is our bottom line
 being unsuitable data structure
 adopt instead the convention
 pointing to the first element
 rejected and adopted scheme
 The following fragment
 converted to a "pointer to
 --- OCR End ---
 --- OCR Start ---
 (a)
 **m
 1.2 Some C
 **m ---*m[0]
 *m[1]
 *m[2]
 (b)
 Figure 1.2.1. Two storage schemes.
 lines connect sequential memory
 to an array of pointers to rows; t
 float a [13] [9],**aa;
 int i;
 aa=(float **) malloc(C
 for(i=0;i<=12;i++) aa[i]
 The identifier aa is now a name;
 or modify its elements ad libitum;
 to any function by its name and
 dummy argument as float **aa;
 knowing its physical size.
 You may rightly not worry about
 fragment. Also, there is some
 indices, so that (for example)
 a [1..13] [1..9]. Both of these
 in nrutil.c (Appendix E) are
 range. The synopses are
 float **matrix (long nr, long nc)
 Allocates a float matrix
 double **dmatrix (long nr, long nc)
 Allocates a double matrix
 int **imatrix(long nrl, long nc)
 Allocates an int matrix w
 void free_matrix(float **m, long nr)
 Frees a matrix allocated w
 --- OCR End ---
 --- OCR Start ---
 22
 void free_dmatrix(double
 Frees a matrix allocated
 void free_imatrix(int
 Frees a matrix allocated
 A typical use is
 float **a;
 a=matrix(1,13,1,9);
 a[3][5]=...
 ...+a[2][9]/3.0...
 someroutine(a,...);
 free_matrix(a,1,13,1,9);
 All matrices in Numerical
 commend it to you.
 Some further utilities
 The first is a function sub
 already-existing matrix (or
 Its synopsis is
 float **submatrix(float
 long oldch, long n
 Point a submatrix [newr]
 the existing matrix range
 Here oldrl and oldrh are
 original matrix that are to be
 the corresponding column
 column indices for the new
 since they are implied by t
 Two sample uses might
 [1..2] some interior rang
 float **a, **b;
 a=matrix(1,13,1,9);
 b=submatrix(a,4,5,2,3,
 and second, to map an
 b[0..12][0..8],
 float **a, **b;
 a=matrix(1,13,1,9);
 b=submatrix(a,1,13,1,9
 --- OCR End ---
 --- OCR Start ---
 1.2 Some C
 Incidentally, you can use sizeof (float)
 is the same as sizeof (float **) and cast
 to type float ** and cast
 The function
 void free\_submatrix(float ***)
 frees the array of row-pointers and
 the memory allocated to the matrix.
 the memory allocation of
 Finally, if you have a
 want to convert it into a matrix,
 the following function does this:
 float \*\*convert\_matrix(long, long);
 Allocate a float matrix m
 standard C manner as a [n] [m] array. This
 routine should be called with
 (You can use this function
 to set values for a matrix,
 book.) The function
 void free\_convert\_matrix(float \*\*);
 Free a matrix allocated by
 frees the allocation, without
 The only examples of
 pointer-to-pointer structure
 sfroid in §17.4. The necessary
 float \*\*f3tensor(long, long, long);
 Allocate a float 3-dimensional
 void free\_f3tensor(float \*\*\*,
 long ndl, long ndh);
 Free a float 3-dimension
 Complex Arithmetic
 C does not have complex
 complex numbers. That of
 the file complex.c which
 A synopsis is as follows:
 --- OCR End ---
 ```
 typedef struct FCOMPLE
 fcomplex Cadd(fcomplex
 Returns the complex sum
 fcomplex Csub(fcomplex
 Returns the complex diffe
 fcomplex Cmul(fcomplex
 Returns the complex prod
 fcomplex Cdiv(fcomplex
 Returns the complex quot
 fcomplex Csqrt(fcomple
 Returns the complex squa
 fcomplex Conjg(fcomple
 Returns the complex conj
 float Cabs(fcomplex z)
 Returns the absolute valu
 fcomplex Complex(float
 Returns a complex numbe
 fcomplex RCmul(float x
 Returns the complex prod
 The implementation o
 arithmetic is not entirely t
 Only about half a doze
 arithmetic functions. The re
 the familiar operations +-+*
 the C language allows oper
 code. However, in this boo
 We should mention th
 and assign structures like
 to be structures) by value.
 the original K&R C definit
 functions in complex.c, m
 fcomplex instead of the v
 the recipes that use the fu
 Several other routine
 complex arithmetic "by han
 float variables. This resul
 the functions in complex.
 ideal solution to the comp
 Implicit Conversion
 In traditional (K&R) C
 before any operation is atte
 as arguments to functions.
 float variable receives the

 ```
 --- OCR Start ---
 1.2 Some C
 is immediately thrown away
 standard C library functions
 The justification for this
 a little extra precision," and
 function." One does not need
 that the implicit conversion
 impossible to write efficient
 separates computer scientists'
 point of view on whether a
 many real-time or state-of-the-art
 The practical scientist is
 computer; the computer scientist
 The ANSI C standard
 operations, but it does require
 prototyped by an ANSI declaration.
 another reason for our being
 and a good reason for you
 Some older C compilers
 the implicit conversion of
 In this book, when we write
 we mean `double`, i.e., the
 precision. Our routines are
 but they are more efficient
 requires double precision,
 without difficulty. (The best
 `#define float double`
 A Few Wrinkles
 We like to keep code
 immediate clarity. We usually
 Through a quirk of history,
 operator `"-="` as being equivalent
 `"*=` as being the same as the
 you will see us write `v = - -v`.
 We have the same view
 (or read) C effectively unless
 rules. Please study the accompanying
 We never use the register
 are quite sophisticated in many
 and the best choices are so
 Different compilers use
 and referencing declarations
 the most common scheme
 `extern` is explicitly included
 class is omitted from the structure
 have commented these declarations.
 you can change the code.  They
 --- OCR End ---
 --- OCR Start ---
 26
 \begin{tabular}{|c|c|}
 \hline
 Opera & \\
 \hline
 \( \) & \\
 \( [ ] \) & \\
 \(. \) & \\
 \( -> \) & \\
 \hline
 \( ! \) & \\
 \( ~ \) & \\
 \( - \) & \\
 \( ++ \) & \\
 \( -- \) & \\
 \( \& \) & \\
 \( * \) & \\
 \( (type) \) & \\
 \( sizeof \) & \\
 \( * \) & \\
 \( / \) & \\
 \( \% \) & \\
 \hline
 \( + \) & \\
 \( - \) & \\
 \hline
 \( << \) & \\
 \( >> \) & \\
 \hline
 \( < \) & \\
 \( > \) & \\
 \( <= \) & \\
 \( >= \) & \\
 \hline
 \( == \) & \\
 \( != \) & \\
 \hline
 \( \& \) & \\
 \( \sim \) & \\
 \( | \) & \\
 \hline
 \( \&\& \) & \\
 \hline
 \( || \) & \\
 \hline
 \( ? : \) & \\
 \hline
 \( = \) & \\
 \( also \) & \( += -= \) \\
 \(  \)& \( <<= >>= \) \\
 \hline
 \( , \) & \\
 \hline
 \end{tabular}
 We have already alluded to certain kinds of numbers, most notably the integers.  This is perhaps the language's most distinctive feature. FORTRAN compilers recognize integers in this case with only one sign and powers up to 12 to be thus
 --- OCR End ---
 --- OCR Start ---
 1.2 Some C
 In C, the mere problem
 the operation as
 #define SQR(a) ((a)*(a)
 However, this is likely to produce
 the sine routine! You might consider a
 squaring function in a temporary
 static float sqrarg;
 #define SQR(a) (sqrarg
 The global variable sqrarg,
 module, which is a little dangerous,
 square expressions of type
 SQR operations in a single expression
 the expression is at the compiler
 of SQR can be that from the
 nonsensical results. When
 following, which exploits the
 a conditional expression:
 static float sqrarg;
 #define SQR(a) ((sqrarg
 A collection of macros for
 (see Appendix B) and used
 SQR(a)
 DSQR(a)
 FMAX(a,b)
 FMIN(a,b)
 DMAX(a,b)
 DMIN(a,b)
 IMAX(a,b)
 IMIN(a,b)
 LMAX(a,b)
 LMIN(a,b)
 SIGN(a,b)
 Scientific programming
 watch out for the thorns!
 CITED REFERENCES AND FURTHER
 Harbison, S.P., and Steele, G.
 NJ: Prentice-Hall). [1]
 AT&T Bell Laboratories 1985,
 Hall).
 Kernighan, B., and Ritchie, D
 Prentice-Hall). [Reference
 the ANSI C standard.]
 Hogan, T. 1984, The C Program
 --- OCR End ---
 --- OCR Start ---
 28
 1.3 Error, Accuracy, and Precision

 Although we assume numbers are stored exactly, we will need to presume a degree of error.  We define these briefly in this section.

 Computers store numbers in a binary representation that can be packed into a fixed number of bits (e.g., 32 bits or 64 bits). Almost all computers use some form of floating-point representation rather than integer representation. The different such representations have implications for error analysis (see section 1.3.1). For example, a number in integer representation is always exactly representable. A number in floating-point representation (float or double) format is only representable to a limited degree of accuracy. A number in integer representation is also constrained by its range (usually, signed 32-bit integers ranging from -2147483648 to 2147483647). A floating-point number is interpreted as producing a value of the form

 $s \cdot B^{E-e} \cdot M$,

 where $B$ is the base of the number system (usually 2), and $E$ is the bias of the exponent and $M$ is the mantissa. The bias is subtracted from the actual value of the exponent in order to allow for both positive and negative exponents in the representation. An example of the value of a floating-point number is given below. Several floating-point representations exist, but this description encompasses many of them. For example, a mantissa with 23 bits can represent 2<sup>23</sup> numbers, which when multiplied by a power of 2, can represent the full range of numbers that are “as less than a power of 2 away from each other.  Bit patterns that are “as less than a power of 2 away from each other” means that these numbers are within half a step of each other. Computers always produce a floating-point number with a properly normalized mantissa and thus allow an easy comparison. The high-order bit of a properly normalized mantissa is always a 1 (the implicit bit). Computers don’t store this high-order bit.

 Arithmetic among numbers is not necessarily exact.  If the operands happen to be exactly represented, but their sum is not exactly representable (as in the case when the sum of two operands is more than the machine can store), the result is rounded to the nearest floating-point number. For example, if two floating-point numbers differ by many orders of magnitude (such as $10^{15}$ versus 1), then the smallest number is essentially ignored by the computer. The process is called “rounding” to the nearest floating-point number. If the sum of two numbers is outside the range that can be stored by the computer, an error occurs. If the operands happen to be exactly representable, their sum or difference is rounded to the nearest representable number; their product or quotient is also rounded.  If, however, the operands are not exactly representable, then rounding to the nearest representable number is done. This rounding may cause small errors to occur in the result.  In the case where the operands differ too greatly in magnitude, the smaller number may be replaced by zero. For example, when adding $10^{15}$ and 1, the result is $10^{15}$ since the least significant bits of the smaller number are lost during addition. If the operands differ too greatly, then we replace the smaller of the two operands by zero.  Since it is not stored, we can only compare two floating-point numbers with a certain degree of accuracy.

 The smallest (in magnitude) non-zero floating-point number is $1.0 \cdot 2^{-126}$, termed the machine accuracy, $\epsilon_m$. The wordlength of the floating-point representation and the base of the number system determine the machine accuracy $\epsilon_m$.  A wordlength has $\epsilon_m$ around $2^{-23}$, which is approximately $1.2 \times 10^{-7}$.  The machine accuracy has several characteristics, and a program may take advantage of these characteristics.
 --- OCR End ---
 --- OCR Start ---
 1.3
 $\overbrace{\text{sign bit}}^{}$
 $\overbrace{\text{8-bit exponent}}^{}$
 $1/2 = 0$   $1\ 0\ 0\ 0\ 0\ 0\ 0$
 $3 = 0$   $1\ 0\ 0\ 0\ 0\ 0\ 0$
 $1/4 = 0$   $0\ 1\ 1\ 1\ 1\ 1\ 1$
 $10^{-7} = 0$   $0\ 1\ 1\ 0\ 1\ 0$
 $= 0$   $1\ 0\ 0\ 0\ 0\ 0\ 0$
 $3 + 10^{-7} = 0$   $1\ 0\ 0\ 0\ 0\ 0\ 0$
 Figure 1.3.1. Floating point representation of the number 1/2 (note the bias in the exponent).  $10^{-7}$, represented to machine accuracy, has an exponent as the number 3; with the addition of a common exponent must occur which equals 3 to machine accuracy and must accurately be added to a much larger number.

 speaking, the machine accuracy with which numbers are represented, comes from the last bit of the mantissa. Pretty obviously, this should be thought of as introducing a type of error is called roundoff.  It is important to understand that the numbers that can be represented on a machine are in the exponent, while all the rest are in the mantissa.  Roundoff errors accumulate in a curious course of obtaining a calculation. You might be so lucky as to have the roundoff errors come in a random-walk.) However, this is not typical. (i) It very frequently happens that peculiarities of your computer's arithmetic push errors in one direction. In this case, the errors are cumulative. (ii) Some especially unpleasant types of error of single operations. Very nearly equal numbers, in particular (few) low-order ones in which a "coincidental" subtraction occurs, can cause expressions magnify its problems. A familiar formula for the solution will follow.

 the addition becomes delicate; and in the next section we will learn how to avoid these problems.
 --- OCR End ---
 --- OCR Start ---
 30
 Roundoff error is a completely different, kind of error that is independent of the hardware.  Algorithms compute “discrete” values. For example, an integral is approximated by evaluating it at a discrete set of points, then the integral is evaluated by summing a finite number of terms, rather than all infinity terms. In other words, as the number of points or of terms in a sum (or other parameter) goes to infinity, the choice converges to the value that it would obtain if it were sufficiently large, choice can affect the result. The discrepancy between the numerical result of a calculation and the true value which would have been obtained in the hypothetical, “perfect” computation is called the true roundoff error. As a general rule, however, roundoff error, other than to use the most sophisticated numerical methods (see discussion of “stability” below), is considered under the programmer’s control. It turns out that there is often clever minimization of roundoff error in the field of numerical analysis.

 Most of the time, true values are so close to one another. A calculation of a true value can be compared with one another. A calculation of the true value that it would have if run on a "perfect" machine, only associated with the number.

 Sometimes, however, roundoff errors can successively magnify and cancel each other, making it necessary for us to be more careful, means that any roundoff error that occurs at any stage is successively magnified. Thus it can be that a more sophisticated method would be useful or required in this world. Here is a simple example, if such a situation should occur, we use them with greater care. It turns out that there is often a clever minimization of roundoff error in this world. It is necessary for us to use them with great care.

 Suppose that it is desired to find the mean of two numbers. We shall call “Mean,” the number given by

 It turns out (you can easily verify this) that this is not a linear relation,

 Thus, knowing the first two terms of the Fibonacci sequence, we can apply (1.3.4) performing on them repeatedly by $\phi$, at each stage.

 Unfortunately, the recursion relation has a multiplier $- \frac{1}{2} (\sqrt{5} + 1)$. Since the reciprocal of this multiplier has a magnitude greater than unity, any roundoff error will grow exponentially. On the other hand, it can be shown that the roundoff error in the first approximation to the mean of two numbers will always decrease.

 --- OCR End ---
 1.3
 to give completely wrong answers for $x \ge 4$. The recurrence (1.3.2) is not stable. We will encounter these numerical difficulties later in this book.

 CITED REFERENCES AND FURTHER READING

 Stoer, J., and Bulirsch, R. 1980, Introduction to Numerical Analysis (New York: Springer-Verlag), Chap. 1.
 Kahaner, D., Moler, C., and Nash, S. 1989, Numerical Methods and Software (Englewood Cliffs, NJ: Prentice Hall), Chap. 1.
 Johnson, L.W., and Riess, R.D. 1982, Numerical Analysis (Reading, MA: Addison-Wesley), §1.3.
 Wilkinson, J.H. 1964, Rounding Errors in Algebraic Processes (Englewood Cliffs, NJ: Prentice-Hall).
 Chapter 2.

 2.0 Introduction

 A set of linear algebra
 $a_{11}x_1$
 $a_{21}x_1$
 $a_{31}x_1$
 $a_{M1}x_1 + $

 Here the $N$ unknowns $x_j$
 coefficients $a_{ij}$ with $i = 1$
 are the right-hand side qua

 Nonsingular versus

 If $N = M$ then there
 chance of solving for a un
 be a unique solution if one
 the others, a condition cal
 variables only in exactly th
 (For square matrices, a ro
 versa.) A set of equations
 singular matrices in some
 Numerically, at least
 • While not exact lin
 may be so close to
 render them linearl
 this case your num
 has failed.
 --- OCR Start ---
 • Accumulated round
 solution. This procedure
 numerical procedure uses a
 set of $x$'s that are weighted
 into the original equations;
 the more likely this process
 will occur during the course of
 as the special case where
 Much of the sophistication
 is devoted to the detection of
 work with large linear sets. This
 sophistication is needed. It is not
 such thing as a "typical" linear
 $N$ as large as 20 or 50 can be
 representations) without resorting
 close to singular. With double precision
 be extended to $N$ as large as
 is generally machine time.
 Even larger linear sets whose
 coefficients are sparse (that is, the
 sparseness. We discuss the
 problems which, by their unfortunate
 might need to resort to sophisticated
 rarely for $N = 5$). Singular problems
 sometimes turn singular problems. This
 sophistication becomes unnecessary.
 Matrices
 Equation (2.0.1) can be written
 Here the raised dot denotes matrix
 b is the right-hand side where
 $A = \begin{bmatrix} a_{11} \\ a_{21} \\ \vdots \\ a_{M1} \end{bmatrix}$
 By convention, the first subscript
 index its column. For most
 in a computer's physical memory, these
 two-dimensional addresses are such that
 that this C notation can in some cases be
 scheme, "pointer to array of"
 --- OCR End ---
 --- OCR Start ---
 34
 Chapter

 at this point. Occasionally
 to pass a whole row a[i]
 Tasks of Computation
 We will consider the
 chapter:
 • Solution of the matrix equation Ax = b, where A
 is a square matrix of order N and b is a known right-hand
 • Solution of more than N equations in N unknowns
 xj, j = 1, 2, ..., each equation being of the form
 $\sum_{i=1}^N a_{ji}x_i = b_j$. In this type of problem the
 constant, while the
 • Calculation of the matrix inverse A−1 of a matrix
 A, i.e., A ⋅ A−1 = I, where I is the unit matrix (a matrix
 except for ones on the principal diagonal), or else a
 matrix A, to the product of A by the inverse A−1 of
 namely the unit vector, and an arbitrary constant (the
 component). The calculation of the matrix
 inverse of A (§2.1) is considered first.
 • Calculation of the characteristic equation of a matrix.

 If M < N, or if M > N, i.e., if there are
 effectively fewer equations than unknowns in the
 solution, or else more than N equations, then the solution
 consists of a particular solution plus a linear combination of
 N − M vectors (which are linearly independent) spanning
 of finding the solution space.
 • Singular value decomposition of a matrix.

 This subject is treated in Chapter 10.
 In the opposite case that M = N, if a solution exists,
 this occurs there is, in general, just one solution.  A system
 of equations is said to be consistent if there is at least one
 best "compromise" solution in the case of more equations than unknowns.
 equations simultaneously. In other words, a best solution minimizes
 the sum of the squares of the residuals, that is, we require the
 equation (2.0.1) be minimized.  This yields a system of equations (usually) solvable linear least-squares solutions
 • Linear least-square solution of overdetermined linear equations.

 The reduced set of equations is given by
 where AT denotes the transpose of A; these are called the
 normal equations of the linear least-squares problem.
 --- OCR End ---
 between singular value dec
 latter is also discussed in
 normal equations (2.0.4) is
 Some other topics in
 • Iterative improvem
 • Various special for
 (§2.4), band diagon
 (§2.7)
 • Strassen's "fast ma
 Standard Subroutines
 We cannot hope, in this
 know about the tasks that have
 alternative but to use sophisticated
 are available, though not always
 Laboratories and deserves
 and available for free use.
 available. Packages available
 those in the IMSL and NAG.
 You should keep in mind
 large linear systems in mind, the
 the number of operations.
 tasks are usually provided
 simplifications in the form
 banded, positive definite, etc.
 you should certainly take advantage of
 different routines, and not just
 There is also a great deal of
 in a predictable number of iterations
 to converge to the desired solution.
 methods become preferable,
 of being lost, either due to roundoff error.
 will treat iterative methods
 18 and 19. These methods
 however, discuss in detail
 and iterative methods, namely those
 obtained by direct methods.
 CITED REFERENCES AND FURTHER READING
 Golub, G.H., and Van Loan, C.F.
 University Press).
 Gill, P.E., Murray, W., and Wright, M.H.
 (Redwood City, CA: Addison-Wesley).
 Stoer, J., and Bulirsch, R. 1980
 Chapter 4.
 Dongarra, J.J., et al. 1979, LIN

 36
 Chapter

 Coleman, T.F., and Van Loan, C
 Forsythe, G.E., and Moler, C.E
 wood Cliffs, NJ: Prentice
 Wilkinson, J.H., and Reinsch,
 putation (New York: Sprin
 Westlake, J.R. 1968, A Handbo
 (New York: Wiley).
 Johnson, L.W., and Riess, R.
 Wesley), Chapter 2.
 Ralston, A., and Rabinowitz, P.
 McGraw-Hill), Chapter 9.

 2.1 Gauss-Jord

 For inverting a matrix
 other method. For solvin
 produces both the solution
 b, and also the matrix inver
 requires all the right-hand s
 (ii) that when the inverse n
 than the best alternative tech
 principal strength is that it
 bit more stable when full

 If you come along la
 multiply it by the inverse m
 quite susceptible to roundo
 included with the set of rig

 For these reasons, Gau
 of first choice, either for
 decomposition methods in
 Because it is straightforward
 good "psychological" back
 think it might be your line
 "
 Some people believe
 Jordan elimination is an "
 mostly myth. Except for
 below, the actual sequence
 very closely related to that

 For clarity, and to avoi
 only for the case of four equ
 hand side vectors that are
 extend the equations to th
 side vectors, in completely
 of course, general.
 --- OCR Start ---
 2.1
 Elimination on Columns
 Consider the linear matrix equation
 $\begin{bmatrix} a_{11} & a_{12} & a_{13} & a_{14} \\ a_{21} & a_{22} & a_{23} & a_{24} \\ a_{31} & a_{32} & a_{33} & a_{34} \\ a_{41} & a_{42} & a_{43} & a_{44} \end{bmatrix} \cdot \begin{bmatrix} x_{11} \\ x_{21} \\ x_{31} \\ x_{41} \end{bmatrix} = \begin{bmatrix} b_{11} \\ b_{21} \\ b_{31} \\ b_{41} \end{bmatrix}$
 Here the raised dot (.) signifies column augmentation,
 making a wider matrix out of it.
 It should not take you long to realize
 that $x_{ij}$ is the $i^{th}$ column of the
 right-hand side ($j = 1, 2, 3, 4$).  In other
 words, the matrix of unknowns is $X$, and in other
 words, the matrix solution is given by
 $[A] \cdot [X_1] = [Y]$
 where A and Y are square matrices, and where
 $A \cdot X_1 = Y$
 and
 Now it is also elementary to see that:
 • Interchanging any two columns of A,
 and of 1, does not change the solution
 Y. Rather, it just changes the order of the columns
 in a different order.
 • Likewise, the solution is unchanged if we
 replace any row in A by the sum of that row
 and of 1, does not change the solution matrix
 (which then is no longer elementary).
 • Interchanging any two rows of A does not change Y,
 if we simultaneously interchange the rows of Y. In other words, the solution remains unchanged.
 If we want to restore A to the identity matrix, we use
 Gauss-Jordan elimination, reducing
 the matrix A to the identity matrix.  Then Y
 becomes the solution set, and we are done.
 --- OCR End ---
 --- OCR Start ---
 38
 Chapter
 Pivoting
 In “Gauss-Jordan elim-
 ination”, the above list is used. The
 trivial linear combination of
 the other row). Then the right
 row to make all the remaining
 the identity matrix. We may
 $a_{22}$, then subtract the right
 make their entries in the same
 to the identity form. And the
 operations to A, we of course
 1 (which by now no longer
 Obviously we will run
 (then current) diagonal when
 element that we divide by,
 obvious, but true, is the fact
 the first or third procedures
 of any roundoff error, even
 Gauss-Jordan elimination (
 So what is this magic
 pivoting) or rows and columns
 element in the diagonal position
 we don’t want to mess up the
 we can choose among elements
 is about to be normalized,
 we are about to eliminate.
 don’t have to keep track of
 makes available as pivots
 out that partial pivoting is
 made mathematically precise
 and references, see [1]). To
 in this section, partial pivoting
 We have to state how
 one. The answer to this is
 theoretically and in practice
 element as the pivot is a very
 that the choice of pivot will
 the third linear equation in
 is almost guaranteed that it
 of the equations is not changed
 routines which choose as pivots
 original equations had all been
 unity. This is called implicit
 of the scale factors by which
 §2.3 include implicit pivoting.
 Finally, let us consider
 reflection you will see that
 --- OCR End ---
 --- OCR Start ---
 2.1
 predictably a one or zero (if
 to identity form) or else the
 as 1 is predictably a one or
 form). Therefore the matrix
 inverse of A is gradually built up.
 the solution vectors x can get
 the same storage, since after
 entry in the b's is never altered.

 Here is the routine for

 #include <math.h>
 #include "nrutil.h"
 #define SWAP(a,b) {temp=(a);(a)=(b);(b)=temp;}
 void gaussj (float **a, int n, float **b)
 Linear equation solution by Gauss-Jordan elimination.
 a is the input matrix. b[1..n][1..m] is the
 output, a is replaced by its matrix inverse,
 vectors.
 {
 	int *indxc,*indxr,*ipiv;
 	int i,icol,irow,j,k,l,ll;
 	float big,dum,pivinv;
 	indxc=ivector(1,n);
 	indxr=ivector(1,n);
 	ipiv=ivector(1,n);
 	for (j=1;j<=n;j++) ipiv[j]=0;
 	for (i=1;i<=n;i++) {
 		big=0.0;
 		for (j=1;j<=n;j++)
 			if (ipiv[j]==0)
 				for (k=1;k<=n;k++) {
 					if (ipiv[k]==0)
 						if (fabs(a[j][k])>=big) {
 							big=fabs(a[j][k]);
 							irow=j;
 							icol=k;
 						}
 				}
 		++(ipiv[icol]);
 		We now have the pivot element
 		element on the diagonal.
 		indxc[i]=icol;
 		indxr[i]=irow;
 		if (irow != icol)
 			for (l=1;l<=n;l++) SWAP(a[irow][l],a[icol][l]);
 		for (l=1;l<=n;l++) SWAP(b[irow][l],b[icol][l]);
 	}
 	indxr[i]=irow;
 	indxc[i]=icol;
 	if (a[icol][icol]==0.0) nrerror("gaussj: Singular Matrix-1");
 	pivinv=1.0/a[icol][icol];
 	a[icol][icol]=1.0;
 	for (l=1;l<=n;l++) a[icol][l] *= pivinv;
 	for (l=1;l<=n;l++) b[icol][l] *= pivinv;
 --- OCR End ---
 --- OCR Start ---
 40
 Chapter
 for (11=1;11<=n;11++)
 if (11 != icol[1])
 dum=a[11][icol[1]]
 a[11][icol[1]]=a[11][1]
 for (1=1;1<=n;1++)
 for (1=1;1<=n;1++)
 }
 This is the end of the main
 ble the solution in view of
 columns in the reverse order
 for (1=n;1>=1;1--) {
 if (indxr[1] != i
 for (k=1;k<=n;k++)
 SWAP(a[k][i
 }
 free_ivector(ipiv,1,n)
 free_ivector(indxr,1,n)
 free_ivector(indxc,1,n)
 Row versus Column
 The above discussion concerns
 operations on a matrix A combined with
 matrix R. For example, the
 effects the interchange of rows
 (including the possibility of partial pivoting)
 yielding successively
 (... R3
 The key point is that since the matrices are
 transformed at each stage from the
 Column operations, on
 by simple matrices, call them
 matrix A, will interchange A's
 involves (conceptually) inserting
 A and the unknown vector x
 (A.C1.
 --- OCR End ---
 --- OCR Start ---
 2.2 Gaussian
 which (peeling of the $C^{-1}$'s
 Notice the essential difference. In the
 latter case, the $C$'s must be applied.
 known. That is, they must all be
 the usefulness of column operations; an
 example in support of full pivoting.
 CITED REFERENCES AND FURTHER READING
 Wilkinson, J.H. 1965, The Algebra
 Carnahan, B., Luther, H.A., and Wilkes, J.O. 1969,
 (New York: Wiley), Example 5.2, p. 202.
 Bevington, P.R. 1969, Data Reduction and Error Analysis for the Physical Sciences
 (New York: McGraw-Hill), Program B.
 Westlake, J.R. 1968, A Handbook of Numerical Matrix Inversion and Solution of Linear Equations
 (New York: Wiley).
 Ralston, A., and Rabinowitz, P. 1978, A First Course in Numerical Analysis, 2nd ed.
 (New York: McGraw-Hill), §9.3–1.

 2.2 Gaussian Elimination
 The usefulness of Gaussian elimination is largely
 pedagogical. It stands between straightforward
 triangular decomposition schemes and more sophisticated
 Gaussian elimination reduces the matrix
 only halfway, to a matrix which is still
 nontrivial. Let us now see how.
 Suppose that in doing Gaussian elimination we at
 each stage subtract away rows to eliminate the
 is the pivot element, for example, $a_{11}$,
 but now use the pivot row to also
 Suppose, also, that we do operations which change
 the order of the unknowns and equations.
 Then, when we have completed the elimination we have an
 equation that looks like this
 $\begin{bmatrix} a'_{11} \\ 0 \\ 0 \\ 0 \end{bmatrix}$
 Here the primes signify that these are modified
 values, but have been modified only up to this
 point. The procedure up to this point is called
 --- OCR End ---
 --- OCR Start ---
 42	Chapter
 Backsubstitution
 But how do we solve
 isolated, namely
 With the last $x$ known we
 and then proceed with the
 The procedure defined by
 bination of Gaussian elimi
 of equations. The advantage of Gaus
 elimination is simply that
 innermost loops of Gauss--
 one multiplication, are exec
 and $M$ unknowns). The co
 only $\frac{1}{2}N^3$ times (only hal
 predictable zeros reduce th
 Each backsubstitution of a
 multiplication plus one sul
 Gaussian elimination thus
 (We could reduce this adva
 as part of the Gauss-Jorda
 For computing the inv
 right-hand sides, namely th
 matrix), Gaussian eliminatio
 reduction) + $\frac{1}{2}N^3$ (right-h
 = $\frac{4}{3}N^3$ loop executions, w
 unit vectors are quite speci
 is taken into account, the ri
 executions, and, for matrix
 Both Gaussian elimina
 that all right-hand sides mu
 in the next section does n
 operations count, both for
 matrix inversion. For this
 elimination as a routine.
 CITED REFERENCES AND F
 Ralston, A., and Rabinowitz, P.
 McGraw-Hill), §9.3-1.
 --- OCR End ---
 --- OCR Start ---
 2.3 LU Decomposition

 Isaacson, E., and Keller, H.B.
 Johnson, L.W., and Riess, R.
 Wesley), §2.2.1.
 Westlake, J.R. 1968, *A Handbook of Numerical Methods* (New York: Wiley).

 2.3 LU Decomposition

 Suppose we are able to find a decomposition $A = LU$, where L is lower triangular and U is upper triangular (has elements only on and above the diagonal). For a 4 × 4 matrix A, for example, we have
 $\begin{bmatrix}
 \alpha_{11} & 0 & 0 & 0 \\
 \alpha_{21} & \alpha_{22} & 0 & 0 \\
 \alpha_{31} & \alpha_{32} & \alpha_{33} & 0 \\
 \alpha_{41} & \alpha_{42} & \alpha_{43} & \alpha_{44}
 \end{bmatrix}$
 We can use a decomposition $A = LU$ to solve $Ax = b$ by first solving for the vector $y$ in $Ly = b$ and then solving for $x$ in $Ux = y$.

 What is the advantage of this approach? The advantage is that the solution of $Ly = b$ and $Ux = y$ can be done by forward substitution as described in §2.2.  For example,
 $y_1 = \frac{b_1}{\alpha_{11}}$
 $y_i = \frac{1}{\alpha_{ii}} \left[ b_i - \sum_{j=1}^{i-1} \alpha_{ij} y_j \right], \quad i = 2, \dots, N$
 while (2.3.5) can then be solved by back substitution (2.2.4),
 $x_N = \frac{y_N}{\beta_{NN}}$
 $x_i = \frac{1}{\beta_{ii}} \left[ y_i - \sum_{j=i+1}^N \beta_{ij} x_j \right], \quad i = N - 1, \dots, 1$
 --- OCR End ---
 44 Chapter
 Equations (2.3.6) and
 of an inner loop containing
 sides which are the unit components
 matrix), then taking into account
 of (2.3.6) from $\frac{1}{2}N^3$ to $\frac{1}{6}N^3$. Notice that, once we have
 many right-hand sides as we like, we can go
 over the methods of §2.1
 Performing the LU Decomposition
 How then can we solve for the
 i, jth component of equations (2.3.8)
 beginning with
 The number of terms in the
 number. We have, in fact
 $i < j$:
 $i = j$:
 $i > j$:
 Equations (2.3.8)-(2.3.10) for the
 $\beta$'s (the diagonal being represented by 1) is less
 than the number of equations (2.3.6) and
 and then try to solve for the $\alpha$'s.
 A surprising procedure is to solve
 the set of $N^2 + N$ equations (2.3.8) - (2.3.10)
 the equations in a certain order.
 • Set $\alpha_{ii} = 1$, $i = 1, 2, \dots , N$.
 • For each $j = 1, 2, \dots , N$, for $i = 1, 2, \dots , j$, use (2.3.8) to solve for $\alpha_{ij}$.
 (When $i = 1$ in 2.3.8, we have a single equation
 for $i = j + 1, j + 2, \dots , N$, use (2.3.10) to solve for $\beta_{ij}$.
 Be sure to do both
 --- OCR Start ---
 2.3 LU Decomposition

 a
 c
 e
 g
 b
 d
 f
 h
 Figure 2.3.1. Crout's algorithm modified in the order indicated by the arrows. The modified elements that are used in subsequent calculations are indicated by shading.

 If you work through a typical Crout calculation, the $\alpha$'s and $\beta$'s that occur on the right-hand side are already determined by the time they are used. Each element is used only once and never needs to be stored in the location that it occupies. [The diagonal unity elements are handled automatically.] Crout's method fills in the matrix

 by columns from left to right (see Figure 2.3.1).

 What about pivoting?  Consider the division in equation 2.
 --- OCR End ---
 --- OCR Start ---
 46
 Chapter
 method. Only partial pivoti
 However this is enough to
 we don't actually decompo
 a rowwise permutation of
 decomposition is just as us
 Pivoting is slightly sul
 equation (2.3.12) in the ca
 equation (2.3.13) except fo
 upper limit of the sum is k
 commit ourselves as to wh
 to fall on the diagonal in th
 below it in the column, i =
 β. This can be decided aft
 should be able to guess by
 (pivot element), then do all
 method with partial pivotin
 initially finds the largest el
 for the maximal pivot eleme
 the equations to make their
 pivoting mentioned in §2.
 #include <math.h>
 #include "nrutil.h"
 #define TINY 1.0e-20
 void ludcmp(float **a, int
 Given a matrix a [1..n] [1..r
 permutation of itself. a and n
 indx [1..n] is an output ve
 pivoting; d is output as ±1 de
 or odd, respectively. This routi
 or invert a matrix.
 {
 int i, imax,j, k;
 float big, dum, sum, temp;
 float *vv;
 vv=vector(1,n);
 *d=1.0;
 for (i=1;i<=n;i++) {
 }
 big=0.0;
 for (j=1;j<=n;j++)
 if ((temp=fabs
 if (big == 0.0) nr
 No nonzero largest e
 vv[i]=1.0/big;
 for (j=1;j<=n;j++) {
 for (i=1;i<j;i++)
 }
 sum=a[i][j];
 for (k=1;k<i;k-
 a[i][j]=sum;
 big=0.0;
 for (i=j;i<=n;i++)
 sum=a[i][j];
 for (k=1;k<j;k-
 --- OCR End ---
 --- OCR Start ---
 2.3 LU D
 sum -- = a[i]
 a[i][j]=sum;
 if ((dum=vv[i
 Is the figure of m
 big=dum;
 imax=i;
 }
 }
 if (j != imax) {
 for (k=1;k<=n;
 dum=a[imax]
 a[imax] [k] =
 a[j] [k]=dum
 *d = -(*d);
 vv [imax]=vv[j]
 indx[j]=imax;
 if (a[j] [j] == 0.0
 If the pivot element
 algorithm). For some
 TINY for zero.
 if (j != n) {
 dum=1.0/(a[j] [
 for (i=j+1;i<=
 }
 }
 free_vector(vv,1,n);
 Here is the routine for
 equations (2.3.6) and (2.3
 void lubksb (float **a, int
 Solves the set of n linear equati
 A but rather as its LU decompo
 as the permutation vector retur
 B, and returns with the soluti
 and can be left in place for suc
 into account the possibility tha
 in matrix inversion.
 {
 int i,ii=0,ip,j;
 float sum;
 for (i=1;i<=n;i++) {
 ip=indx[i];
 sum=b[ip];
 b[ip]=b[i];
 if (ii)
 for (j=ii;j<=i-
 else if (sum) ii=i
 b[i]=sum;
 for (i=n;i>=1;i--) {
 sum=b[i];
 for (j=i+1;j<=n;j+
 b[i]=sum/a[i][i];
 }
 }
 --- OCR End ---
 --- OCR Start ---
 48
 Chapter

 The LU decomposition
 loops (each with one multiplication)
 for solving one (or a few)
 Gauss-Jordan routine gaussj
 than a Gauss-Jordan routine
 For inverting a matrix, the
 as discussed following equation
 as gaussj.

 To summarize, this is
 A $\cdot$ x = b:

 float **a, *b, d;
 int n, *indx;

 ludcmp(a, n, indx, &d);
 lubksb(a, n, indx, b);

 The answer x will be
 been destroyed.
 If you subsequently want a
 different right-hand side b
 lubksb(a, n, indx, b);

 not, of course, with the original
 set by ludcmp.

 Inverse of a Matrix

 Using the above LU
 pletely straightforward to find the
 #define N
 float **a, **y, d, *col;
 int i, j, *indx;

 ludcmp(a, N, indx, &d);
 for (j = 1; j <= N; j++) {
   for (i = 1; i <= N; i++)
     col[j] = 1.0;
   lubksb(a, N, indx, col);
   for (i = 1; i <= N; i++)
 }

 The matrix y will now contain the inverse;
 been destroyed. Alternatively, one can use a
 routine like gaussj (§2.1)
 Both methods have practical
 --- OCR End ---
 2.3 LU D
 Incidentally, if you ever solve the equation $Ax = B$, you should LU decompose $A$ and solve for $x$ by forward and backward substitution with the unit vectors $e_i$ instead of with the unit vectors $e_i$ and matrix multiplication, and
 Determinant of a Matrix
 The determinant of a triangular matrix is the product of its diagonal elements,
 We don't, recall, compute the determinant but rather the LU decomposition of a rowwise permutation of $A$, which is easily done; whether the number of row interchanges is even or odd is all that matters; the determinant is the product by the corresponding sign. (This is done in the routine ludcmp.) Calculation of a determinant by this means requires fewer operations than direct calculation, but requires frequent backsubstitutions by other routines.
 \#define N
 float **a,d;
 int j,*indx;
 ludcmp(a, N, indx, &d);
 for(j=1;j<=N;j++) d *= a[j][j];
 The variable d now contains the determinant; the array a will have been destroyed. For a matrix of any substantial size, there is a serious danger of overflow or underflow; you should use the scaling described earlier.  Even so, you can modify the loop of the program to keep track of the scale factors and thereby keep control of the absolute values of the intermediate results.
 Complex Systems
 If your matrix A is real, then you can (i) LU decompose A in the usual way, (ii) perform the backsubstitution with the unit vector, and (iii) backsubstitute to solve for $x$.  If the matrix itself is complex, this is more complicated.
 then there are two possible ways to proceed:  you could either use as complex routines. Complex arithmetic is significantly slower than real arithmetic, but the scaling vector vv and in the program are easily modified for complex numbers; the solution is done through in the obvious way, with the obvious modification to account for the fact that we are dealing with complex numbers, which is discussed in the discussion of complex arithmetic in the following chapter.
 --- OCR Start ---
 50
 Chapter
 A quick-and-dirty way
 parts of (2.3.16), giving
 which can be written as a 2
 and then solved with ludcmp
 2 inefficient in storage, since
 in time, since the complex m
 use 4 real multiplies, while the
 an $N \times N$ one. If you can to
 is an easy way to proceed.
 CITED REFERENCES AND F
 Golub, G.H., and Van Loan, C.F
 University Press), Chapt
 Dongarra, J.J., et al. 1979, LIN
 Forsythe, G.E., Malcolm, M.Α.
 Computations (Englewoo
 Forsythe, G.E., and Moler, C.E
 wood Cliffs, NJ: Prentice
 Westlake, J.R. 1968, A Handbo
 (New York: Wiley).
 Stoer, J., and Bulirsch, R. 1980
 §4.2.
 Ralston, A., and Rabinowitz, P.
 McGraw-Hill), §9.11.
 Horn, R.A., and Johnson, C.R.
 2.4 Tridiagonal
 of Equation
 The special case of a s
 nonzero elements only on t
 frequently. Also common a
 only along a few diagonal 1
 For tridiagonal sets, th
 substitution each take only
 very concisely. The resultin
 Naturally, one does no
 the nonzero components, st
 $\begin{bmatrix}
 b_1 & c_1 & 0 & \cdots & 0 \\
 a_2 & b_2 & c_2 & \cdots & 0 \\
 & & \cdots & & \\
 & & \cdots & & a_N
 \end{bmatrix}$
 --- OCR End ---
 --- OCR Start ---
 2.4 Tridiagonal a
 Notice that $a_1$ and $c_N$ are un
 #include "nrutil.h"
 void tridag(float a[], float b[], float c[], float r[], unsigned long n)
 Solves for a vector u[1..n] given
 b[1..n], c[1..n], and r[1..n]
 {
 unsigned long j;
 float bet, *gam;
 gam=vector(1,n);
 if (b[1] == 0.0) nrerror("Error in tridag");
 If this happens then you should quit
 trivially eliminated.
 u[1]=r[1]/(bet=b[1]);
 for (j=2;j<=n;j++) {
 gam[j]=c[j-1]/bet;
 bet=b[j]-a[j]*gam[j];
 if (bet == 0.0) nrerror("Error in tridag");
 u[j]=(r[j]-a[j]*u[j-1])/bet;
 }
 for (j=(n-1);j>=1;j--) {
 u[j] -= gam[j+1]*u[j+1];
 }
 free_vector(gam,1,n);
 }
 There is no pivoting in
 when the underlying matrix
 a nonsingular matrix. In pra
 of problems that lead to tr
 which guarantee that the al
 $|b_j|$
 (called diagonal dominance
 a zero pivot.
 It is possible to constr
 algorithm causes numerical
 never encountered — unlike
 The tridiagonal algori
 more robust than theory sa
 problem for which tridag
 band diagonal systems, nov
 Some other matrix fo
 additional elements (e.g.,
 solution; see §2.7.
 Band Diagonal Sys
 Where tridiagonal syster
 one, band diagonal systems are
 immediately to the left of (bel
 its right (above it). Of course,
 --- OCR End ---
 52
 Chapter

 In that case, the solution of the equation is
 much faster, and in much less storage.
 The precise definition of band diagonal matrices is
 $a_{ij} = 0$
 Band diagonal matrices are stored in a compact form,
 if the matrix is tilted 45° clockwise, to produce a
 matrix with $m_1 + 1 + m_2$ columns.
 The band diagonal matrix

 which has $N = 7$, $m_1 = 2$, and $m_2 = 2$.

 Here $x$ denotes elements that would be
 referenced by any manipulation
 of the original matrix appearing on the
 superdiagonal elements to its right.
 The simplest manipulation is to multiply
 it by a vector to its right. Although this might appear simple,
 the following routine carefully utilizes the
 compact storage format in an efficient manner.

 \#include "nrutil.h"

 void banmul(float **a, unsigned long $n$, int $m1$, int $m2$, float *b, float *x)
 Matrix multiply $b = A \cdot x$, where $A$ is
 rows above. The input vector $x$ is stored
 respectively. The array $a[1..n][m1+1]$ contains the elements of
 are in $a[1..n][m1+1]$. Subscripts are such that
 appropriate to the number of elements in each row.
 $a[1..j][m1+2..m1+m2+1]$ vectors to the
 perdiagonal.
 \{
 unsigned long i,j,k, tmploop;
 for (i=1; i<=n; i++){
 k = i - m1 -1;
 tmploop = LMIN(m1+m2+1, n-i+1);
 b[i] = 0.0;
 for (j=LMAX(1, 1-k)
 \}
 \}
 --- OCR Start ---
 2.4 Tridiagonal a
 It is not possible to store a band diagonal matrix as compactly as the compact method, see §2.3) produces and returns the upper triangular matrix; this routine constructs a lower triangular matrix replaces a, which is stored in the array a. The vector indx[1..n] is an output vector which records the row interchanges; d is output as ±1 depending on whether the number of row interchanges is even or odd, respectively. This routine is useful for solving sets of equations.
 #include <math.h>
 #define SWAP(a,b) {dum=(a);(a)=(b);(b)=dum;}
 #define TINY 1.0e-20
 void bandec(float **a, unsigned long indx[], int n, int m1, int m2, float *d)
 {
 unsigned long i,j,k,l;
 int mm;
 float dum;
 mm=m1+m2+1;
 l=m1;
 for (i=1;i<=m1;i++) {
 for (j=m1+2-i;j<=mm;j++)
 }
 l--;
 for (j=mm-1;j<=mm;j++) a[i][j]=0.0;
 *d=1.0;
 l=m1;
 for (k=1;k<=n;k++) {
 dum=a[k][1];
 i=k;
 if (l < n) l++;
 for (j=k+1;j<=l;j++) {
 if (fabs(a[j][1]) > fabs(dum)) {
 dum=a[j][1];
 i=j;
 }
 }
 indx[k]=i;
 if (dum == 0.0) a[k][mm]=0.0;
 Matrix is algorithmically singular.
 some applications).
 if (i != k) {
 *d = -(*d);
 for (j=1;j<=mm;j++) {
 SWAP(a[k][j],a[i][j]);
 }
 }
 for (i=k+1;i<=l;i++) {
 dum=a[i][1]/a[k][1];
 a[i][1]=dum;
 for (j=2;j<=mm;j++)
 a[i][j]-=dum*a[k][j-k];
 }
 }
 }
 --- OCR End ---
 --- OCR Start ---
 54
 Chapter
 routine does take advantage
 diagonal element of $U$, then
 is in fact singular. In this respect, the algorithm
 which can fail algorithmically
 $m_1 = m_2 = 1$) for some ill-conditioned matrix.
 Once the matrix $A$ has been decomposed, the solution
 turn by repeated calls to `banbks`.
 `#define SWAP(a,b) {dum=(a);(a)=(b);(b)=dum;}`
 `void banbks(float **a, unsigned long indx[],`
 `unsigned long i,k,l;`
 `int mm;`
 `float dum;`
 `mm=m1+m2+1;`
 `l=m1;`
 `for (k=1;k<=n;k++) {`
 `i=indx[k];`
 `if (i != k) SWAP(b[i],b[k]);`
 `if (l < n) l++;`
 `for (i=k+1;i<=l;i++) {`
 `b[i] -= a[i][k-1]*b[k];`
 `}`
 `}`
 `l=m1;`
 `for (i=n;i>=1;i--) {`
 `dum=b[i];`
 `for (k=2;k<=l;k++)`
 `b[i]=dum/a[i][1];`
 `if (l < mm) l++;`
 `}`
 `}`
 The routines `bandec` and `bansol` are given in [1].
 CITED REFERENCES AND FURTHER READING
 Keller, H.B. 1968, Numerical Methods for Two-Point Boundary-Value Problems (Waltham, Mass.: Blaisdell), p. 74.
 Dahlquist, G., and Bjorck, A. 1974, Numerical Methods (Englewood Cliffs, N.J.: Prentice-Hall), Example 5.4.3, p. 166.
 Ralston, A., and Rabinowitz, P. 1978, A First Course in Numerical Analysis, 2nd ed. (New York: McGraw-Hill), §9.11.
 Wilkinson, J.H., and Reinsch, C. 1971, Handbook for Automatic Computation, vol. 2, Linear Algebra (New York: Springer-Verlag), pp. 93–101.
 Golub, G.H., and Van Loan, C.F. 1983, Matrix Computations (Baltimore: Johns Hopkins University Press), §4.3.
 --- OCR End ---
 --- OCR Start ---
 2.5 Iterative Improvement

 δx
 x + δx
 x

 Figure 2.5.1. Iterative improvement
 A to produce b + δb. The known
 side is inverted, giving δx. This is

 2.5 Iterative Improvement
 Linear Equations

 Obviously it is not easy to
 set than the precision of your
 large sets of linear equations
 even comparable to, the computed
 errors accumulate, and the matrix becomes
 to singular. You can easily find cases where
 (you thought) were far from singular.

 If this happens to you, it is
 called iterative improvement.

 Figure 2.5.1): Suppose that

 You don't, however, know
 where δx is the unknown error in x. The
 solution gives a product slightly

 Subtracting (2.5.1) from (2
 --- OCR End ---
 --- OCR Start ---
 56
 Chapter
 But (2.5.2) can also be solv
 In this equation, the whole
 solution that you want to
 in double precision, since t
 Then, we need only solve (
 solution to get an improve
 An important extra be
 decomposition. In this case
 we need do to solve (2.5.4)
 The code to do all thi
 #include "nrutil.h"
 void mprove (float **a, flo
 Improves a solution vector $x$ [
 a[1..n] [1..n], and the vec
 Also input is alud [1..n] [1.
 the vector indx [1..n] also r
 to an improved set of values.
 {
 void lubksb (float **a,
 int j,i;
 double sdp;
 float *r;
 r=vector(1,n);
 for (i=1;i<=n;i++) {
 sdp = -b[i];
 for (j=1;j<=n;j++)
 r[i]=sdp;
 lubksb (alud, n, indx,r);
 for (i=1;i<=n;i++) x[i]
 free_vector(r,1,n);
 You should note that
 it LU decomposes it. Since
 and its LU decomposition,
 lubksb destroys b in obta
 this extra storage, iterative
 of order only $N^2$ operation
 discussion following equat
 money's worth if it saves a
 spent of order $N^3$ operati
 You can call mprove
 starting quite far from the
 call to verify convergence
 --- OCR End ---
 --- OCR Start ---
 2.5 Iterative Improvement
 More on Iterative Improvement

 It is illuminating (and what was missing in
 analytical foundation for equation (2.5.10):
 the previous discussion was that
 we neglected the fact that the
 A different analytical approach is to use an
 approximate inverse of the matrix A and
 Define the residual matrix R
 which is supposed to be "small."

 Next consider the following
 A$^{-1}$ = A$^{-1}$ ⋅ (B$_0^{-1}$ + R)
 = (1 - R)$^{-1}$ ⋅ A$^{-1}$

 We can define the $n$th partial inverse B$_n$
 so that B$_\infty$ → A$^{-1}$, if the limit exists.
 It now is straightforward to derive the
 recurrence relations. As regards the speed of

 Then it is easy to show that

 This is immediately recognized by
 taking the role of A$^{-1}$. We see that if the
 decomposition of A be exact,
 the residual is smaller than the square of
 application of equation (2.5.10), the residual
 of order R$^2$, will be smaller than the
 moreover, can be applied more than once.
 A much more surprising result is that it more
 than doubles the order $n$ at each step, i.e.,

 B$_{2n+1}$ =

 Repeated application of equation (2.5.11) converges
 quadratically to the unknown (if it converges
 cally"). Equation (2.5.11) goes by the name of
 Method; see Pan and Reif [1] and the
 Newton-Raphson method of root finding.
 Before you get too excited, remember that it
 involves two full matrix multiplications. It takes
 N$^3$ adds and multiplies. But the
 only N$^3$ adds and N$^3$ multiplications.
 special circumstances allow it to be faster than
 matrices. We will meet such circumstances later.

 In the spirit of delayed gratification, we ask:
 When does the series in equation (2.5.11) converge?
 for example, an initial LU decomposition, etc.
 --- OCR End ---
 --- OCR Start ---
 58
 Chapter
 We can define the norm
 able to induce on a vector,
 If we let equation (2.5.7) act on
 to do, it is obvious that a sufficient condition
 Pan and Reif [1] point out that
 $\epsilon$ times the matrix transpose
 $B_0$
 To see why this is so involves
 $A^T \cdot A$ is a symmetric, positive definite matrix.  Its
 diagonal representation, R takes the form
 $R = $
 where all the $\lambda_i$'s are positive and
 $\|R\| < 1$. It is not difficult
 convergence for equation (2.5.7).
 Rarely does one know the bounds of the matrix elements.  However, we can
 derive several interesting bounds for the spectral radius.  The
 choices guarantee the convergence of equation (2.5.7):
 $\epsilon \le 1 / \sum_{j,k} a_{jk}^2$     or
 The latter expression is truly a vector norm.  We can replace
 the vector norm in equation (2.5.7) by the
 the $L_\infty$ (max) norm, or the $L_2$ norm.
 Another approach, with a statistical interpretation, is to bound the
 eigenvalue statistically, by calculating the maximum and variance
 of 2 max $s_i$ and 2NVar($s_i$)/$\rho$
 respectively.
 CITED REFERENCES AND FURTHER READING
 Johnson, L.W., and Riess, R.D. 1982, Numerical Analysis (Reading, MA:
 Golub, G.H., and Van Loan, C.F. 1983, Matrix Computations (Baltimore, MD: Johns Hopkins
 Dahlquist, G., and Bjorck, A. 1974, Numerical Methods (Englewood Cliffs, NJ: Prentice-Hall),
 Forsythe, G.E., and Moler, C.B. 1967, Computer Solution of Linear Algebraic Systems (Engle-
 Ralston, A., and Rabinowitz, P. 1978, A First Course in Numerical Analysis (New York:
 Pan, V., and Reif, J. 1985, in Proceedings of the 17th Annual ACM Symposium on Theory
 of Computing (New York: ACM), pp. 143-151.
 --- OCR End ---
 --- OCR Start ---
 2.6 Singular Values
 There exists a very powerful set of techniques for dealing with matrices that are either singular or nearly singular.  In cases where Gaussian elimination fails to produce accurate results, this set of techniques will almost always work.  These techniques will diagnose for you precisely what has gone wrong and provide not only a diagnose the problem, but also a very useful numerical answer, and a much deeper understanding that you thought you should have had all along.  SVD is also the method of choice for modeling data.
 We will outline the relevant properties of SVD, and illustrate the use of SVD in this application, in this chapter, with specific focus on its use in modeling of data.
 SVD methods are based on the singular value decomposition.  A complete theoretical treatment is beyond our scope:  Any $M \times N$ matrix $A$ can be represented as a product of three matrices whose dimensions are equal to its number of columns and rows. The result is a column-orthogonal matrix $U$, a diagonal matrix containing the singular values, and a row-orthogonal matrix $V$.
 The various shapes of these matrices are dependent on the relative values of $M$ and $N$.
 $\begin{pmatrix} & & \\ & A & \\ & & \end{pmatrix} = \begin{pmatrix} & & \\ & & \\ & & \end{pmatrix}$
 The matrices U and V are column-orthogonal and row-orthogonal (orthonormal, respectively),
 $\sum_{i=1}^M \sum_{j=1}^N$
 --- OCR End ---
 --- OCR Start ---
 60
 Chapter
 or as a tableau,
 $\begin{pmatrix}
 U^T \\
 \end{pmatrix}$
 Since $V$ is square, it is also
 The SVD decomposition
 the singular values $w_j$ for
 columns of $U$ are also zero.
 The decomposition (2
 matrix is, and it is "almost"
 the same permutation of the
 rows of $V^T$), or (ii) forming
 corresponding elements of
 of the permutation freedom
 the decomposition need no
 zero singular values can be
 At the end of this section
 an arbitrary matrix $A$, replace
 $W$ and $V$ separately. The
 al. [1], which is in turn based
 various forms, in [2-4] and else
 of the algorithm used. As I am
 going to ask you to accept
 its necessary background ma
 stable, and that it is very un
 enter the algorithm (House
 $QR$ procedure with shifts)
 If you are as suspicious
 that `svdcmp` does what we
 matrix $A$, call the routine,
 (2.6.4) are satisfied. Since
 for SVD, this procedure is
 Now let us find out w
 --- OCR End ---
 --- OCR Start ---
 2.6 S
 SVD of a Square Ma
 If the matrix $A$ is squa
 of the same size. Their inve
 so their inverses are equal
 diagonal matrix whose elen
 it now follows immediatel
 The only thing that can g
 to be zero, or (numericall-
 roundoff error and therefor
 problem, then the matrix is
 clear diagnosis of the situ
 Formally, the conditio
 (in magnitude) of the $w_j$'s
 condition number is infinit
 large, that is, if its reciproc
 example, less than $10^{-6}$ fc
 For singular matrices
 Consider the familiar set c
 where $A$ is a square matriz
 linear mapping from the ve
 there is some subspace of $x$
 The dimension of the nulls
 can be found in it) is calle
 Now, there is also som
 that there exists some $x$ whi
 of $A$. The dimension of the
 range will be all of the vect
 will be less than $N$. In fact
 What has this to do w
 for the nullspace and rang
 same-numbered elements $u$
 span the range; the columr
 an orthonormal basis for $t$
 Now let's have anothe
 (2.6.6) in the case that $A$ is
 $b = 0$, is solved immediate
 is zero yields a solution.
 When the vector $b$ on
 whether it lies in the range
 does have a solution $x$; in
 the nullspace (any column
 in any linear combination
 --- OCR End ---
 62
 Chapter

 If we want to single out
 a representative, we might use
 how to find that vector using
 very often that one gets to see
 x

 This will be the solution vector
 nullspace complete the space
 Proof: Consider |x + x|
 the modified inverse of W

 |x + x|

 Here the first equality follows
 mality of V. If you now
 right-hand side, you will see
 $w_j \ne 0$, while the second only
 only where $w_j = 0$. Therefore
 If b is not in the range
 has no solution. But here
 equation (2.6.7) can still be
 will not exactly solve A . x
 closest possible job in the

 x
 v

 The number r is called the
 The proof is similar to
 x'. Then A . x - b is more
 the range of A. We then

 $|A . x - b + b'| = |($

 $= |($

 $= |U$

 $= |($

 Now, ($W . W^{-1} - 1$) is a
 $w_j = 0$, while $U^T b'$ has no
 range of A. Therefore the
 Figure 2.6.1 summarizes
 --- OCR Start ---
 solutions of
 $A\textbf{x} = \textbf{d}$
 null
 space
 of $A$
 SVD solution of
 $A\textbf{x} = \textbf{d}$
 2.6 S
 $\textbf{x}$
 so
 $A$
 Figure 2.6.1. (a) A nonsingular
 vector $\textbf{x}$ is mapped into $\textbf{b}$, so that
 vector space into one of lower dimension.  The
 "nullspace" of $A$ is mapped to zero.  Thus,
 any vector in the nullspace, here
 (SVD) selects the particular solution
 of $A$, so $A\textbf{x} = \textbf{c}$ has no solution unless
 solution of $A\textbf{x} = \textbf{c}'$, as shown

 In the discussion since
 either is singular or else is
 however, the far more common case is that
 but nonzero, so that the many
 methods of LU decomposition
 solution to the set of equations
 the solution vector may have
 when multiplying by the
 right-hand vector $\textbf{b}$. In such
 --- OCR End ---
 --- OCR Start ---
 64 Chapter
 small $w_j$'s and then using
 residual $|A \cdot x - b|$ being s
 solution where the small $w_j$
 It may seem paradox
 corresponds to throwing away
 we are trying to solve. The
 precisely a combination of
 best useless; usually it is w
 off towards infinity along some
 this, it compounds the rounding
 SVD cannot be applied
 deciding at what threshold t
 what size of computed res
 As an example, here
 equation (2.6.7) and obtain
 that the SVD of a matrix $A$
 that this routine presumes t
 do this for you. If you ha
 ill-conditioned as any direc
 \#include "nrutil.h"
 void svbksb(float **u, float *w,
 Solves $A \cdot X = B$ for a vector $X$
 $v[1..n][1..n]$ as returned b
 square matrices. b[1..m] is t
 No input quantities are destroy
 \{
 int jj,j,i;
 float s, \*tmp;
 tmp=vector(1,n);
 for (j=1;j<=n;j++) \{
 s=0.0;
 if (w[j]) \{
 for (i=1;i<=m;
 s /= w[j];
 \}
 tmp[j]=s;
 \}
 for (j=1;j<=n;j++) \{
 s=0.0;
 for (jj=1;jj<=n;jj
 x[j]=s;
 \}
 free\_vector(tmp,1,n);
 \}
 Note that a typical u
 typical use of ludcmp and
 matrix $A$ just once, and the
 with different right-hand si
 values before svbksb is c
 --- OCR End ---
 --- OCR Start ---
 2.6 S
 #define N ...
 float wmax, wmin, **a, **u
 int i, j;
 for (i=1; i<=N; i++)
   for (j=1; j<=N; j++)
     u[i][j] = a[i][j];
 svdcmp(u, N, N, w, v);
 wmax = 0.0;
 for (j=1; j<=N; j++) if (w[j] > wmax) wmax = w[j];
 This is where we set the threshold.  This
 is typical, but not universal.
 wmin = wmax * 1.0e-6;
 for (j=1; j<=N; j++) if (w[j] < wmin) w[j] = 0.0;
 svbksb(u, w, v, N, N, b, x);

 SVD for Fewer Equations.
 If you have fewer linear equations than unknowns,
 expecting a unique solution is unrealistic. There will be a range
 of solutions. If you want a particular solution, SVD can do the job.
 The SVD decomposition is still valid provided
 $M < N$. There may be an infinite number of solutions to the linear
 equations. Be sure that you use the routine
 svbksb, which will give you the solution corresponding to setting
 the components of V corresponding to zero singular values to zero.  This is equivalent to adding
 to the particular solution any vector in the nullspace of $A^T$.

 SVD for More Equations.
 This situation will occur when you are trying to find a least-squares
 solution to an overdetermined system of linear equations.  The equations
 to be solved are

 The proofs that we gave above do not need to be altered
 to the case of more equations.
 --- OCR End ---
 --- OCR Start ---
 66
 Chapter
 given by (2.6.7), which, wi
 $\begin{pmatrix}
 \end{pmatrix} = \begin{pmatrix}
 V
 \end{pmatrix}$
 X
 In general, the matrix
 set to zero. Occasionally,
 this case you will need to
 column in V gives the line=
 the supposedly overdeterm
 Sometimes, although
 reasons, you may neverthe
 Their corresponding column
 to your data. In fact, you m
 free parameters in the fit. T
 Constructing an Or
 Suppose that you hav
 $N \le M$. Then the N
 Often you want to constru
 subspace. The textbook
 starting with one vector a
 time. Numerically, howe
 Gram-Schmidt orthogonali
 The right way to con
 Form an $M \times N$ matrix A
 through svdcmp. The colu
 from svdcmp) are your des
 You might also want
 then the spanned subspace
 corresponding to zero $w_j$'s
 (QR factorization, dis
 see [5].)
 Approximation of M
 Note that equation (2.
 of outer products of colum
 being the singular values
 --- OCR End ---
 --- OCR Start ---
 2.6 S
 If you ever encounter
 matrix $A$ are very small, the
 sum (2.6.13). This means the
 same $k$ ones) and you will
 vector $\bf x$: You just dot $\bf x$ with
 scalar by the corresponding
 column of $U$. If your matrix
 values, then this computation
 instead of $MN$ for the function
 SVD Algorithm
 Here is the algorithm
 matrix. See §11.2-§11.3,
 method.
 #include <math.h>
 #include "nrutil.h"
 void svdcmp(float **a, int
 Given a matrix a [1..m] [1..n],
 $U \cdot W \cdot V^T$. The matrix $U$ replaces
 put as a vector w [1..n]. The
 {
 float pythag(float a,
 int flag, i,its,j,jj,k,
 float anorm,c,f,g,h,s,
 rv1=vector(1,n);
 g=scale=anorm=0.0;
 for (i=1;i<=n;i++) {
 l=i+1;
 rv1 [i]=scale*g;
 g=s=scale=0.0;
 if (i <= m) {
 for (k=i;k<=m;k++)
 s+=a[k][i]*a[k][i];
 if (scale) {
 for (k=i;k<=m;k++) {
 a[k][i]
 s += a
 }
 f=a[i][i];
 g = -SIGN(s,f);
 h=f*g-s;
 a[i][i]=f-g
 for (j=1;j<=n;j++) {
 for (s=
 f=s/h;
 for (k=
 }
 for (k=i;k<
 }
 }
 w[i]=scale *g;
 g=s=scale=0.0;
 if (i <= m && i != m) {
 for (k=l;k<=n;l++)
 if (scale) {
 --- OCR End ---
 ```
 for (k=1;k<=n;k++) {
 a[i][k]
 s += a[i][k]*a[i][k];
 }
 f=a[i][1];
 g = -SIGN(s);
 h=f*g-s;
 a[i][1]=f-g;
 for (k=1;k<=n;k++) {
 for (j=1;j<=n;j++) {
 for (s=0.0;s<=1.0;s+=0.1) {
 for (k=1;k<=n;k++) {
 }
 }
 }
 }
 for (k=1;k<=n;k++) {
 }
 }
 anorm=FMAX(anorm,(fabs(h)));
 for (i=n;i>=1;i--) {
 if (i < n) {
 if (g) {
 for (j=1;j<=n;j++) {
 v[j][i]
 for (j=1;j<=n;j++) {
 for (s=0.0;s<=1.0;s+=0.1) {
 for (k=1;k<=n;k++) {
 }
 }
 }
 }
 }
 }
 for (j=1;j<=n;j++) {
 }
 v[i][i]=1.0;
 }
 g=rv1[i];
 l=i;
 for (i=IMIN(m,n);i>=1;i--) {
 l=i+1;
 g=w[i];
 for (j=1;j<=n;j++)
 if (g) {
 g=1.0/g;
 for (j=1;j<=n;j++) {
 for (s=0.0;s<=1.0;s+=0.1) {
 f=(s/a[i][i])*a[i][j];
 for (k=i;k<=n;k++)
 }
 }
 for (j=i;j<=m;j++)
 } else for (j=i;j<=n;j++)
 ++a[i][i];
 for (k=n;k>=1;k--) {
 for (its=1;its<=30;its++) {
 flag=1;
 for (l=k;l>=1;l--) {
 nm=l-1;
 if ((float)(fabs(a[l][k])-anorm*fabs(a[nm][k])) > 0.0) {
 flag=0;
 break;
 }
 }
 if ((float)(fabs(a[k][l])-anorm*fabs(a[k][nm])) > 0.0)
 }
 if (flag) {
 c=0.0;
 s=1.0;
 for (i=1;i<

 ```
 --- OCR Start ---
 2.6 S
 f=s*rv1
 rv1[i]=
 if ((fl
 g=w[i];
 h=pythag(f,1.0);
 w[i]=h;
 h=1.0/h;
 c=g*h;
 s = -f*
 for (j=
 y=a
 z=a
 a[j
 a[j
 }
 }
 }
 z=w[k];
 if (1 == k) {
 if (z < 0.0)
 w [k] =
 for (j=
 }
 break;
 }
 if (its == 30)
 x=w [1];
 nm=k-1;
 y=w [nm];
 g=rv1 [nm];
 h=rv1 [k];
 f=((y-z)*(y+z));
 g=pythag(f,1.0);
 f=((x-z)*(x+z));
 c=s=1.0;
 for (j=1;j<=nm
 i=j+1;
 g=rv1[i];
 y=w[i];
 h=s*g;
 g=c*g;
 z=pythag(f,g);
 rv1[j]=z;
 c=f/z;
 s=h/z;
 f=x*c+g*s;
 g = g*c-x*s;
 h=y*s;
 y *= c;
 for (jj=1;j<=nm;jj++) {
 x=v[jj][j];
 z=v[jj][i];
 v[jj][j]=
 v[jj][i]=
 }
 z=pythag(f,g);
 w[j]=z;
 if (z) {
 z=1.0/z;
 c=f*z;
 s=h*z;
 }
 f=c*g+s*y;
 x=c*y-s*g;
 --- OCR End ---
 --- OCR Start ---
 70
 Chapter
 for (jj=1;
 y=a[jj]
 z=a[jj]
 a[jj] [j
 a[jj] [i
 }
 }
 rv1[1]=0.0;
 rv1 [k]=f;
 w [k]=x;
 }
 }
 free\_vector(rv1,1,n);
 }
 \#include <math.h>
 \#include "nrutil.h"
 float pythag(float a, float b)
 Computes (a² + b²)<sup>1/2</sup> without
 {
 float absa, absb;
 absa=fabs(a);
 absb=fabs(b);
 if (absa > absb) return
 else return (absb == 0.0 ? absa : absb*sqrt(1.0+(absa/absb)*(absa/absb)));
 }
 (Double precision versions dsvbksb, and dpythag, and also a routine to make the conversions, or else are on the diskette.)
 CITED REFERENCES AND FORMULAS
 Golub, G.H., and Van Loan, C.F. 1983, *Matrix Computations* (Baltimore: Johns Hopkins University Press), §8.3 and §5.2.6.
 Lawson, C.L., and Hanson, R.J. 1974, *Solving Least Squares Problems* (Englewood Cliffs, NJ: Prentice-Hall), Chapter 11.
 Forsythe, G.E., Malcolm, M.A., and Moler, C.B. 1977, *Computer Methods for Mathematical Computations* (Englewood Cliffs, NJ: Prentice-Hall).
 Wilkinson, J.H., and Reinsch, C. 1971, *Handbook for Automatic Computation, Vol. 2, Linear Algebra* (New York: Springer-Verlag).
 Dongarra, J.J., et al. 1979, LINPACK User's Guide (Philadelphia: SIAM).
 Smith, B.T., et al. 1976, *Matrix Eigensystem Routines—EISPACK Guide* (Lecture Notes in Computer Science, vol. 6, 2nd ed.; New York: Springer-Verlag).
 Stoer, J., and Bulirsch, R. 1980, *Introduction to Numerical Analysis* (New York: Springer-Verlag), §6.7. [4]
 Golub, G.H., and Van Loan, C.F. 1989, *Matrix Computations*, 2nd ed. (Baltimore: Johns Hopkins University Press), §5.2.6.
 --- OCR End ---
 --- OCR Start ---
 2
 2.7 Sparse Line
 A system of linear equations
 of its matrix elements $a_{ij}$
 linear algebra on such problems
 devoted to solving the set of equations.
 Furthermore, you might want to save
 memory space, and it is worthwhile
 Note that there are two distinct
 matrix method: saving time and saving
 We have already considered a
 diagonal matrix. In the tridiagonal case,
 both time (order $N$ instead of $N^3$) and
 method of solution was not based on
 decomposition; it was just a simple
 of zero elements. Many practical
 same character. They are fundamentally
 schemes akin to Gauss-Jordan
 of so-called fill-ins, initially
 solution process, and for which
 Direct methods for solving such systems
 precise pattern of sparsity
 useful as way-stations in the
 names and special methods
 review of these. Reference
 "in" to the specialized literature
 2.7.1) will at least let you
 • tridiagonal
 • band diagonal (or banded)
 • band triangular
 • block diagonal
 • block tridiagonal
 • block triangular
 • cyclic banded
 • singly (or doubly)
 • singly (or doubly)
 • singly (or doubly)
 • singly (or doubly)
 • other (!)
 You should also be aware
 solution of partial differential
 If your particular pattern of sparsity. The fact
 try an analyze/factorize/operate to find
 out how fill-ins are to be minimized to fit
 pattern of sparsity. The factorization
 fits the pattern. The operation

 --- OCR End ---
 --- OCR Start ---
 72
 Chapter
 (a)
 (d)
 (g)
 zeros
 zeros
 (j)
 Figure 2.7.1. Some standard form
 tridiagonal; (d) singly bordered by
 block triangular; (g) bordered band;
 and (k) other! (after Tewarson)
 be used with the particular
 library [4] has an analyze/factorize
 routines for sparse matrix
 Sparse Matrix Package [6].
 You should be aware
 --- OCR End ---
 --- OCR Start ---
 2
 prescribed by a sparse matrix
 operations, generally acts to
 to, e.g., regular $LU$ decom
 make its nonzero matrix elements
 will sometimes ameliorate
 In the remainder of this section,
 to some general classes of sparse matrices. The
 details of the pattern of sparsity will be
 Sherman-Morrison
 Suppose that you have the inverse
 $A^{-1}$ of a square matrix $A$.  For
 example change one element of
 Is there any way of calculating
 your difficult labors? Yes,
 for some vectors u and v.  Adding the vector v
 of v to the $i$th row. (Recall that the addition
 of the $i$th component of u and the $j$th component
 (2.7.1) adds the components of v
 to unit vectors $e_i$ and $e_j$ respectively.
 The Sherman-Morrison formula is
 briefly as follows:
 $(A + u \otimes v)^{-1} = (1 + A^{-1}u \otimes v)^{-1} A^{-1}$
 $= (1 - A^{-1}u \otimes v A^{-1}v)^{-1} A^{-1}$
 $= A^{-1} - A^{-1}uv A^{-1}$
 $= A^{-1} - \frac{A^{-1}uv A^{-1}}{1 + vA^{-1}u}$
 where
 The second line of (2.7.2) is a consequence of the
 associativity of outer and inner products.
 The use of (2.7.2) is to
 perform two matrix multiplications
 $z = A^{-1}u$
 to get the desired change
 --- OCR End ---
 74
 Chapter

 The whole procedure requires
 even smaller number if you use
 The Sherman-Morrison
 problems. If you already have a
 tridiagonal matrix, or something close,
 you to build up to your relevant
 row or column at a time. More
 than once successive corrections
 (equation 2.7.5). Of course, there is
 an $N^3$ method. The constant
 better direct methods, but you must
 of pivoting — so be careful.
 For some other sparse matrices,
 directly applied for the simplest
 is not feasible. If you want to
 and solve the linear system
 then you proceed as follows:
 the matrix A, solve the two
 for the vectors y and z.  I

 as we see by multiplying
 Cyclic Tridiagonal Systems

 So-called cyclic tridiagonal systems
 example of how to use the Sherman-
 The equations have the form
 $\begin{bmatrix}
 b_1 & c_1 & 0 & \dots & a_N \\
 a_2 & b_2 & c_2 & \dots & 0 \\
 \vdots & \vdots & \vdots & \ddots & \vdots
 \end{bmatrix}
 \alpha$

 This is a tridiagonal system.
 Forms like this are typically associated
 with periodic boundary conditions.
 We use the Sherman-Morrison
 a correction. In the notation
 --- OCR Start ---
 2
 Here γ is arbitrary for the matrix in (2.7.9), with two
 $b_1'$
 We now solve equations (2.7.10) and (2.7.11) to
 get the solution from equation (2.7.9).
 The routine cyclic boundary condition requires the
 parameter γ = −$b_1$ to avoid singularity in
 (2.7.11). In the unlikely event of singularity in
 these equations, you can modify the routine.

 #include "nrutil.h"
 void cyclic(float a[], float b[], float c[],
 	float r[], float x[1..n])
 Solves for a vector x[1..n] that is the solution
 b, c, and r are input vectors, and a, b, c are
 entries in the matrix. The input vector x is
 {
 	void tridag(float a[], float b[], float c[],
 		float r[], float x[1..n], unsigned long n);
 	unsigned long i;
 	float fact, gamma, *bb, *u, *z;

 	if (n <= 2) nrerror("n must be >2 in cyclic");
 	bb=vector(1,n);
 	u=vector(1,n);
 	z=vector(1,n);
 	gamma = -b[1];
 	bb[1]=b[1]-gamma;
 	bb[n]=b[n]-alpha*beta/gamma;
 	for (i=2; i<n; i++) bb[i]=b[i];
 	tridag(a,bb,c,r,x,n);
 	u[1]=gamma;
 	u[n]=alpha;
 	for (i=2; i<n; i++) u[i]=0.0;
 	tridag(a,bb,c,u,z,n);
 	fact=(x[1]+beta*x[n])/gamma;
 	for (i=1; i<=n; i++) x[i]=x[i]-fact*u[i];
 	free_vector(z,1,n);
 	free_vector(u,1,n);
 	free_vector(bb,1,n);
 }
 Woodbury Formula
 If you want to add more corrections to A repeatedly, since without storing
 problems (2.7.7) efficiently after the first correction
 is the block-matrix version of the Woodbury formula:
 $(A + U \cdot V^T)^{-1} $
 $= A^{-1} - [A^{-1} U (I + V^T A^{-1} U)^{-1} V^T A^{-1}]$
 --- OCR End ---
 76
 Chapter
 Here A is, as usual, an $N \times$
 and usually $P \ll N$. The in
 as the tableau,
 $\begin{bmatrix}
 U \\
 \cdot \\
 \cdot \\
 \cdot \\
 \end{bmatrix}
 \begin{bmatrix}
 1+ \\
 \end{bmatrix}$
 where you can see that the ma
 The relation between the
 Morrison formula is now clarif
 P vectors $u_1, \dots, u_P$, and $V$ is
 $U = \begin{bmatrix} u_1 \\ \end{bmatrix}$
 then two ways of expressing
 (Note that the subscripts on
 different column vectors.)
 Equation (2.7.15) reveals
 P corrections in one fell swo
 them by applying (2.7.5) P
 If you don't have storag
 To solve the linear equation
 first solve the P auxiliary p
 and construct the matrix Z b
 Next, do the $P \times P$ matrix
 Finally, solve the one further
 In terms of these quantities,

 Inversion by Partition

 Once in a while, you
 that can be inverted efficiently.
 A is partitioned into

 where P and S are square matrices.
 The matrices Q and R are
 respectively.
 If the inverse of A is
 then $\widetilde{\mathbf{P}}$, $\widetilde{\mathbf{Q}}$, $\widetilde{\mathbf{R}}$, $\widetilde{\mathbf{S}}$, which has
 found by either the formulas

 $\widetilde{\mathbf{P}} = (\mathbf{P} - \mathbf{Q} \cdot \mathbf{S}^{-1} \cdot \mathbf{R})^{-1}$
 $\widetilde{\mathbf{Q}} = -(\mathbf{P} - \mathbf{Q} \cdot \mathbf{S}^{-1} \cdot \mathbf{R})^{-1} \cdot \mathbf{Q} \cdot \mathbf{S}^{-1}$
 $\widetilde{\mathbf{R}} = -(\mathbf{S}^{-1} \cdot \mathbf{R})$
 $\widetilde{\mathbf{S}} = \mathbf{S}^{-1} + (\mathbf{S}^{-1} \cdot \mathbf{R}) \cdot (\mathbf{P} - \mathbf{Q} \cdot \mathbf{S}^{-1} \cdot \mathbf{R})^{-1} \cdot (\mathbf{Q} \cdot \mathbf{S}^{-1})$

 or else by the equivalent set

 $\widetilde{\mathbf{P}} = \mathbf{P}^{-1} + (\mathbf{P}^{-1} \cdot \mathbf{Q}) \cdot (\mathbf{S} - \mathbf{R} \cdot \mathbf{P}^{-1} \cdot \mathbf{Q})^{-1} \cdot (\mathbf{R} \cdot \mathbf{P}^{-1})$
 $\widetilde{\mathbf{Q}} = -(\mathbf{P}^{-1} \cdot \mathbf{Q})$
 $\widetilde{\mathbf{R}} = -(\mathbf{S} - \mathbf{R} \cdot \mathbf{P}^{-1} \cdot \mathbf{Q})^{-1} \cdot (\mathbf{R} \cdot \mathbf{P}^{-1})$
 $\widetilde{\mathbf{S}} = (\mathbf{S} - \mathbf{R} \cdot \mathbf{P}^{-1} \cdot \mathbf{Q})^{-1}$

 The parentheses in equations (2.7.24) and (2.7.25) may be
 you may wish to compute
 do the matrix multiplication in
 equation (2.7.24) and (2.7.25) before using the
 simpler formula; or on whether
 --- OCR Start ---
 78
 Chapter
 to calculate than the expression
 and S; or on whether P$^{-1}$
 Another sometimes uses the
 matrix,
 det A = det P det(S
 Indexed Storage of
 We have already seen (§2) a storage
 format that allocates storage only
 locations to make the bookkeeping
 sparse matrix of dimension $N$ (lower
 case), it is surely inefficient —
 $N^2$ elements. Even if one dictates
 machine time to loop over all the
 Obviously some kind of indexed
 matrix elements, along with some
 logically belongs and how to do the
 operations. Unfortunately, there is not
 one method. The Yale Sparse
 Matrix Package methods. The
 sparse storage mode, is that it
 matrix elements. (Other methods
 we will treat only the case of symmetric
 To represent a matrix A using
 one-dimensional arrays, call them
 in single or double precision as follows:
 • The first $N$ locations are used for the
 diagonal elements are stored. This is an
 inefficiency, since diagonal elements
 • Each of the first $N$ locations holds
 the first off-diagonal element. If there are
 no off-diagonal elements, this location is
 most recently stored.
 • Location 1 of ija is a pointer to the
 • Location $N+1$ of ija is the
 element of the last row of the matrix.
 Location $N+1$ of sa is 0.
 • Entries in sa at locations 1 through $N$ are
 rows and, within each row, are stored
 • Entries in ija at locations 1 through $N$ are
 element in sa.
 While these rules seem complicated, they form a
 scheme. As an example, consider
 --- OCR End ---
 --- OCR Start ---
 2
 In row-indexed compact storage
 11, as follows
 \begin{tabular}{|c|c|c|}
 \hline
 index k & 1 & 2 \\
 \hline
 ija[k] & 7 & 8 \\
 \hline
 sa[k] & 3. & 4. \\
 \hline
 \end{tabular}
 Here $x$ is an arbitrary value.
 (namely 5) is ija[1]-2, and
 The diagonal element in row
 sa[k] where k loops from i
 the lower one (as in C's for
 Here is a routine, sprsin
 sparse storage mode, throwing
 Of course, the principal use of
 won't fit into your machine at
 Nevertheless sprsin is useful
 subscale testing of large problems.
 furnishes the impetus to sparse
 \#include <math.h>
 void sprsin(float **a, int n, int nmax,
 unsigned long ija[])
 Converts a square matrix a[1..n][1..n] to
 ments of a with magnitude > tolerance tol,
 sion nmax (an input parameter) is the maxi-
 number of elements filled of sa
 \{
 void nrerror(char error\_text[])
 int i,j;
 unsigned long k;
 for (j=1;j<=n;j++) sa[j]=a[j][j];
 ija[1]=n+2;
 k=n+1;
 for (i=1;i<=n;i++) \{
 for (j=1;j<=n;j++) \{
 if (fabs(a[i][j]) > tol) \{
 if (++k > nmax) nrerror("sprsin:k>nmax");
 sa[k]=a[i][j];
 ija[k]=j;
 \}
 \}
 \}
 ija[i+1]=k+1;
 \}
 \}
 The single most important use of
 multiply a vector to its right.
 The following routine is thus
 void sprsax(float sa[], unsigned long ija[],
 unsigned long n)
 Multiply a matrix in row-index
 a vector b[1..n].
 \{
 void nrerror(char erro
 --- OCR End ---
 --- OCR Start ---
 80
 Chapter
 unsigned long i,k;
 if (ija[1] != n+2) nre
 for (i=1;i<=n;i++) {
 b[i]=sa[i]*x[i];
 for (k=ija[i];k<=i
 b[i] += sa[k]*
 }
 }
 It is also simple to multiply the transpose of a matrix
 this operation later in this section.
 void sprstx(float sa[], unsigned long n)
 Multiply the transpose of a matrix
 x[1..n], giving a vector b[1..n].
 {
 void nrerror(char error,
 unsigned long i,j,k;
 if (ija[1] != n+2) nrerror
 for (i=1;i<=n;i++) b[i]
 for (i=1;i<=n;i++) {
 for (k=ija[i];k<=i
 j=ija[k];
 b[j] += sa[k]*
 }
 }
 }
 (Double precision versions of these routines are provided
 by the routine atimes later in this chapter.  The
 the converted routines from the single precision routines.
 In fact, because the changes must be made so
 differently, it is quite an involved process.  The sparse
 matrix itself in row-indexed storage is organized
 is done as follows: An index is constructed for the
 (see §8.4). The elements are sorted by row.  When an
 element is written, its row is automatically determined, and
 are sorted by row.
 void sprstp(float sa[], unsigned long n)
 Construct the transpose of a sparse matrix, whose
 ija into arrays sb and ijb.
 {
 void iindexx(unsigned long n, unsigned long *arr)
 Version of indexx with all the changes.
 unsigned long j,jl,jm,
 float v;
 n2=ija[1];
 for (j=1;j<=n2-2;j++)
 iindexx(ija[n2-1]-ija[
 Index all off-diagonal elements of the sparse matrix.
 jp=0;
 for (k=ija[1];k<=ija[n
 m=ijb[k]+n2-1;
 sb[k]=sa[m];
 for (j=jp+1;j<=ija
 --- OCR End ---
 jp=ija[m];
 jl=1;
 ju=n2-1;
 while (ju-j1 > 1)
 jm=(ju+j1)/2;
 if (ija[jm] >
 }
 ijb [k]=jl;
 }
 2
 for (j=jp+1;j<n2;j++)
 for (j=1;j<=n2-2;j++)
 jl=ijb[j+1]-ijb[j]
 noff=ijb[j]-1;
 inc=1;
 do {
 inc *= 3;
 inc++;
 } while (inc <= jl
 do {
 inc /= 3;
 for (k=noff+in
 iv=ijb[k];
 v=sb [k];
 m=k;
 while (ijb
 ijb [m] =
 sb [m] =s
 m = im
 }
 if (m-m
 }
 }
 ijb[m]=iv;
 sb [m] =v;
 } while (inc > 1);
 }
 The above routine embed
 routine iindexx to construct
 as listed in §8.4, except that th
 (The Numerical Recipes disk
 often use indexx without ma
 that numerical values will so
 floating or integer values.
 As final examples of the
 multiplication of two sparse ma
 In general, the product
 to limit the size of the product
 of the product that are specifie
 nonzero elements, but store on
 former technique, when it cam
 by furnishing an index array
 then constructs a correspondin
 excessive compute times and
 With row-index storage,
 the transpose of a matrix (on
 rows on columns. Our routin
 that you have to run your rig
 sending it to the matrix mult


 --- OCR Start ---
 82
 Chapter
 The two implementing routines
 multiply" are quite similar in
 combinations of diagonal or off-diagonal
 void sprspm(float sa[], unsigned long n,
 float sc[], unsigned long m,
 Matrix multiply $A \cdot B^T$ where $A$ is
 $B^T$ is the transpose of $B$. Here
 This routine computes only the
 input index array ijc, which is
 matrix in row-index storage mode,
 preceded by a call to sprstp;
 {
 void nrerror(char error\_text[]);
 unsigned long i,ijma, ijb, j, k, l, m,
 float sum;
 if (ija[1] != ijb[1] || ija[1] != ijc[1])
 nrerror("sprspm: s");
 for (i=1;i<=ijc[1]-2;i++) {
 j=m=i;
 mn=ijc[i];
 sum=sa[i]*sb[i];
 for (;;) {
 mb=ijb[j];
 for (ma=ija[i];ma<=ija[i+1]-1;ma++) {
 Loop through elements to find
 various combinations of
 ijma=ija[ma];
 if (ijma == mb) {
 sum += sa[ma]*sb[j];
 } else {
 while (ijma < mb) {
 ijma=ija[++ma];
 if (ijma > mb) break;
 }
 if (ijma == mb) {
 sum += sa[ma]*sb[j];
 } else {
 break;
 }
 }
 }
 break;
 }
 }
 for (mbb=mb;mbb<=ijb[j+1]-1;mbb++) {
 if (ijb[mbb] != ijma) continue;
 sc[m]=sum;
 sum=0.0;
 if (mn >= ijc[i+1]) break;
 j=ijc[m=mn++];
 }
 }
 #include <math.h>
 void sprstm(float sa[], unsigned long n,
 float thresh, unsigned long m,
 --- OCR End ---
 ```
 --- OCR Start ---
 2
 Matrix multiply A. $B^T$ where
 $B^T$ is the transpose of B. Her
 B. This routine computes all c
 but stores only those whose m
 (whose maximum size is input
 For sparse matrix multiplicatio
 to construct the transpose of
 {
 void nrerror (char erro
 unsigned long i,ijma, i
 float sum;
 if (ija[1] != ijb[1])
 ijc[1]=k=ija[1];
 for (i=1;i<=ija[1]-2;i
 for (j=1;j<=ijb [1]
 if (i == j) sum
 mb=ijb[j];
 for (ma=ija[i]
 Loop through ele
 various combinat
 ijma=ija[ma
 if (ijma ==
 else {
 while (C
 ijm
 if
 } e
 } e
 }
 bre
 }
 }
 }
 for (mbb=mb;mbl
 if (ijb[mbb
 }
 if (i == j) sc
 else if (fabs(:
 if (k > nma
 sc [k]=sum;
 ijc [k++]=j=
 }
 }
 ijc [i+1]=k;
 }
 }
 Conjugate Gradient
 So-called conjugate gra
 $N \times N$ linear system
 The attractiveness of these m
 through its multiplication of a
 --- OCR End ---
 ```
 84
 Chapter

 we have seen, these operations:
 the "owner" of the matrix $A$.
 matrix multiplications as efficient
 routine, linbcg below, that sometimes
 The simplest, "ordinary"
 case that $A$ is symmetric and positive definite.

 This function is minimized when
 is zero, which is equivalent to a
 succession of search directions
 is found that minimizes $f(x_k)$.
 The $p_k$ and $x_k$ are built up in
 vector space of directions already found.
 the minimizer over the entire space.
 Later, in §10.6, we will
 minimization of arbitrary non-
 but not necessarily positive definite
 important, the biconjugate gradient
 connection with function minimization.
 $\bar{p}_k$, $k=1, 2, \dots$. You supply
 you carry out the following

 This sequence of vectors satisfies
 and the biconjugacy condition
 $\bar{p}_i$.

 There is also a mutual orthogonality.

 The proof of these properties
 recurrence does not break down
 terminate after $m \le N$ steps when
 $N$ steps you run out of new orthogonal vectors.
 To use the algorithm to find a
 solution. Choose $r_1$ to be the initial
 and choose $\bar{r}_1 = r_1$. Then for


 --- OCR Start ---
 2
 while carrying out the recurrence is in fact the residue
 $x_{m+1}$ is the solution to equation
 While there is no guarantee of convergence for general $A$, in practice
 most $N$ iterations occurs only when a genuine error
 criterion is met. The ordinary conjugate gradient
 algorithm when $A$ is symmetric can be simplified;
 $k$; you can omit computing the product $A \cdot p_k$
 version has the interpretation as well as symmetric, the algorithm
 indeed reduces to the ordinary conjugate gradient method.
 It does all the redundant computations. Another variant of the
 algorithm, for definite $A$, with the choice $r_k = A \cdot p_k$ for all $k$. This
 algorithm, but with all dot products is the same as the
 algorithm, because it corresponds to the ordinary conjugate gradient method
 where the successive iterates $x_k$ are defined by the conjugate gradient method
 for unsymmetric matrices. The conjugate gradient method is
 probably the most robust of general methods. Note that equation (2.7
 For any nonsingular matrix $A$, one might be tempted to solve equation
 to the problem
 Don't! The condition number of $A$ (see §2.6 for definition of condition number)
 number of iterations required, is almost always better to apply preconditioning.
 So far we have said nothing about using the ordinary conjugate gradient method
 "close" to the identity matrix.
 form of equation (2.7.29),
 The idea is that you might already have an approximation $\tilde{A}$
 to $A$, in which case $\tilde{A}^{-1} \cdot A$ is called a preconditioned
 preconditioned biconjugate gradient method.
 For efficient implementation, we introduce $z_k$ and $\bar{z}_k$ defined by
 $\tilde{A}$.
 --- OCR End ---
 --- OCR Start ---
 86
 Chapter
 and modifies the definitions o
 For linbcg, below, we will as
 (2.7.42). If you have no idea
 of A, or even the identity ma
 on the biconjugate gradient
 The routine linbcg, belo
 (See [13] for a different, less
 should know about.
 What constitutes "good
 linbcg therefore provides fo
 If itol=1, iteration stops wh
 tol. If itol=2, the require
 $\tilde{A}$
 If itol=3, the routine uses i
 divided by the magnitude of x.
 except that the largest (in absc
 are used instead of the vector
 may need to experiment to fin
 On output, err is the t
 not indicate that the maximum
 should be less than tol. If yo
 they are and call the routine a
 gradient subspace between ca
 than about every $N$ iteration
 Finally, note that linbcg
 used when $N$ is quite large.
 #include <stdio.h>
 #include <math.h>
 #include "nrutil.h"
 #define EPS 1.0e-14
 void linbcg(unsigned long j;
 int itmax, int *iter,
 Solves A $\cdot$ x = b for x[1..n]
 On input x[1..n] should be s
 or 4, specifying which converg
 of allowed iterations; and tol
 reset to the improved solution,
 estimated error. The matrix A
 which computes the product of
 $\tilde{A} \cdot x = b$ or $A^T \cdot x = b$ for some
 {
 void asolve(unsigned 1
 void atimes(unsigned 1
 double snrm(unsigned l
 unsigned long j;
 double ak, akden, bk, bkd
 double *p, *pp, *r, *rr,*
 --- OCR End ---
 --- OCR Start ---
 /*
 p=dvector(1,n);
 pp=dvector (1,n);
 r=dvector(1,n);
 rr=dvector (1,n);
 z=dvector(1,n);
 zz=dvector (1,n);
 Calculate initial residual.
 *iter=0;
 atimes(n,x,r,0);
 for (j=1;j<=n;j++) {
 r[j]=b[j]-r[j];
 rr[j]=r[j];
 }
 atimes(n,r,rr,0); */
 if (itol == 1) {
 }
 bnrm=snrm(n,b,itol);
 asolve(n,r,z,0);
 else if (itol == 2) {
 }
 asolve (n,b,z,0);
 bnrm=snrm(n,z,itol);
 asolve(n,r,z,0);
 else if (itol == 3 ||
 asolve (n,b,z,0);
 bnrm=snrm(n,z,itol);
 asolve(n,r,z,0);
 znrm=snrm(n,z,itol);
 } else nrerror("illegal");
 while (*iter <= itmax) {
 ++(*iter);
 asolve(n, rr,zz, 1);
 for (bknum=0.0,j=1
 Calculate coefficient
 if (*iter == 1) {
 for (j=1;j<=n;
 p[j]=z[j];
 pp[j]=zz [j];
 }
 }
 else {
 bk=bknum/bkden;
 for (j=1;j<=n;
 p[j]=bk*p[j];
 pp[j]=bk*pp[j];
 }
 }
 bkden=bknum;
 atimes(n,p,z,0);
 for (akden=0.0,j=1
 ak=bknum/akden;
 atimes (n,pp,zz, 1);
 for (j=1;j<=n;j++) {
 x[j] += ak*p[j];
 r[j] -= ak*z[j];
 rr[j] -= ak*zz[j];
 }
 asolve(n,r,z,0);
 if (itol == 1)
 *err=snrm(n,r,itol);
 else if (itol == 2)
 *err=snrm(n,z,itol);
 --- OCR End ---
 --- OCR Start ---
 88
 Chapter
 else if (itol == 3){
 zm1nrm=znrm;
 znrm=snrm(n,z,itol);
 if (fabs(zm1nrm-znrm) < tol){
 dxnrm=fabs(znrm);
 *err=znrm/fabs(dxnrm);
 } else {
 *err=znrm/b;
 continue;
 }
 xnrm=snrm(n,x,itol);
 if (*err <= tol) break;
 else {
 *err=znrm/b;
 continue;
 }
 }
 printf("iter=%4d err=%14.7e\n",iter,*err);
 if (*err <= tol) break;
 }
 free_dvector(p,1,n);
 free_dvector(pp,1,n);
 free_dvector(r,1,n);
 free_dvector(rr,1,n);
 free_dvector(z,1,n);
 free_dvector(zz,1,n);
 The routine linbcg uses
 #include <math.h>
 double snrm(unsigned long n,double sx[],unsigned long itol){
 Compute one of two norms for
 {
 unsigned long i,isamax;
 double ans;
 if (itol <= 3) {
 ans = 0.0;
 for (i=1;i<=n;i++)
 return sqrt(ans);
 } else {
 isamax=1;
 for (i=1;i<=n;i++)
 if (fabs(sx[i]) > fabs(sx[isamax])) isamax=i;
 return fabs(sx[isamax]);
 }
 }
 So that the specification
 simple versions that assume a
 extern unsigned long ija[];
 extern double sa[];
 void atimes(unsigned long n,double x[],double b[]);
 {
 void dsprsax(double sa[],unsigned long ija[],unsigned long n);
 --- OCR End ---
 void dsprstx(double sa
 unsigned long n);
 These are double versions
 if (itrnsp) dsprstx(sa
 else dsprsax(sa,ija,x,
 }
 extern unsigned long ija[];
 extern double sa[];
 void asolve(unsigned long
 {
 unsigned long i;
 for(i=1;i<=n;i++) x[i]
 The matrix $\tilde A$ is the diag
 transpose matrix has the
 CITED REFERENCES AND P
 Tewarson, R.P. 1973, Sparse M
 Jacobs, D.A.H. (ed.) 1977, The
 Chapter 1.3 (by J.K. Reic
 George, A., and Liu, J.W.H. 198
 (Englewood Cliffs, NJ: P
 NAG Fortran Library (Numerica
 [4]
 IMSL Math/Library Users Manu
 Eisenstat, S.C., Gursky, M.C., s
 age, Technical Reports 11
 Knuth, D.E. 1968, Fundamental
 MA: Addison-Wesley), §2
 Kincaid, D.R., Respess, J.R., Y
 ematical Software, vol. 8
 PCGPAK User's Guide (New H
 Bentley, J. 1986, Programming
 Golub, G.H., and Van Loan, C.F
 University Press), Chapte
 Stoer, J., and Bulirsch, R. 1980
 Chapter 8. [12]
 Baker, L. 1991, More C Tools f
 Fletcher, R. 1976, in Numerica
 A. Dold and B Eckmann,
 Saad, Y., and Schulz, M. 1986
 pp. 856–869. [15]
 Bunch, J.R., and Rose, D.J. (
 Press).
 Duff, I.S., and Stewart, G.W.
 S.I.A.M.).
 --- OCR Start ---
 90
 Chapter
 2.8 Vandermonde Matrices
 In §2.4 the case of a
 particular type of linear system
 rather than of order $N^3$ for
 exist, it is important to know
 ever happen to be working
 type, can be enormous.
 This section treats two
 $N^2$ operations, not as good
 (Other than the operations
 Matrices of the first type,
 having to do with the fitting
 their moments, and also other
 problem crops up in §3.5.
 tend to occur in problems
 book, a Toeplitz problem in
 These are not the only
 Hilbert matrices, whose coefficients $c_i$ which fit a polynomial
 1,..., N can be inverted
 invert in any other way, since
 The Sherman-Morrison and
 be used to convert new special forms. We have no time for that.
 the two that we now discuss.
 Vandermonde Matrices
 A Vandermonde matrix is defined by a set of
 numbers $x_1, x_2, \dots, x_N$, in the form
 $x_i^{j-1}$, $i, j = 1, \dots, N$. Evidently,
 we view the $i$'s as rows, $j$'s as columns, we have a
 system of equations that looks like
 $\begin{bmatrix}
 1 & x_1 \\
 1 & x_2 \\
 \vdots & \vdots \\
 1 & x_N
 \end{bmatrix}$
 Performing the matrix multiplication will yield
 coefficients $c_i$ which fit a polynomial.
 Precisely this problem will arise in the
 method that we are about to
 --- OCR End ---
 --- OCR Start ---
 2.8 Vanderm
 The alternative identifica
 $\begin{bmatrix}
 1 \\
 x_1 \\
 x_1^2 \\
 \vdots \\
 x_1^{N-1}
 \end{bmatrix}$
 Write this out and you will see that given the values
 of $N$ points $x_i$, find the unknown coefficients
 $q_j$ of the first $N$ moments.  (Our discussion in
 this section solves (2.8.2).
 The method of solution is based on polynomial interpolation formulas.  Under-
 standing, the following derivation is useful:
 Let $P_j(x)$ be the polynomial
 Here the meaning of the last row is crucial.  The
 coefficients that arise when the polynomial is expressed in
 powers of $x$ are designed in such a way as to give
 The polynomial $P_j(x)$ is
 specifically designed so that its value is one at $x = x_j$ and zero at $x = x_k$ for
 $k \ne j$.  In other words, $P_j(x)$ is a delta function.
 But (2.8.4) says that $A_{jk}$
 appears in (2.8.2), with the sum
 is just that matrix inverse times $q$.
 As for the transpose problem, the transposed matrix
 is the transpose of the inverse matrix.
 The routine in §3.5 implements this.
 It remains to find a good way
 to get the components of $A_{jk}$.
 read the routine itself to see how this is done. You
 work out its coefficients, and then to proceed
 via synthetic division by the one polynomial.
 Since each such division is one step in the process,
 You should be warned that these processes have limitations in
 their very nature. (As an aside, they do not compare with
 Chebyshev fitting so impressive for
 good uniform fits to zero. Hence the
 of the leading terms of these polynomials are only accurate to
 problems in double precision
 --- OCR End ---
 --- OCR Start ---
 92
 Chapter
 The routine for (2.8.2)
 #include "nrutil.h"
 void vander (double x [], double q[], double w[])
 Solves the Vandermonde linear system $Aw = q$, where $A_{ij} = x_i^{j-1}$ using the vectors x[1..n] and q[1..n].
 {
 int i,j,k;
 double b,s,t,xx;
 double *c;
 c=dvector(1,n);
 if (n == 1) w[1]=q[1];
 else {
 for (i=1;i<=n;i++)
 c[n] = -x[1];
 for (i=2;i<=n;i++) {
 xx = -x[i];
 for (j=(n+1-i);j<=n;j++)
 c[n] += xx;
 }
 for (i=1;i<=n;i++) {
 xx=x[i];
 t=b=1.0;
 s=q[n];
 for (k=n;k>=2;k--) {
 b=c[k]+xx*b;
 s += q[k-1]*b;
 t=xx*t+b;
 }
 w[i]=s/t;
 }
 }
 free_dvector(c,1,n);
 }
 Toeplitz Matrices
 An $N \times N$ Toeplitz matrix has the form
 $1, \dots, -1, 0, 1, \dots, N - 1$.
 along the (upper-left to lower
 $\begin{bmatrix}
 R_0 & R_{-1} & \dots & R_{-N+1} \\
 R_1 & R_0 & R_{-1} & \dots \\
 \vdots & R_1 & R_0 & \vdots \\
 R_{N-1} & \dots & R_1 & R_0
 \end{bmatrix}$
 The linear Toeplitz problem
 $\sum_{j=1}^N$
 where the $x_j$'s, $j = 1, \dots, N$
 The Toeplitz matrix is s
 algorithm for fast solution of t
 --- OCR End ---
 --- OCR Start ---
 2.8 Vanderm
 a recursive procedure th
 $M$
 $\sum_{j=1}$
 in turn for $M = 1, 2, \dots$ until
 is the result at the $M$th stage,
 the method generalizes to the
 of excessive detail, we therefore
 In following a recursion
 $x^{(M)}$ changes in this way:
 $\sum_{j=1}^M$
 becomes
 $\sum_{j=1}^M R_{i-j} x_j^{(M+1)} + F$
 By eliminating $y_i$ we find
 $\sum_{j=1}^M R_{i-j} \left( \frac{x_j^{(M)} -}{x_j^{(M)}} \right)$
 or by letting $i \to M + 1 -$
 where
 To put this another way,
 $x_{M+1-j}^{(M+1)} =$
 Thus, if we can use recursion
 order $M + 1$ quantity $x_{M+1}^{(M+1)}$ follows from
 $\sum_{j=1}^M$
 For the unknown order $M -$
 quantities in $G$ since
 R
 The result of this operation
 $x_{M+}^{(M+1}$
 --- OCR End ---
 94
 Chapter
 The only remaining problem for a
 that, however, we should point out that the
 original linear problem (which we
 have been discussing) and left-hand side
 differs only in that we deal with
 M
 ∑
 j=1
 Then, the same sequence of operations
 where
 (compare with 2.8.14 – 2.8.1
 that, by equation (2.8.21), the
 the substitution $y_i \rightarrow R_i$ on
 equation (2.8.19) that
 $H^{(M-1)}_{M+1}$
 By the same token, $G$ satisfies
 This gives
 $G^{(M+1)}_{M+1}$
 The same "morphism" also turns out to be true
 for
 $G_j^{(M+1)}$
 $H_j^{(M+1)}$
 Now, starting with the
 $x_1^{(1)} = y_1/F$
 we can recurse away. At each step we have
 $H^{(M+1)}$, $G^{(M+1)}$, and then equation
 so that the vectors $x^{(M+1)}_i$
 The program below does
 $H^{(M+1)}$
 so that the computation can
 does not allow pivoting, the algorithm fails. The
 original Toeplitz matrix vanishes at this point
 (§2.4). If the algorithm fails, you should solve your problem by a simple
 to solve your problem by a similar procedure with pivoting.
 The routine that implements this
 that the routine's r[n+j] is equal to
 1 to 2N − 1.
 --- OCR Start ---
 2.8 Vanderm
 #include "nrutil.h"
 #define FREERETURN {free_
 void toeplz (float r[], float y[], float x[])
 Solves the Toeplitz system $\sum_{j=1}^n r_{i-j+1} x_j = y_i$, $i=1, \dots, n$.  The Toeplitz matrix need
 not be symmetric. y [1..n] and x[1..n] are input and output vectors, respectively.
 {
 int j,k,m,m1, m2;
 float pp, pt1, pt2,qq, qt1, qt2;
 float *g,*h;
 if (r[n] == 0.0) nrerror("toeplz: r[n]=0.");
 g=vector (1,n);
 h=vector(1,n);
 x[1]=y [1]/r[n];
 if (n == 1) FREERETURN
 g[1]=r[n-1]/r[n];
 h[1]=r[n+1]/r[n];
 for (m=1;m<=n;m++) {
 m1=m+1;
 sxn = -y [m1];
 sd = -r [n];
 for (j=1;j<=m;j++) {
 sxn += r[n+m1-j]*x[j];
 sd += r[n+m1-j]*g[j];
 }
 if (sd == 0.0) nrerror("toeplz: sd=0.");
 x[m1]=sxn/sd;
 for (j=1;j<=m;j++) {
 if (m1 == n) FREERETURN
 sgn = -r[n-m1];
 shn = -r[n+m1];
 sgd = -r[n];
 for (j=1;j<=m;j++) {
 sgn += r[n+j-m1]*g[j];
 shn += r[n+m1-j]*h[j];
 sgd += r[n+j-m1]*h[j];
 }
 }
 if (sgd == 0.0) nrerror("toeplz: sgd=0.");
 g[m1]=sgn/sgd;
 h[m1]=shn/sd;
 k=m;
 m2=(m+1) >> 1;
 pp=g[m1];
 qq=h [m1];
 for (j=1;j<=m2;j++) {
 pt1=g[j];
 pt2=g [k];
 qt1=h[j];
 qt2=h [k];
 g[j]=pt1-pp*qt2;
 g[k]=pt2-pp*qt1;
 h[j]=qt1-qq*pt2;
 h[k--]=qt2-qq*pt1;
 }
 }
 nrerror("toeplz - should not get here");
 }
 If you are in the business
 so-called "new, fast" algorithm
 compared to $N^2$ for Levinson
 --- OCR End ---
 --- OCR Start ---
 96
 Chapter
 Papers by Bunch [6] and de H
 CITED REFERENCES AND F
 Golub, G.H., and Van Loan, C.F.
 University Press), Chapte
 Forsythe, G.E., and Moler, C.E.
 wood Cliffs, NJ: Prentice
 Westlake, J.R. 1968, A Handbo
 (New York: Wiley). [2]
 von Mises, R. 1964, Mathema
 Press), pp. 394ff. [3]
 Levinson, N., Appendix B of
 Stationary Time Series (
 Robinson, E.A., and Treitel, S. 1
 Hall), pp. 163ff. [5]
 Bunch, J.R. 1985, SIAM Journa
 de Hoog, F. 1987, Linear Algeb
 2.9 Cholesky D
 If a square matrix A h
 special, more efficient, triang
 $i, j = 1, \dots, N$, while positi
 (In Chapter 11 we will see th
 all positive eigenvalues.) Whi
 occur quite frequently in som
 decomposition, is good to kno
 a factor of two faster than alte
 Instead of seeking arbit
 decomposition constructs a lo
 the upper triangular part. In c
 This factorization is sometime
 components of $L^T$ are of cou
 Writing out equation (2.9.2)
 (2.3.12)-(2.3.13),
 and
 $L_{ji} = \frac{1}{L_{ii}} \left( a$
 --- OCR End ---
 --- OCR Start ---
 2.5
 If you apply equations
 that the $L$'s that occur on the
 needed. Also, only components
 these have complete information
 subdiagonal (lower triangular
 upper triangular values of $A$. Components
 part of $L$. The operations consist of
 multiply and one subtract), which is a
 factor 2 better than $LU$ decomposition.
 A straightforward implementation
 #include <math.h>
 void choldc (float **a, int n, float *p)
 Given a positive-definite symmetric matrix $a$, this routine
 decomposition: $A = L \cdot L^T$. Components
 modified. The Cholesky factor
 elements which are returned in
 {
 void nrerror (char error_text[])
 int i,j,k;
 float sum;
 for (i=1;i<=n;i++) {
 for (j=i;j<=n;j++) {
 for (sum=a[i][j],k=i-1;k>=1;k--)
 if (i == j) {
 if (sum <= 0.0)
 nrerror("Cholesky decomposition failed");
 p[i]=sqrt(sum);
 } else a[j][i]=sum/p[i];
 }
 }
 }
 You might at this point
 decomposition is extremely stable. A failure
 simply indicates that the matrix $a$ is
 not positive definite. In fact,
 is positive definite. (In this application, a
 some less drastic signaling routine
 Once your matrix is decomposed, solve the
 equation by backsubstitution.
 void cholsl (float **a, int n, float *p, float b[], float x[])
 Solves the set of n linear equations $a \cdot x = b$. Here
 $a[1..n][1..n]$ and $p[1..n]$ are as
 subdiagonal portion of $a$ is a
 solution vector is returned in $x$.
 for successive calls with different
 $x$ in the calling sequence, which is
 {
 int i,k;
 float sum;
 for (i=1;i<=n;i++) {
 for (sum=b[i],k=i-1;k>=1;k--)
 x[i]=sum/p[i];
 for (i=n;i>=1;i--) {
 for (sum=x[i],k=i+1;k<=n;k++)
 --- OCR End ---
 --- OCR Start ---
 98
 Chapter
 x[i]=sum/p[i];
 }
 }
 A typical use of choldc is
 the fit of data to a model; see, e.g.,
 L⁻¹. The lower triangle of this matrix is
 for (i=1;i<=n;i++) {
 a[i][i]=1.0/p[i];
 for (j=i+1;j<=n;j++) {
 sum=0.0;
 for (k=i;k<j;k++) {
 a[j][i]=sum/p[i];
 }
 }
 }
 CITED REFERENCES AND FURTHER READING
 Wilkinson, J.H., and Reinsch, C., eds. 1971. Handbook for automatic computation (New York: Springer-Verlag), vol. 2, Linear algebra.
 Gill, P.E., Murray, W., and Wright, M.H. 1981. Practical optimization (Redwood City, CA: Addison-Wesley).
 Dahlquist, G., and Bjorck, A. 1974. Numerical methods. Englewood Cliffs, NJ: Prentice-Hall, §5.3.5.
 Golub, G.H., and Van Loan, C.F. 1983. Matrix computations (Baltimore: Johns Hopkins University Press), §4.2.
 2.10 QR Decomposition
 There is another matrix
 decomposition,
 Here R is upper triangular, where
 where Qᵀ is the transpose matrix. For a rectangular matrix, we shall require that Q be a square matrix with dimensions N × N.
 Like the other matrix factorization methods, this decomposition can be used to solve systems of linear equations. We first form Qᵀ⋅b and then solve Rb = Qᵀ⋅b by backsubstitution. Since Q is orthogonal, unlike the LU decomposition, it is not usually necessary to make any special provisions to meet special cases where QF is singular.
 --- OCR End ---
 --- OCR Start ---
 The standard algorithm
 transformations (to be discussed
 can zero all elements in a column.
 arrange for the first Householder
 the first element. Similarly $Q_1$
 element, and so on up to $Q_{n-1}$.
 Since the Householder matrices
 $Q = I - \frac{uu^T}{c}$ where $c = \frac{1}{2} u^T u$.
 In most applications we don't need pivoting
 form (2.10.6). Pivoting is not required.
 A general QR algorithm for real
 matrices, an implementation

 #include <math.h>
 #include "nrutil.h"
 void qrdcmp(float **a, int n, float *d, int *sing)
 Constructs the QR decomposition of
 turned in the upper triangle of
 d[1..n]. The orthogonal matrices
 $Q_1 \dots Q_{n-1}$, where $Q_j = I - uu^T/c$.
 while the nonzero components
 true (1) if singularity is encountered;
 completed in this case; otherwise

 {
 int i,j,k;
 float scale, sigma, sum, *c;
 *sing=0;
 for (k=1;k<n;k++) {
 scale=0.0;
 for (i=k;i<=n;i++)
 if (scale == 0.0)
 *sing=1;
 c [k]=d[k]=0.0;
 } else {
 for (i=k;i<=n;i++)
 for (sum=0.0,i=k;i<=n;i++)
 sigma=SIGN(sqrt(sum),a[k][k]);
 a[k] [k] += sigma;
 c [k]=sigma*a [k] [k];
 d[k] = -scale*sigma;
 for (j=k+1;j<=n;j++)
 for (sum=0.0,i=k;i<=n;i++)
 tau=sum/c[k];
 for (i=k;i<=n;i++)
 }
 }
 }
 d[n]=a[n] [n];
 if (d[n] == 0.0) *sing=1;
 The next routine, qrsol
 part (2.10.4) of the algorithm
 --- OCR End ---
 ```
 --- OCR Start ---
 100
 Chapter
 void qrsolv(float **a, int
 Solves the set of n linear equa
 input as the output of the ro
 right-hand side vector, and is
 {
 void rsolv (float **a,
 int i,j;
 float sum, tau;
 for (j=1;j<n;j++) {
 }
 for (sum=0.0,i=j;i
 tau=sum/c[j];
 for (i=j;i<=n;i++)
 rsolv(a,n,d,b);
 }
 void rsolv(float **a, int
 Solves the set of n linear equa
 a and d. a [1..n] [1..n] an
 are not modified. b [1..n] is
 solution vector on output.
 {
 int i,j;
 float sum;
 b[n] = d[n];
 for (i=n-1;i>=1;i--) {
 for (sum=0.0,j=i+1
 b[i]=(b[i]-sum)/d[
 }
 }
 See [2] for details on how
 and for solving least-squares
 because of its greater diagnos
 Updating a QR dec
 Some numerical algorith
 differs only slightly from its
 to solve the equations from s
 operations and use the new fa
 decomposition is complicated
 quite simple for a very com
 (compare equation 2.7.1). In p
 A=QF
 One can go back and forth b
 is orthogonal, giving
 t = v
 The algorithm [2] has tw
 reduce R + uv to upper He
 upper Hessenberg matrix to th
 product of Q with the 2(N
 the algorithm can easily be re
 --- OCR End ---
 ```
 --- OCR Start ---
 #include <math.h>
 #include "nrutil.h"
 void qrupdt (float **r, float **qt, int n, float *u, float *v)
 Given the QR decomposition
 matrix Q. (R+uv). The quadratic form is given by
 u[1..n], and v [1..n]. Note that r is an n x n matrix.
 {
 void rotate(float **r, float **qt, int n, int i, float *u)
 int i,j,k;
 for (k=n;k>=1;k--) {
 if (u[k]) break;
 }
 if (k < 1) k=1;
 for (i=k-1;i>=1;i--) {
 rotate(r,qt,n,i,u[i]);
 if (u[i] == 0.0) u[i]=0.0;
 else if (fabs(u[i]) > fabs(u[i+1])) u[i]=fabs(u[i]);
 else u[i]=fabs(u[i+1]);
 }
 for (j=1;j<=n;j++) r[1][j]=0.0;
 for (i=1;i<k;i++)
 rotate(r, qt,n,i,r[i][1]);
 #include <math.h>
 #include "nrutil.h"
 void rotate (float **r, float **qt, int n, int i, float *u)
 Given matrices r [1..n] [1..n] and qt [1..n] [1..n].
 i and i + 1 of each matrix. a and b are elements of r.
 sin θ = b/√a² + b².
 {
 int j;
 float c, fact,s,w,y;
 if (a == 0.0) {
 c=0.0;
 s=(b >= 0.0 ? 1.0 : -1.0);
 } else if (fabs(a) > fabs(b)) {
 fact=b/a;
 c=SIGN(1.0/sqrt(1.0+fact*fact));
 s=fact*c;
 } else {
 fact=a/b;
 s=SIGN(1.0/sqrt(1.0+fact*fact));
 c=fact*s;
 }
 for (j=i;j<=n;j++) {
 y=r[i][j];
 w=r[i+1][j];
 r[i][j]=c*y-s*w;
 r[i+1][j]=s*y+c*w;
 }
 for (j=1;j<=n;j++) {
 y=qt [i][j];
 w=qt [i+1][j];
 qt [i][j]=c*y-s*w;
 qt [i+1][j]=s*y+c*w;
 }
 }
 --- OCR End ---
 102
 Chapter
 We will make use of $Q$.
 CITED REFERENCES AND F
 Wilkinson, J.H., and Reinsch, c
 putation (New York: Springer-Verlag),
 Golub, G.H., and Van Loan, C.F.
 University Press), §§5.2,
 2.11 Is Matrix Ir
 We close this chapter
 itation which probes more
 with a seemingly simple c
 How many individual
 tiplication of two 2 $\times$ 2 m
 $\begin{pmatrix} a_{11} \\ a_{21} \end{pmatrix}$
 Eight, right? Here they ar
 Do you think that one
 multiplications? (Try it yo
 Such a set of formulas
 $Q_1$
 $Q_2$
 $Q_3$
 $Q_4$
 $Q_5$
 $Q_6$
 $Q_7$
 --- OCR Start ---
 2.11 Is M
 in terms of which

 What's the use of this
 (2.11.2), but many more advantages
 has been gained. But notice
 Therefore (2.11.3) and (2.11.
 The problem of multiplying
 integer m) can now be broken down
 quarters, sixteenths, etc. A
 "7/8"; it is that factor at each
 the process of matrix multiplication.
 What about all the extra
 the advantage of the fewer
 six times as many additions
 if N is very large, this converts
 from N³ to Nlog₂7.
 With this "fast" matrix
 for matrix inversion [1].  S
 $\begin{pmatrix} a \\ a \end{pmatrix}$
 are inverses of each other. The
 operations (compare equations
 --- OCR End ---
 --- OCR Start ---
 104
 Chapter
 In (2.11.6) the "inverse
 reciprocal if the $a$'s and $c$'s
 themselves submatrices. Im
 $N = 2^m$, recursively by pa
 the number of inverse opera
 all! So divisions don't dom
 is dominated, in fact, by its
 algorithm, so can the mat
 This is fun, but let's lo
 before the difference betwe
 enough to outweigh the boo
 of the recursive Strassen a
 immediate danger of beco
 If, on the other hand,
 multiply the complex numb
 [Answer: see §5.4.] (2) C
 $x$ for many different value
 [Answer: see §5.3.]
 CITED REFERENCES AND F
 Strassen, V. 1969, Numerische
 Kronsjö, L. 1987, Algorithms: 1
 Winograd, S. 1971, Linear Alg
 Pan, V. Ya. 1980, SIAM Journa
 Pan, V. 1984, How to Multiply
 (New York: Springer-Verl
 Pan, V. 1984, SIAM Review, vol
 of 2.496 can be achieved
 --- OCR End ---
 Chapter 3.
 3.0 Introduction
 We sometimes know the values of a function
 (say, with $x_1 < \dots < x_N$), and we want to
 us calculate its value at an arbitrary point.  In
 some physical measurement, one might fit
 into a simple functional form.
 The task now is to estimate the value of this
 smooth curve through (and perhaps beyond) the
 largest and smallest of the known points.  Within
 that range, it is called extrapolation.  (In
 former stock-market analyses, this procedure
 Interpolation and extrapolation beyond
 beyond the known points.  The methods we shall
 be sufficiently general so as to cover any case
 which might arise in practice.  The functions
 used are polynomials (§3.1) and these turn
 out to be extremely useful.  Later chapters give
 rise to trigonometric interpolation methods.
 Chapters 12 and 13.  There is an extensive theory.
 sort of functions can be well approximated.  The
 theorems are, alas, almost useless because they do not tell us
 enough about our function to take us out of
 the pitiful state of having too little information.
 Interpolation is related to approximation.  It
 consists of finding an approximation to the value
 of a more complicated one.  But it is not possible to assume
 at points not of your own choosing.  We are
 allowed to compute the function value at these points,  and thus to improve
 your approximation. We describe these ideas.  One can easily find particular
 lation scheme.  Consider,
 --- OCR Start ---
 106
 Cha
 which is well-behaved even
 and otherwise takes on all
 the values $x = 3.13, 3.14,$
 the value $x = 3.1416$, even
 quite smooth! (Try it on
 Because pathologies can
 lation and extrapolation require
 an error estimate can never be
 for reasons known only to
 two tabulated points. Interpolation
 for the function interpolates
 from smoothness can be controlled.
 Conceptually, the interpolation
 function to the data points
 the target point $x$. However, this two-stage
 practice. Typically it is controlled by
 roundoff error, than methods which use
 from the $N$ tabulated values
 at a nearby point $f(x_i)$, the
 as information from other points.
 $O(N^2)$ operations. If even the
 smallest, and it can be used
 In the case of polynomials, the
 coefficients of the interpolation
 in evaluating the interpolated
 eventuality in §3.5.
 Local interpolation, uses the
 interpolated values $f(x)$ to
 derivatives. That happens if
 interpolation scheme switches,
 a switch is allowed to occur in
 interpolated function itself.
 In situations where a
 the "stiffer" interpolation
 a polynomial between each pair of
 determined "slightly" nonlinear
 smoothness in the interpolation
 (§3.3) are the most popular.
 through the second derivative
 possibility of wild oscillations.
 The number of points determines
 the order of the interpolation and
 the accuracy, especially in
 from the point of interest $x$,
 constrained points, tends to
 oscillation may have no relationship.
 Figure 3.0.1). Of course, accuracy
 --- OCR End ---
 --- OCR Start ---
 (a)
 (b)
 Figure 3.0.1. (a) A smooth function accurately approximated by a polynomial (shown schematically by a linear dashed line). (b) A function that cannot be accurately approximated by a high-degree polynomial (dashed lines). Even a low-degree polynomial can be badly approximated by high-degree polynomials.
 but a finer mesh implies a higher-degree polynomial. Unless there is solid evidence that the interpolant approximates the true function $f$, it is a waste of time to go beyond low-degree polynomials. We enthusiastically endorse the use of low-degree polynomials (3, 4, or 5 or 6; but we rarely go beyond degree 6) to approximate functions and the estimation of errors.
 When your table of values is used to build an interpolating function, you must be certain that there is adequate information in the table. While no fixed rules work in all cases, the following considerations are important enough (and often crucial):
 The routines given for interpolation are important in many important applications, including the numerical solution of differential equations. The basic problem is to estimate the interpolation errors. Otherwise, the data may cause your interpolating function, which otherwise would work, to go berserk when the argument is slightly outside the range of the table. Interpolation can be computationally expensive, and the typical spacing of tabular data may preclude high accuracy.
 --- OCR End ---
 --- OCR Start ---
 108
 Cha
 $f(x, y, z)$. Multidimensional
 one-dimensional interpolation
 CITED REFERENCES AND F
 Abramowitz, M., and Stegun, I
 matics Series, Volume 55
 Dover Publications, New
 Stoer, J., and Bulirsch, R. 1980
 Chapter 2.
 Acton, F.S. 1970, Numerical M
 matical Association of Ar
 Kahaner, D., Moler, C., and Na
 NJ: Prentice Hall), Chap
 Johnson, L.W., and Riess, R.
 Wesley), Chapter 5.
 Ralston, A., and Rabinowitz, P.
 McGraw-Hill), Chapter 3.
 Isaacson, E., and Keller, H.B. 15
 3.1 Polynomial
 Through any two points
 unique quadratic. Et cetera
 the $N$ points $y_1 = f(x_1)$
 Lagrange's classical formula
 $P(x) = \frac{(x - x_2)(x - x_3)\dots(x - x_N)}{(x_1 - x_2)(x_1 - x_3)\dots(x_1 - x_N)} y_1$
 $+ \dots + \frac{(x - x_1)(x - x_2)\dots(x - x_{N-1})}{(x_N - x_1)(x_N - x_2)\dots(x_N - x_{N-1})} y_N$
 There are $N$ terms, each a
 zero at all of the $x_i$ except
 It is not terribly wrong,
 but it is not terribly right either;
 it is also somewhat awkward,
 the same, unique, interpolating
 and sometimes confused with
 Let $P_1$ be the value
 a constant) passing through
 $P_2, P_3, \dots, P_N$. Now let
 degree one passing through
 $P_{(N-1)N}$. Similarly, for higher
 of the unique interpolating
 --- OCR End ---
 --- OCR Start ---
 3.1 Polynom
 The various $P$'s form a ``t
 ``descendant'' at the extrem
 $x_1$:
 $x_2$:
 $x_3$:
 $x_4$:
 Neville's algorithm is
 a column at a time, from
 ``daughter'' $P$ and its two
 $P_{i(i+1)...(i+m)} = \frac{(x - }{}$
 This recurrence works bec
 $x_{i+m-1}$.
 An improvement on
 differences between parent
 $N - 1)$,
 $C_m$
 $D_m$
 Then one can easily derive
 $D_{m+1}$,
 $C_{m+1}$,
 At each level $m$, the $C$'s an
 order higher. The final ans
 and/or $D$'s that form a path
 Here is a routine for
 points. Note that the inp
 zero-offset arrays, rememb
 #include <math.h>
 #include "nrutil.h"
 void polint(float xa[], fl
 Given arrays xa[1..n] and ya
 an error estimate dy. If $P(x)$
 1,..., n, then the returned va
 {
 int i,m,ns=1;
 float den,dif, dift, ho,
 --- OCR End ---
 --- OCR Start ---
 110
 Cha
 float *c,*d;
 dif=fabs(x-xa[1]);
 c=vector(1,n);
 d=vector(1,n);
 for (i=1;i<=n;i++) {
 if ((dift=fabs(x-
 ns=i;
 }
 dif=dift;
 }
 c[i]=ya[i];
 d[i]=ya[i];
 *y=ya [ns--];
 for (m=1;m<n;m++) {
 for (i=1;i<=n-m;i+
 ho=xa [i]-x;
 hp=xa [i+m]-x;
 }
 w=c[i+1]-d[i];
 if ((den-ho-h
 This error can oc
 den=w/den;
 d[i]=hp*den;
 c[i]=ho*den;
 *y += (*dy=(2*ns <
 After each column in
 we want to add to ou
 tableau-forking up c
 line" route through th
 where we are. This ro
 on the target x. The
 }
 free_vector(d,1,n);
 free_vector(c,1,n);
 Quite often you will
 and ya replaced by actua
 polint(&xx [14], &yy [14
 ulated values xx [15..18]
 CITED REFERENCES AND F
 Abramowitz, M., and Stegun,
 matics Series, Volume 55
 Dover Publications, New
 Stoer, J., and Bulirsch, R. 1980
 §2.1.
 Gear, C.W. 1971, Numerical Ini
 Cliffs, NJ: Prentice-Hall),
 --- OCR End ---
 --- OCR Start ---
 3.2 Rational Fu
 3.2 Rational Function
 Extrapolation
 Some functions are
 approximated by rational
 note by $R_{i(i+1)...(i+m)}$ a
 $(x_i, y_i)...(x_{i+m}, y_{i+m})$.
 $R_{i(i+1)...(i+}$
 Since there are $\mu + \nu + 1$
 In specifying a rational function
 order of both the numerator
 Rational functions are
 because of their ability to model
 of equation (3.2.1). These
 to be interpolated itself has
 finite real $x$, but has an arbitrary
 Such poles can themselves
 real values of $x$, just as the
 in $x$. If you draw a circle
 then you should not expect
 pole is rather far outside the
 will stay "good" as long as
 for (cancel) any nearby poles.
 For the interpolation
 through a chosen set of data
 mention in passing that rational
 work. One sometimes considers
 that the rational function
 that agrees with the first $m$
 function $f(x)$. This is called
 Bulirsch and Stoer for
 rational function extrapolation
 (3.1.2) is constructed colour
 The Bulirsch-Stoer algorithm
 the degrees of numerator and
 of the denominator larger than
 derivation of the algorithm,
 --- OCR End ---
 --- OCR Start ---
 112
 Chap
 relation exactly analogous to
 $R_i(i+1)...(i+m) = R_i(i+$
 $+$
 This recurrence generates the terms $R_i(i+1)...(i+m)$
 through $m$ and (the term $R_{i+m}$ is not generated)
 with
 and with
 $R = [R$
 Now, exactly as in equation (3.2.3), we reduce this
 recurrence (3.2.3) to one in
 $C_m$
 $D_m$
 Note that these satisfy the recurrence relations
 $C_m$
 which is useful in proving
 $D_{m+1,i} =$
 $C_{m+1,i} =$
 This recurrence is implemented
 in every way to polint
 assumed (§1.2).
 #include <math.h>
 #include "nrutil.h"
 #define TINY 1.0e-25
 #define FREERETURN {free_vector(c,1,n);free_vector(d,1,n);return}
 void ratint (float xa[], float ya[], int n, float x, float y, float *dy)
 Given arrays xa[1..n] and ya[1..n], and given a value of x, this routine
 y and an accuracy estimate $dy$ of the interpolating function
 evaluated at x, which passes through the n points (xa[i],ya[i]).
 \{
 int m,i,ns=1;
 float w,t,hh,h,dd, *c, *d;
 --- OCR End ---
 ```
 c=vector(1,n);
 d=vector(1,n);
 hh=fabs(x-xa[1]);
 for (i=1;i<=n;i++) {
 h=fabs(x-xa[i]);
 if (h == 0.0) {
 *y=ya[i];
 *dy=0.0;
 FREERETURN
 } else if (h < hh) {
 ns=i;
 hh=h;
 }
 }
 c[i]=ya[i];
 d[i]=ya[i]+TINY;
 *y=ya[ns--];
 for (m=1;m<n;m++) {
 for (i=1;i<=n-m;i++) {
 w=c[i+1]-d[i];
 h=xa[i+m]-x;
 t=(xa[i]-x)*d[i];
 dd=t-c[i+1];
 if (dd == 0.0) {
 This error condition
 requested value
 dd=w/dd;
 d[i]=c[i+1]*dd;
 c[i]=t*dd;
 }
 }
 *y += (*dy=(2*ns <
 FREERETURN
 CITED REFERENCES AND FORMULAS
 Stoer, J., and Bulirsch, R. 1980
 §2.2. [1]
 Gear, C.W. 1971, Numerical Initial Value Problems in Ordinary Differential Equations (Englewood Cliffs, NJ: Prentice-Hall),
 Cuyt, A., and Wuytack, L. 1987
 Holland), Chapter 3.
 3.3 Cubic Spline
 Given a tabulated function $y=f(x)$ over a
 particular interval, between two adjacent points
 the interpolation formula
 ```
 --- OCR Start ---
 114
 Cha
 where
 $A = \frac{x_j -}{x_j +}$
 Equations (3.3.1) and (3.3.2
 formula (3.1.1).
 Since it is (piecewise
 the interior of each interval
 abscissas $x_j$. The goal of cu
 that is smooth in the first c
 within an interval and at i
 Suppose, contrary to
 also have tabulated values
 of numbers $y_j''$. Then, wit
 equation (3.3.1) a cubic po
 value $y_j''$ on the left to a val
 continuous second derivati
 zero values at $x_j$ and $x_{j+1}$
 tabulated functional values
 A little side calculati
 construction, namely repla
 $y =$
 where A and B are define
 $\frac{1}{6}(A^3 - A)(x_j +$
 Notice that the dependence
 (3.3.4) is entirely through t
 B) the cubic $x$-dependenc
 We can readily check
 interpolating polynomial.
 using the definitions of A, E
 The result is
 $\frac{dy}{dx} = \frac{y_{j+1} - y_j}{x_{j+1} - x_j} - \frac{3A^2}{6}$
 for the first derivative, an
 for the second derivative.
 other way around, (3.3.6) s
 also that the second derivati
 the two intervals ($x_{j-1}$, $x_j$
 --- OCR End ---
 --- OCR Start ---
 3.3
 The only problem now
 they are not. However, we
 from equation (3.3.5), be co
 key idea of a cubic spline i
 for the second derivatives
 The required equation
 $x = x_j$ in the interval $(x_{j-}$
 in the interval $(x_j, x_{j+1})$. V
 $x_j - x_{j-1} \quad x_{j+1} - x_j$
 $ \frac{ }{6} y''_{j-1} + \frac{ }{3} $
 These are $N - 2$ linear equ
 there is a two-parameter fa
 For a unique solution,
 as boundary conditions at $x$
 • set one or both of
 cubic spline, which
 boundaries, or
 • set either of $y_1''$ and
 to make the first de
 value on either or
 One reason that cubic
 (3.3.7), along with the two
 also tridiagonal. Each $y_j''$ is
 the equations can be solved
 That algorithm is concise e
 This makes the routine not
 so we encourage you to stu
 are assumed to be unit-offs
 #include "nrutil.h"
 void spline(float x[], flo
 Given arrays x[1..n] and y[
 $x_1 < x_2 < ... < x_N$, and give
 function at points 1 and n, res
 the second derivatives of the i
 $y_{pn}$ are equal to $1 \times 10^{30}$ or
 condition for a natural spline,
 \{
 int i,k;
 float p,qn,sig,un, *u;
 u=vector(1,n-1);
 if (yp1 > 0.99e30)
 y2[1]=u[1]=0.0;
 else \{
 y2[1] = -0.5;
 u[1]=(3.0/(x[2]-x[
 \}
 --- OCR End ---
 --- OCR Start ---
 116
 }
 Cha
 for (i=2;i<=n-1;i++) {
 sig=(x[i]-x[i-1])/
 }
 p=sig*y2[i-1]+2.0;
 y2[i]=(sig-1.0)/p;
 u[i]=(y[i+1]-y[i])
 u[i]=(6.0*u[i]/(x[
 if (ypn > 0.99e30)
 qn=un=0.0;
 else {
 }
 qn=0.5;
 un=(3.0/(x[n]-x[n-
 y2 [n]=(un-qn*u[n-1])/(
 for (k=n-1;k>=1;k--)
 y2 [k]=y2 [k]*y2 [k+1]
 free_vector(u,1,n-1);
 It is important to understand that it is necessary to process an entire tabulated function (and store the values of the interpolated function at each tabulated point, as desired) to a separate row of storage.
 void splint (float xa[], float ya[], float y2a[], int n, float x, float *y)
 {
 void nrerror(char error_text[]);
 int klo, khi,k;
 float h,b,a;
 klo=1;
 khi=n;
 while (khi-klo > 1) {
 k=(khi+klo) >> 1;
 if (xa [k] > x) khi=k;
 else klo=k;
 }
 h=xa [khi]-xa [klo];
 if (h == 0.0) nrerror("bad xa input to splint");
 a=(xa [khi]-x)/h;
 b=(x-xa [klo])/h;
 *y=a*ya [klo]+b*ya [khi]
 }
 CITED REFERENCES AND FURTHER READING
 De Boor, C. 1978, A Practical Guide to Splines (New York: Springer-Verlag).
 Forsythe, G.E., Malcolm, M.A., and Moler, C.B. 1977, Computer Methods for Mathematical Computations (Englewood Cliffs, NJ: Prentice-Hall), §4.8.
 Stoer, J., and Bulirsch, R. 1980, Introduction to Numerical Analysis (New York: Springer-Verlag), §2.4.
 Ralston, A., and Rabinowitz, P. 1978, A First Course in Numerical Analysis, 2nd ed. (New York: McGraw-Hill), §3.8.
 --- OCR End ---
 --- OCR Start ---
 3.4 How to Search
 3.4 Suppose that you have
 such as fourth-order polynomials
 set of tabulated $x_i$'s and $f_i$'s
 in the table of $x_i$'s, given some $x$
 is desired. This problem is
 often in practice that it would
 Formally, the problem
 with the elements either more
 given a number $x$, find an
 For this task, let us define
 plus or minus infinity (in which
 table). Then $j$ will always
 "off-scale" at one end of the
 In most cases, when a
 which will find the right place
 bisection in the spline evaluation
 might glance back at that.
 void locate(float xx[], unsigned long ju,jm,jl
 Given an array xx[1..n], and
 and $x_{j+1}$. xx must be monotonic
 to indicate that x is out of range.
 \{
 unsigned long ju,jm,jl;
 int ascnd;
 j1=0;
 ju=n+1;
 ascnd=(xx[n] >= xx[1]);
 while (ju-jl > 1) \{
 jm=(ju+jl) >> 1;
 if (x >= xx[jm]) == ascnd)
 jl=jm;
 \}
 else
 ju=jm;
 \}
 if (x == xx[1]) *j=1;
 else if (x == xx[n]) *j=n;
 else *j=jl;
 \}
 A unit-offset array xx
 remember to subtract 1 from
 Search with Correlation
 Sometimes you will be generating a function
 and with nearly identical
 may be generating a function: Most differential
 --- OCR End ---
 --- OCR Start ---
 118
 Cha
 1
 (a)
 8
 ↓
 hunt phase
 1
 (b)
 7 10 14
 Figure 3.4.1. (a) The routine 1
 of steps that converge to element
 previous known position in the ta
 particularly unfavorable example,
 be convergence to an element nea
 for right-hand side evaluat
 trend moves slowly in the
 In such cases it is was
 following routine instead st
 either up or down, in incre
 bracketed. Second, it then
 about a factor of 2 slower t
 the whole table). At best, it
 point is usually quite close t
 void hunt (float xx[], unsi
 Given an array xx[1..n], an
 xx[jlo] and xx[jlo+1]. x
 jlo=0 or jlo=n is returned t
 initial guess for jlo on outpu
 {
 unsigned long jm,jhi,i
 int ascnd;
 ascnd=(xx[n] >= xx[1])
 if (*jlo <= 0 || *jlo
 *jlo=0;
 jhi=n+1;
 } else {
 inc=1;
 if (x >= xx[*jlo]
 if (*jlo == n)
 jhi=(*jlo)+1;
 while (x >= xx
 *jlo=jhi;
 inc += inc;
 jhi=(*jlo)+
 if (jhi >
 jhi=n+1
 break;
 }
 --- OCR End ---
 --- OCR Start ---
 3.4 Ho
 }
 } else {
 if (*jlo == 1)
 }
 *jlo=0;
 return;
 jhi=(*jlo)--;
 while (x < xx [
 jhi=(*jlo);
 inc <<= 1;
 if (inc >=
 *jlo=0;
 break;
 }
 else *jlo=
 }
 }
 }
 while (jhi-(*jlo) != 1
 jm=(jhi+(*jlo)) >>
 if (x >= xx[jm] ==
 *jlo=jm;
 else
 jhi=jm;
 }
 }
 if (x == xx [n]) *jlo=n
 if (x == xx [1]) *jlo=1
 If your array xx is zer
 After the Hunt
 The problem: Routin
 desired value lies between t
 full length of the table. Bu
 like polint (§3.1) or rat
 arrays, of length m. How
 The solution: Calcul
 k = IM
 (The macros IMIN and I
 arguments; see §1.2 and A
 leftmost member of an m-p
 j and j+1, but bounded by
 interpolation routine with a
 poli
 CITED REFERENCES AND F
 Knuth, D.E. 1973, Sorting and
 MA: Addison-Wesley), SE
 --- OCR End ---
 --- OCR Start ---
 120
 Chap.
 3.5 Coefficients
 Occasionally you may
 that passes through a (small) poly-
 nomial. A valid use of
 simultaneous interpolated values (see
 §5.3), or to convolve a segment,
 where the moments of that segment
 are known analytically. However, please be certain
 coefficients of the interpolation are used
 than its value at a desired argument. These
 coefficients only for use in interpolation will
 will not pass exactly through the tabulated points.
 by the routines in §3.1–§3.3.
 Also, you should not resort to this
 for its cousin, the best fit process, since the number of data
 process, since the number of data points. The
 determined even in the presence of small
 §14.8.) Interpolation, where the data
 points are equal, takes the tabulated
 errors, these can be magnified considerably
 between the tabulated points.
 As before, we take the polynomial; the
 polynomial is written as
 $y = \sum_{i=0}^N c_i x^i$
 then the $c_i$'s are required to satisfy
 $\begin{bmatrix} 1 & x_0 & x_0^2 & \cdots & x_0^N \\
 1 & x_1 & x_1^2 & \cdots & x_1^N \\
 \vdots & \vdots & \vdots & \ddots & \vdots \\
 1 & x_N & x_N^2 & \cdots & x_N^N \end{bmatrix}
 \begin{bmatrix} c_0 \\ c_1 \\ \vdots \\ c_N \end{bmatrix} = \begin{bmatrix} y_0 \\ y_1 \\ \vdots \\ y_N \end{bmatrix}$
 This is a Vandermonde matrix; the
 equation (3.5.2) by standard methods (see
 the special method that was developed for
 order $N$, so it is much better.
 Remember that Vandermonde matrices are ill-conditioned; in this
 case, no numerical method should be used. Do
 not, please note, imply any use of the methods
 of §3.1, but only difficulty should be expected.
 Like the routine in §2.6, all input
 arrays are all assumed to
 --- OCR End ---
 --- OCR Start ---
 3.5 Coefficie
 #include "nrutil.h"
 void polcoe (float x[], float y[], int n, float cof[])
 Given arrays x [0..n] and y[0..n]
 returns an array of coefficients
 {
 int k,j,i;
 float phi, ff,b,*s;
 s=vector(0,n);
 for (i=0;i<=n;i++) s[i]=y[i];
 s[n] = -x[0];
 for (i=1;i<=n;i++) {
 for (j=n-i;j<=n-1;j++)
 s[j] -= x[i]*s[j+1];
 s[n] = x[i];
 }
 for (j=0;j<=n;j++) {
 phi=n+1;
 for (k=n;k>=1;k--)
 phi=k*s [k]+x[j]*(phi-k);
 ff=y[j]/phi;
 b=1.0;
 for (k=n;k>=0;k--) {
 cof [k] += b*ff;
 b=s [k]+x[j]*b;
 }
 }
 free_vector(s,0,n);
 }
 Another Method
 Another technique is
 already given (polint §3.1). For
 the interpolating polynomial
 we can subtract $c_0$ from the
 out one point (the one with the
 procedure to find $c_1$, and
 It is not instantly obvious,
 found it to be somewhat more
 method is of order $N^3$, we
 find, however, that neither
 ill-condition of the Vandermonde
 satisfactory; about double
 #include <math.h>
 #include "nrutil.h"
 void polcof(float xa[], float ya[], int n, float cof[])
 Given arrays xa [0..n] and y[0..n]
 routine returns an array of coefficients
 {
 void polint(float xa[], float ya[], int n, float x, float *y, float *dy);
 int k,j,i;
 float xmin,dy, *x, *y;
 --- OCR End ---
 --- OCR Start ---
 122
 }
 x=vector(0,n);
 y=vector(0,n);
 Cha
 for (j=0;j<=n;j++) {
 x[j]=xa[j];
 y[j]=ya[j];
 }
 for (j=0;j<=n;j++) {
 polint(x-1,y-1,n+1
 Subtract 1 from the p
 extrapolate to $x = 0$
 xmin=1.0e38;
 k = -1;
 for (i=0;i<=n-j;i+
 if (fabs(x[i])
 xmin=fabs(x
 k=i;
 if (x[i]) y[i]:
 }
 for (i=k+1;i<=n-j;
 y[i-1]=y[i];
 x[i-1]=x[i];
 }
 }
 free_vector(y,0,n);
 free_vector(x,0,n);
 If the point $x = 0$ is n
 then the coefficients of the in
 However, the real "inform=
 from the "translation-induc
 resulting in loss of signifi
 consider redefining the orig
 Another pathology is
 a smooth function, the inte
 coefficients, in combination
 to match the tabulated valu
 effect is the same as the int
 oscillate (wildly) between
 machine's floating precisio
 polcof have slightly differ
 Are you still quite cer
 CITED REFERENCES AND F
 Isaacson, E., and Keller, H.B.
 --- OCR End ---
 3.6 Interpolation
 In multidimensional interpolation from an $n$-dimensional grid giving the tabulated values $x_n$. We will not here consider Cartesian, i.e., has tabulated space rather than at the vertices explicitly only the case of 2 dimensions, being analogous in every dimension. In two dimensions, we have $y_a[1..m][1..n]$. We are given the relation of these input values.
 We want to estimate, by interpolation, $(x_1, x_2)$. An important concept falls, that is, the four tabulated values. For convenience, we will number these values from the lower left (see Fig. 3.6). This defines $j$ and $k$, then
 The simplest interpolation in a grid square. Its formulas are:
 $t \equiv (x_1 - x_j)/ \Delta x_1$
 $u \equiv (x_2 - x_k)/ \Delta x_2$
 (so that $t$ and $u$ each lie between 0 and 1).
 $y(x_1, x_2) = (1 - t)(1 - u)y_{jk} + ...$
 Bilinear interpolation
 --- OCR Start ---
 124
 d2
 X₁ = x11
 Cha
 pt. (4
 desired p
 (X1,X2)
 pt. (1
 d1
 (a)
 Figure 3.6.1. (a) Labeling of p
 bcucof. (b) For each of the four
 and one cross-derivative, a total
 function value changes co
 function changes discontin
 There are two distinct
 bilinear interpolation to hig
 increased accuracy for the i
 without necessarily trying
 derivatives. Or, one can ma
 these derivatives as the inte
 now consider each of thes
 Higher Order for Ac
 The basic idea is to br
 interpolations. If we want t
 order in the x2 direction, w
 matrix that contains our d
 interpolations in the x2 dir
 values at the points (x1a [-
 in the x1 direction to get th
 polint of §3.1, and a su
 addressed through the point
 #include "nrutil.h"
 void polin2(float x1a[], f
 float x2, float *y, fl
 Given arrays x1a[1..m] and x
 values ya[1..m][1..n], tabu
 x1 and x2 of the independent
 and an accuracy indication dy
 {
 void polint(float xa[]
 --- OCR End ---
 --- OCR Start ---
 3.6 Interpolation
 int j;
 float *ymtmp;
 ymtmp=vector(1,m);
 for (j=1;j<=m;j++) {
 polint(x2a, ya[j],n,x2,
 }
 polint (x1a, ymtmp,m,x1,
 free_vector(ymtmp,1,m)
 }
 Higher Order for Surfaces
 We will give two methods
 not unrelated. The first is
 Bicubic interpolation of
 the function $y(x_1, x_2)$, but
 the cross derivative $\partial^2 y/\partial$
 cubic in the scaled coordinates
 following properties: (i) The
 are reproduced exactly on
 the specified derivatives change
 one grid square to another.
 It is important to understand
 requires you to specify the exact
 tautologically "forced," and
 derivatives. It is a separate
 are specified. The better your
 it will be smooth no matter
 Best of all is to know the
 accurately by numerical means;
 numerical differencing from
 relevant code would be something
 y1a[j][k]=(ya[j+1][k]-
 y2a[j][k]=(ya[j][k+1]-
 y12a[j][k]=(ya[j+1][k+
 /((x1a[j+1]-x1a
 To do a bicubic interpolation,
 derivatives y1, y2, y12 at each
 First obtain the sixteen quantities
 below. (The formulas that follow
 are just a complicated linear
 determined once in the midst.
 Next, substitute the c's into
 and derivatives, as desired.
 --- OCR End ---
-/

-- TODO: parse the OCR text into Lean definitions
