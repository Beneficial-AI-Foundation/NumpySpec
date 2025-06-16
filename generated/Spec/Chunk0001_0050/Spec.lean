/-
 Numerical Recipes in C

 The Art of Scientific Computing
 Second Edition

 William H. Press

 Harvard-Smithsonian Center for Astrophysics

 Saul A. Teukolsky

 Department of Physics, Cornell University

 William T. Vetterling

 Polaroid Corporation

 OMA YUON) €ZpZ-228-008

 }ayNdwod Ja/uas Aue Oo}
 lo swei6olg ‘ssalg Aysuaniuy eBpuquueg Aq 2661-8861 (D) 1yBUAdOD

 ($-80L€b-12S-0 NS!) ONILNdWOOD OISILNAIOS 4O LYV SHL 'O NI SAdIOSY TWOINSWNN Woy e6ed ajdwes

 Brian P. Flannery
 EXXON Research and Engineering Company

 “aremyos sedicay jeouewnn Aq 2661-8861 (O)

 UY YON apis}no) Bio‘ebpuquies@AsasjsnojoeuIp OF
 ‘SIWOHGD 40 syoog sedio:

 CAMBRIDGE UNIVERSITY PRESS
 Cambridge New York Port Chester Melbourne Sydney

 Published by the Press Syndicate of the University of Cambridge
 The Pitt Building, Trumpington Street, Cambridge CB2 1RP

 40 West 20th Street, New York, NY 10011-4211, USA

 477 Williamstown Road, Port Melbourne, VIC, 3207, Australia

 Copyright © Cambridge University Press 1988, 1992

 except for 813.10 and Appendix B, which are placed into the public domain,
 and except for all other computer programs and procedures, which are
 Copyright © Numerical Recipes Software 1987, 1988, 1992, 1997, 2002
 All Rights Reserved.

 Some sections of this book were originally published, in different form, in Computers
 in Physics magazine, Copyright © American Institute of Physics, 1988-1992.

 First Edition originally published 1988; Second Edition originally published 1992.
 Reprinted with corrections, 1993, 1994, 1995, 1997, 2002.
 This reprinting is corrected to software version 2.10

 Printed in the United States of America
 Typeset in TEX

 Without an additional license to use the contained software, this book is intended aq
 a text and reference book, for reading purposes only. A free license for limited use of the}
 software by the individual owner of a copy of this book who personally types one or more|
 routines into a single computer is granted under terms described on p. xvii. See the sectior
 “License Information” (pp. xvi-xviii) for information on obtaining more general licenses|
 at low cost.

 Machine-readable media containing the software in this book, with included licenses
 for use on a single screen, are available from Cambridge University Press. See the|
 order form at the back of the book, email to “orders@cup.org” (North America) o1
 “directcustserv@cambridge.org” (rest of world), or write to Cambridge University Press.
 110 Midland Avenue, Port Chester, NY 10573 (USA), for further information.

 The software may also be downloaded, with immediate purchase of a license
 also possible, from the Numerical Recipes Software Web Site (http: //www.nr.com)|
 Unlicensed transfer of Numerical Recipes programs to any other format, or to any|
 computer except one that is specifically licensed, is strictly prohibited. Technical questions
 corrections, and requests for information should be addressed to Numerical Recipes|
 Software, P.O. Box 380243, Cambridge, MA 02238-0243 (USA), email “info@nr.com”,
 or fax 781 863-1739.

 Library of Congress Cataloging in Publication Data

 Numerical recipes in C : the art of scientific computing / William H. Press

 . fet al.J. -— 2nd ed.

 Includes bibliographical references (p. ) and index.

 ISBN 0-521-43108-5

 1. Numerical analysi:
 3. C (Computer program language) I. Press, William H.
 QA297.N866 1992
 519.4'0285'53-de20 92-8876

 A catalog record for this book is available from the British Library.

 ISBN 0 521 431085 Book

 ISBN 0 521 43720 2. Example book in C

 ISBN 0 521 75037 7 C/C++ CDROM (Windows/Macintosh)
 ISBN 0 521 75035 0 Complete CDROM (Windows/Macintosh)
 ISBN 0 521 75036 9 Complete CDROM (UNIX/Linux)

 s—Computer programs. 2. Science-Mathematics—Computer programs.

 *(eoLaWy YON episyno) Bio‘eBpuquies@AJesysno}Oa1Ip 0} [EWE PUas JO ‘(AJUO BOVEWY YVON) E%PZ-ZZ8-008-| [fe 40 WOO UMMM): daY

 O'SGOM IISIA ‘SWWOHGD 40 Sy00q sedivay jEOUAWINN Japs0 OF “payiqiyoud Ajolys si ‘wayndwios Ja/as Aue 0} (auUO sy} Buipnjoul) s:
 -aulyoeul jo BulAdoo Aue Jo ‘uolonpoidas sayjin4 ‘“asn jeuosiad UMO JIAaU} 10} Adoo Jaded auo ayew O} Suasn JeUJE\U! 10} payuRJB S|

 “aremyog sedioay /eouewnn Aq 2661-886} (9) 1UBUAdOD swWesBoIg ‘ssalq AysianlU eBpUIquIeD Aq 2661-8861 (9) 1YBUAdOD

 ($-80L€b-12S-0 NS!) ONILNdWOOD OISILNAIOS 4O LYV SHL 'O NI SAdIOSY TWOINSWNN Woy e6ed ajdwes

 Contents

 Preface to the Second Edition xi
 Preface to the First Edition xiv
 License Information xvi
 Computer Programs by Chapter and Section xix
 Preliminaries 1
 1.0 Introduction 1
 1.1 Program Organization and Control Structures 5
 1.2 Some C Conventions for Scientific Computing 15
 1.3 Error, Accuracy, and Stability 28
 Solution of Linear Algebraic Equations 32
 2.0 Introduction 32
 2.1 Gauss-Jordan Elimination 36
 2.2 Gaussian Elimination with Backsubstitution 41
 2.3 LU Decomposition and Its Applications 43
 2.4 Tridiagonal and Band Diagonal Systems of Equations 50
 2.5 Iterative Improvement of a Solution to Linear Equations 55
 2.6 Singular Value Decomposition 59
 2.7 Sparse Linear Systems 71
 2.8 Vandermonde Matrices and Toeplitz Matrices 90
 2.9 Cholesky Decomposition 96
 2.10 QR Decomposition 98
 2.11 Is Matrix Inversion an N° Process? 102
 Interpolation and Extrapolation 105
 3.0 Introduction 105
 3.1 Polynomial Interpolation and Extrapolation 108
 3.2 Rational Function Interpolation and Extrapolation 111
 3.3 Cubic Spline Interpolation 113
 3.4 How to Search an Ordered Table 117
 3.5 Coefficients of the Interpolating Polynomial 120
 3.6 Interpolation in Two or More Dimensions 123

 vU
 g
 3

 S
 B
 Q
 D
 om
 oO
 2
 a
 =
 g
 i
 2
 S

 z
 4

 z
 =
 =
 =
 3
 Q
 8
 3
 2
 8
 2
 &
 8
 8
 &
 &
 iM
 x
 FS
 8
 Z
 E
 a
 3
 >
 3
 g
 g
 3
 3
 2
 Z

 SI ‘“ayndwod JeMas Aue 0} (9U0 SI

 aC

 *(eoLeWY YON episyno) Bio‘eBpuquied@AJesysno}a1Ip 0} |eWa Pues JO

 BJISGOM SIA ‘SWIOHGO 10 Syoog sedioay jeOUOWINN JapPso O| “payiqiyoud Aj 1
 -auiyoeul jo BulAdoo Aue Jo ‘uolonpoidas Jayyin4 ‘asn jeuosiad UMO sau} 410} Adoo saded auo ayew 0} Siasn JaUEU! 10} payueB SI

 ($-80L€b-12S-0 NS!) ONILNdWOOD OISILNAIOS 4O LYV SHL 'O NI SAdIOSY TWOINSWNN Woy e6ed ajdwes

 “AIEMYOS Sadioay ;eOUOWNN Aq Z661-8B6l (D) IYBUAdOD swesBOlY “‘ssalg AysIaAIUN EBpLqueD Aq 2661-8861 (D) jyBUAdOD

 vi

 Contents

 Integration of Functions

 4.0 Introduction

 4.1 Classical Formulas for Equally Spaced Abscissas
 4.2 Elementary Algorithms

 4.3 Romberg Integration

 4.4 Improper Integrals

 4.5 Gaussian Quadratures and Orthogonal Polynomials
 4.6 Multidimensional Integrals

 Evaluation of Functions

 5.0 Introduction

 5.1 Series and Their Convergence

 5.2 Evaluation of Continued Fractions

 5.3 Polynomials and Rational Functions

 5.4 Complex Arithmetic

 5.5 Recurrence Relations and Clenshaw’s Recurrence Formula
 5.6 Quadratic and Cubic Equations

 5.7 Numerical Derivatives

 5.8 Chebyshev Approximation

 5.9 Derivatives or Integrals of a Chebyshev-approximated Function
 5.10 Polynomial Approximation from Chebyshev Coefficients
 5.11 Economization of Power Series

 5.12 Padé Approximants

 5.13 Rational Chebyshev Approximation

 5.14 Evaluation of Functions by Path Integration

 Special Functions

 6.0 Introduction

 6.1 Gamma Function, Beta Function, Factorials, Binomial Coefficients

 6.2 Incomplete Gamma Function, Error Function, Chi-Square
 Probability Function, Cumulative Poisson Function

 6.3 Exponential Integrals

 6.4 Incomplete Beta Function, Student’s Distribution, F-Distribution,
 Cumulative Binomial Distribution

 6.5 Bessel Functions of Integer Order

 6.6 Modified Bessel Functions of Integer Order

 6.7 Bessel Functions of Fractional Order, Airy Functions, Spherical
 Bessel Functions

 6.8 Spherical Harmonics

 6.9 Fresnel Integrals, Cosine and Sine Integrals

 6.10 Dawson’s Integral

 6.11 Elliptic Integrals and Jacobian Elliptic Functions

 6.12 Hypergeometric Functions

 Random Numbers

 7.0 Introduction
 7.1 Uniform Deviates

 129

 129
 130
 136
 140
 141
 147
 161

 165

 165
 65
 69
 73
 76
 178
 83
 86
 90
 95
 197
 98
 200
 204
 208

 212

 212
 213

 216
 222

 226
 230
 236

 240
 252
 255
 259
 261
 271

 274

 274
 275

 Buipnjoul) say ajqepeos

 2
 @
 Fy
 2
 5
 a
 s
 =
 g
 3
 2
 ©
 5
 g
 3
 io
 3
 B
 R
 é
 °
 s
 3
 9
 B
 3
 g
 3
 8
 3
 g
 sz
 Fg

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 BJISGOM SIA ‘SWIOHGD 40 Sy00g sadioay jeoUaWINN Japso O| “payiqiyoud Ajjouys Ss! “4a}NdWOd JaAsas Aue 0} (U0 S|

 -aulyoew jo BulAdoo Aue Jo ‘uonjonpoides seyyin4 “asn yeuosied uMO

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 Contents

 Vii

 10

 11

 7.2 Transformation Method: Exponential and Normal Deviates
 7.3 Rejection Method: Gamma, Poisson, Binomial Deviates
 7A Generation of Random Bits

 7.5 Random Sequences Based on Data Encryption

 7.6 Simple Monte Carlo Integration

 7.7 Quasi- (that is, Sub-) Random Sequences

 7.8 Adaptive and Recursive Monte Carlo Methods

 Sorting

 8.0 Introduction

 8.1 Straight Insertion and Shell’s Method
 8.2 Quicksort

 8.3 Heapsort

 8.4 Indexing and Ranking

 8.5 Selecting the /th Largest

 8.6 Determination of Equivalence Classes

 Root Finding and Nonlinear Sets of Equations

 9.0 Introduction

 9.1 Bracketing and Bisection

 9.2 Secant Method, False Position Method, and Ridders’ Method

 9.3 Van Wijngaarden—Dekker—Brent Method

 9.4 Newton-Raphson Method Using Derivative

 9.5 Roots of Polynomials

 9.6 Newton-Raphson Method for Nonlinear Systems of Equations

 9.7 Globally Convergent Methods for Nonlinear Systems of Equations

 Minimization or Maximization of Functions

 10.0 Introduction

 10.1 Golden Section Search in One Dimension

 10.2 Parabolic Interpolation and Brent’s Method in One Dimension
 10.3 One-Dimensional Search with First Derivatives

 10.4 Downhill Simplex Method in Multidimensions

 10.5 Direction Set (Powell’s) Methods in Multidimensions

 10.6 Conjugate Gradient Methods in Multidimensions

 10.7 Variable Metric Methods in Multidimensions

 10.8 Linear Programming and the Simplex Method

 10.9 Simulated Annealing Methods

 Eigensystems

 11.0 Introduction

 11.1 Jacobi Transformations of a Symmetric Matrix

 11.2 Reduction of a Symmetric Matrix to Tridiagonal Form:
 Givens and Householder Reductions

 11.3 Eigenvalues and Eigenvectors of a Tridiagonal Matrix

 11.4 Hermitian Matrices

 11.5 Reduction of a General Matrix to Hessenberg Form

 287
 290
 296
 300
 304
 309
 316

 329

 329
 330
 332
 336
 338
 341
 345

 347

 347
 350
 354
 359
 362
 369
 379
 383

 394

 394
 397
 402
 405
 408
 412
 420
 425
 430
 444

 456

 456
 463

 469
 475
 481
 482

 Buipnjoul) say ajqepeos

 2
 @
 Fy
 2
 5
 a
 s
 =
 g
 3
 2
 ©
 5
 g
 3
 io
 3
 B
 R
 é
 °
 s
 3
 9
 B
 3
 g
 3
 8
 3
 g
 sz
 Fg

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 BJISGOM SIA ‘SWIOHGD 40 Sy00g sadioay jeoUaWINN Japso O| “payiqiyoud Ajjouys Ss! “4a}NdWOd JaAsas Aue 0} (U0 S|

 -aulyoew jo BulAdoo Aue Jo ‘uonjonpoides seyyin4 “asn yeuosied uMO

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Viii

 Contents

 12

 13

 14

 15

 11.6 The QR Algorithm for Real Hessenberg Matrices
 11.7 Improving Eigenvalues and/or Finding Eigenvectors by
 Inverse Iteration

 Fast Fourier Transform

 12.0 Introduction

 12.1 Fourier Transform of Discretely Sampled Data

 12.2 Fast Fourier Transform (FFT)

 12.3 FFT of Real Functions, Sine and Cosine Transforms
 12.4 FFT in Two or More Dimensions

 12.5 Fourier Transforms of Real Data in Two and Three Dimensions

 12.6 External Storage or Memory-Local FFTs

 Fourier and Spectral Applications

 13.0 Introduction

 13.1 Convolution and Deconvolution Using the FFT

 13.2 Correlation and Autocorrelation Using the FFT

 13.3 Optimal (Wiener) Filtering with the FFT

 13.4 Power Spectrum Estimation Using the FFT

 13.5 Digital Filtering in the Time Domain

 13.6 Linear Prediction and Linear Predictive Coding

 13.7 Power Spectrum Estimation by the Maximum Entropy
 (All Poles) Method

 13.8 Spectral Analysis of Unevenly Sampled Data

 13.9 Computing Fourier Integrals Using the FFT

 13.10 Wavelet Transforms

 13.11 Numerical Use of the Sampling Theorem

 Statistical Description of Data

 14.0 Introduction
 14.1 Moments of a Distribution: Mean, Variance, Skewness,
 and So Forth

 14.2 Do Two Distributions Have the Same Means or Variances?

 14.3 Are Two Distributions Different?

 14.4 Contingency Table Analysis of Two Distributions
 14.5 Linear Correlation

 14.6 Nonparametric or Rank Correlation

 14.7 Do Two-Dimensional Distributions Differ?

 14.8 Savitzky-Golay Smoothing Filters

 Modeling of Data

 15.0 Introduction

 15.1 Least Squares as a Maximum Likelihood Estimator
 15.2 Fitting Data to a Straight Line

 15.3 Straight-Line Data with Errors in Both Coordinates
 15.4 General Linear Least Squares

 15.5 Nonlinear Models

 486
 493

 496

 496
 500
 504
 510
 521
 525
 532

 537

 537
 538
 545
 547
 549
 558
 564

 572
 575
 584
 591
 606

 609
 609

 610
 615
 620
 628
 636
 639
 645
 650

 656

 656
 657
 661
 666
 671
 681

 Buipnjoul) say ajqepeos

 2
 @
 Fy
 2
 5
 a
 s
 =
 g
 3
 2
 ©
 5
 g
 3
 io
 3
 B
 R
 é
 °
 s
 3
 9
 B
 3
 g
 3
 8
 3
 g
 sz
 Fg

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 BJISGOM SIA ‘SWIOHGD 40 Sy00g sadioay jeoUaWINN Japso O| “payiqiyoud Ajjouys Ss! “4a}NdWOd JaAsas Aue 0} (U0 S|

 -aulyoew jo BulAdoo Aue Jo ‘uonjonpoides seyyin4 “asn yeuosied uMO

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 Contents

 ix

 16

 17

 18

 19

 20

 15.6 Confidence Limits on Estimated Model Parameters
 15.7 Robust Estimation

 Integration of Ordinary Differential Equations

 16.0 Introduction

 16.1 Runge-Kutta Method

 16.2 Adaptive Stepsize Control for Runge-Kutta

 16.3 Modified Midpoint Method

 16.4 Richardson Extrapolation and the Bulirsch-Stoer Method
 16.5 Second-Order Conservative Equations

 16.6 Stiff Sets of Equations

 16.7 Multistep, Multivalue, and Predictor-Corrector Methods

 Two Point Boundary Value Problems

 17.0 Introduction

 17.1 The Shooting Method

 17.2 Shooting to a Fitting Point

 17.3 Relaxation Methods

 17.4 A Worked Example: Spheroidal Harmonics

 17.5 Automated Allocation of Mesh Points

 17.6 Handling Internal Boundary Conditions or Singular Points

 Integral Equations and Inverse Theory

 18.0 Introduction

 18.1 Fredholm Equations of the Second Kind

 18.2 Volterra Equations

 18.3 Integral Equations with Singular Kernels

 18.4 Inverse Problems and the Use of A Priori Information
 18.5 Linear Regularization Methods

 18.6 Backus-Gilbert Method

 18.7 Maximum Entropy Image Restoration

 Partial Differential Equations

 19.0 Introduction

 19.1 Flux-Conservative Initial Value Problems

 19.2 Diffusive Initial Value Problems

 19.3 Initial Value Problems in Multidimensions

 19.4 Fourier and Cyclic Reduction Methods for Boundary
 Value Problems

 19.5 Relaxation Methods for Boundary Value Problems

 19.6 Multigrid Methods for Boundary Value Problems

 Less-Numerical Algorithms

 20.0 Introduction
 20.1 Diagnosing Machine Parameters
 20.2 Gray Codes

 689
 699

 707

 707
 710
 714
 722
 724
 732
 734
 TAT

 753

 753
 757
 760
 762
 7712
 783
 784

 788

 788
 791
 794
 797
 804
 808
 815
 818

 827

 827
 834
 847
 853

 857
 863
 871

 889

 889
 889
 894

 Buipnjoul) say ajqepeos

 2
 @
 Fy
 2
 5
 a
 s
 =
 g
 3
 2
 ©
 5
 g
 3
 io
 3
 B
 R
 é
 °
 s
 3
 9
 B
 3
 g
 3
 8
 3
 g
 sz
 Fg

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 BJISGOM SIA ‘SWIOHGD 40 Sy00g sadioay jeoUaWINN Japso O| “payiqiyoud Ajjouys Ss! “4a}NdWOd JaAsas Aue 0} (U0 S|

 -aulyoew jo BulAdoo Aue Jo ‘uonjonpoides seyyin4 “asn yeuosied uMO

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 Contents

 896
 903

 20.3 Cyclic Redundancy and Other Checksums
 20.4 Huffman Coding and Compression of Data

 20.5 Arithmetic Coding

 910
 915

 20.6 Arithmetic at Arbitrary Precision

 926

 References

 Sample page from NUMERICAL RECIPES IN C: THE ART OF SCIENTIFIC COMPUTING (ISBN 0-521-43108-5)

 Copyright (C) 1988-1992 by Cambridge University Press. Programs Copyright (C) 1988-1992 by Numerical Recipes Software.

 is granted for internet users to make one paper copy for their own personal use. Further reproduction, or any copying of machine-
 readable files (including this one) to any server computer, is strictly prohibited. To order Numerical Recipes books or CDROMs, visit website
 http:/Avww.nr.com or call 1-800-872-7423 (North America only), or send email to directcustserv @cambridge.org (outside North America).

 930
 940
 948
 951
 965

 Appendix A: Table of Prototype Declarations
 Appendix B: Utility Routines

 Appendix C: Complex Arithmetic

 Index of Programs and Dependencies

 General Index

 Preface to the Second Edition

 Our aim in writing the original edition of Numerical Recipes was to provide a
 book that combined general discussion, analytical mathematics, algorithmics, and
 actual working programs. The success of the first edition puts us now in a difficult,
 though hardly unenviable, position. We wanted, then and now, to write a book
 that is informal, fearlessly editorial, unesoteric, and above all useful. There is a
 danger that, if we are not careful, we might produce a second edition that is weighty,
 balanced, scholarly, and boring.
 It is a mixed blessing that we know more now than we did six years ago. Then,
 we were making educated guesses, based on existing literature and our own research,
 about which numerical techniques were the most important and robust. Now, we have
 the benefit of direct feedback from a large reader community. Letters to our alter-ego
 enterprise, Numerical Recipes Software, are in the thousands per year. (Please, don’t
 telephone us.) Our post office box has become a magnet for letters pointing out
 that we have omitted some particular technique, well known to be important in a
 particular field of science or engineering. We value such letters, and digest them
 carefully, especially when they point us to specific references in the literature.
 The inevitable result of this input is that this Second Edition of Numerical
 Recipes is substantially larger than its predecessor, in fact about 50% larger both in
 words and number of included programs (the latter now numbering well over 300).
 “Don’t let the book grow in size,” is the advice that we received from several wise
 colleagues. We have tried to follow the intended spirit of that advice, even as we
 violate the letter of it. We have not lengthened, or increased in difficulty, the book’s
 principal discussions of mainstream topics. Many new topics are presented at this
 same accessible level. Some topics, both from the earlier edition and new to this
 one, are now set in smaller type that labels them as being “advanced.” The reader
 who ignores such advanced sections completely will not, we think, find any lack of
 continuity in the shorter volume that results.
 Here are some highlights of the new material in this Second Edition:
 e anew chapter on integral equations and inverse methods
 e a detailed treatment of multigrid methods for solving elliptic partial
 differential equations
 routines for band diagonal linear systems
 improved routines for linear algebra on sparse matrices
 Cholesky and QR decomposition
 orthogonal polynomials and Gaussian quadratures for arbitrary weight
 functions
 methods for calculating numerical derivatives
 e Padé approximants, and rational Chebyshev approximation
 e Bessel functions, and modified Bessel functions, of fractional order; and
 several other new special functions

 e improved random number routines

 © quasi-random sequences

 e routines for adaptive and recursive Monte Carlo integration in high-
 dimensional spaces

 e globally convergent methods for sets of nonlinear equations

 xi

 SILO

 *(eoewy YON epis}no) B10'eBpuquies @AJes}sno}O~1IP 0} [ea PUSS JO ‘(AJUO BOVBWIY YON) EZPZ-ZZ8-008- | [129 10 WOoU'MMMy/:dAY,
 O'USGOM IISIA ‘SWWOHGD 40 Sy00g sedisay jeOUEWINN Japso OF “payiqiyoid Ajolys si ‘ayndwios Ja/as Aue 0} (UO Siu} Bulpnjoul) sally ajqepees

 2
 @
 3
 2
 3
 a
 s
 =
 8
 3
 2
 ©
 &
 8
 3
 3
 3
 a
 ES
 3
 °
 s
 3
 3
 3
 3
 g
 3
 fe}
 3
 2
 s
 Fa
 2
 °
 =
 5
 3
 8
 Fa
 °
 5
 2
 ©
 &
 ®
 n
 s
 Ea
 2
 3
 3
 °
 Qa
 2
 S
 &
 P
 fa
 2
 e}
 2
 8
 fo}
 3
 s.
 5
 a
 g
 3
 3
 8
 2
 5
 ?

 uAdog

 n
 Ey
 3
 3
 g
 3
 Ey
 a
 3
 fei
 3
 Zz
 i
 =
 m
 2
 fe)
 >
 =
 D
 m
 Q
 vu
 m
 n
 2
 2
 4
 x
 m
 >
 D
 4
 fe)
 9
 n
 Q
 m
 Zz
 a
 al
 ie)
 Q
 fe}
 =
 vu
 Cc
 a
 2
 fo)
 D
 jes)
 Zz
 2
 a
 X
 h
 g
 3
 ha
 Ro)

 2
 o
 2
 e
 o
 S
 8

 z
 1?)
 2
 3
 ic
 z

 a
 o
 Cc
 Es
 Fe
 g
 gZ

 =
 3
 3
 S
 9
 2
 3

 Q
 Ba
 3
 a
 9
 S

 3

 Ss

 2
 E

 2
 o
 2
 2
 o
 3S
 nn
 z

 <
 Zz
 é
 3
 g
 3
 Ea
 DD
 2
 &

 3
 3
 3
 n
 ot
 =
 FA
 a
 8

 xii Preface to the Second Edition

 simulated annealing minimization for continuous control spaces

 fast Fourier transform (FFT) for real data in two and three dimensions
 fast Fourier transform (FFT) using external storage

 improved fast cosine transform routines

 wavelet transforms

 Fourier integrals with upper and lower limits

 spectral analysis on unevenly sampled data

 Savitzky-Golay smoothing filters

 fitting straight line data with errors in both coordinates

 a two-dimensional Kolmogorov-Smirnoff test

 the statistical bootstrap method

 embedded Runge-Kutta-Fehlberg methods for differential equations
 high-order methods for stiff differential equations

 a new chapter on “less-numerical” algorithms, including Huffman and
 arithmetic coding, arbitrary precision arithmetic, and several other topics.
 Consult the Preface to the First Edition, following, or the Table of Contents, for a
 list of the more “basic” subjects treated.

 Acknowledgments

 It is not possible for us to list by name here all the readers who have made
 useful suggestions; we are grateful for these. In the text, we attempt to give specific
 attribution for ideas that appear to be original, and not known in the literature. We
 apologize in advance for any omissions.

 Some readers and colleagues have been particularly generous in providing
 us with ideas, comments, suggestions, and programs for this Second Edition.
 We especially want to thank George Rybicki, Philip Pinto, Peter Lepage, Robert
 Lupton, Douglas Eardley, Ramesh Narayan, David Spergel, Alan Oppenheim, Sallie
 Baliunas, Scott Tremaine, Glennys Farrar, Steven Block, John Peacock, Thomas
 Loredo, Matthew Choptuik, Gregory Cook, L. Samuel Finn, P. Deuflhard, Harold
 Lewis, Peter Weinberger, David Syer, Richard Ferch, Steven Ebstein, Bradley
 Keister, and William Gould. We have been helped by Nancy Lee Snyder’s mastery
 of a complicated TEX manuscript. We express appreciation to our editors Lauren
 Cowles and Alan Harvey at Cambridge University Press, and to our production editor
 Russell Hahn. We remain, of course, grateful to the individuals acknowledged in
 the Preface to the First Edition.

 Special acknowledgment is due to programming consultant Seth Finkelstein,
 who wrote, rewrote, or influenced many of the routines in this book, as well as in
 its FORTRAN-language twin and the companion Example books. Our project has
 benefited enormously from Seth’s talent for detecting, and following the trail of, even
 very slight anomalies (often compiler bugs, but occasionally our errors), and from
 his good programming sense. To the extent that this edition of Numerical Recipes
 in C has a more graceful and “C-like” programming style than its predecessor, most
 of the credit goes to Seth. (Of course, we accept the blame for the FORTRANish
 lapses that still remain.)

 We prepared this book for publication on DEC and Sun workstations run-
 ning the UNIX operating system, and on a 486/33 PC compatible running
 MS-DOS 5.0/Windows 3.0. (See §1.0 for a list of additional computers used in

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.
 -eulyoew jo BulAdoo Aue Jo ‘uojonpoides sayyin4 “asn seuosied UMO 4194} 10} Adoo seded auo eyeW 0} suas JeUJE}U! 10} PayUeJGH SI UOISSILAg

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Preface to the Second Edition xiii

 program tests.) We enthusiastically recommend the principal software used: GNU
 Emacs, TgX, Perl, Adobe Illustrator, and PostScript. Also used were a variety of C
 compilers — too numerous (and sometimes too buggy) for individual acknowledg-
 ment. It is a sobering fact that our standard test suite (exercising all the routines
 in this book) has uncovered compiler bugs in many of the compilers tried. When
 possible, we work with developers to see that such bugs get fixed; we encourage
 interested compiler developers to contact us about such arrangements.

 WHP and SAT acknowledge the continued support of the U.S. National Science
 Foundation for their research on computational methods. D.A.R.P.A. support is
 acknowledged for §13.10 on wavelets.

 doa,

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 June, 1992 William H. Press
 Saul A. Teukolsky
 William T. Vetterling
 Brian P. Flannery

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 *(eouaWy YLON epis}no) Bio’ aBpuquieo® les}sno}0~a11p 0} |fewWa PUBS JO ‘(KjUO BOUV@WIY YUON) EZPZ-ZZ8-008- | [29 10 WOO™U'MMy/: cy
 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII


 Preface to the First Edition

 We call this book Numerical Recipes for several reasons. In one sense, this book
 is indeed a “cookbook” on numerical computation. However there is an important
 distinction between a cookbook and a restaurant menu. The latter presents choices
 among complete dishes in each of which the individual flavors are blended and
 disguised. The former — and this book — reveals the individual ingredients and
 explains how they are prepared and combined.

 Another purpose of the title is to connote an eclectic mixture of presentational
 techniques. This book is unique, we think, in offering, for each topic considered,
 a certain amount of general discussion, a certain amount of analytical mathematics,
 a certain amount of discussion of algorithmics, and (most important) actual imple-
 mentations of these ideas in the form of working computer routines. Our task has
 been to find the right balance among these ingredients for each topic. You will
 find that for some topics we have tilted quite far to the analytic side; this where we
 have felt there to be gaps in the “standard” mathematical training. For other topics,
 where the mathematical prerequisites are universally held, we have tilted towards
 more in-depth discussion of the nature of the computational algorithms, or towards
 practical questions of implementation.

 We admit, therefore, to some unevenness in the “level” of this book. About half
 of it is suitable for an advanced undergraduate course on numerical computation for
 science or engineering majors. The other half ranges from the level of a graduate
 course to that of a professional reference. Most cookbooks have, after all, recipes at
 varying levels of complexity. An attractive feature of this approach, we think, is that
 the reader can use the book at increasing levels of sophistication as his/her experience
 grows. Even inexperienced readers should be able to use our most advanced routines
 as black boxes. Having done so, we hope that these readers will subsequently go
 back and learn what secrets are inside.

 If there is a single dominant theme in this book, it is that practical methods
 of numerical computation can be simultaneously efficient, clever, and — important
 — clear. The alternative viewpoint, that efficient computational methods must
 necessarily be so arcane and complex as to be useful only in “black box” form,
 we firmly reject.

 Our purpose in this book is thus to open up a large number of computational
 black boxes to your scrutiny. We want to teach you to take apart these black boxes
 and to put them back together again, modifying them to suit your specific needs.
 We assume that you are mathematically literate, i.e., that you have the normal
 mathematical preparation associated with an undergraduate degree in a physical
 science, or engineering, or economics, or a quantitative social science. We assume
 that you know how to program a computer. We do not assume that you have any
 prior formal knowledge of numerical analysis or numerical methods.

 The scope of Numerical Recipes is supposed to be “everything up to, but
 not including, partial differential equations.” We honor this in the breach: First,
 we do have one introductory chapter on methods for partial differential equations
 (Chapter 19). Second, we obviously cannot include everything else. All the so-called
 “standard” topics of a numerical analysis course have been included in this book:

 xiv

 SILO

 *(eoewy YON epis}no) B10'eBpuquies @AJes}sno}O~1IP 0} [ea PUSS JO ‘(AJUO BOVBWIY YON) EZPZ-ZZ8-008- | [129 10 WOoU'MMMy/:dAY,
 O'USGOM IISIA ‘SWWOHGD 40 Sy00g sedisay jeOUEWINN Japso OF “payiqiyoid Ajolys si ‘ayndwios Ja/as Aue 0} (UO Siu} Bulpnjoul) sally ajqepees

 2
 @
 3
 2
 3
 a
 s
 =
 8
 3
 2
 ©
 &
 8
 3
 3
 3
 a
 ES
 3
 °
 s
 3
 3
 3
 3
 g
 3
 fe}
 3
 2
 s
 Fa
 2
 °
 =
 5
 3
 8
 Fa
 °
 5
 2
 ©
 &
 ®
 n
 s
 Ea
 2
 3
 3
 °
 Qa
 2
 S
 &
 P
 fa
 2
 e}
 2
 8
 fo}
 3
 s.
 5
 a
 g
 3
 3
 8
 2
 5
 ?

 uAdog

 n
 Ey
 3
 3
 g
 3
 Ey
 a
 3
 fei
 3
 Zz
 i
 =
 m
 2
 fe)
 >
 =
 D
 m
 Q
 vu
 m
 n
 2
 2
 4
 x
 m
 >
 D
 4
 fe)
 9
 n
 Q
 m
 Zz
 a
 al
 ie)
 Q
 fe}
 =
 vu
 Cc
 a
 2
 fo)
 D
 jes)
 Zz
 2
 a
 X
 h
 g
 3
 ha
 Ro)

 2
 o
 2
 e
 o
 S
 8

 z
 1?)
 2
 3
 ic
 z

 a
 o
 Cc
 Es
 Fe
 g
 gZ

 =
 3
 3
 S
 9
 2
 3

 Q
 Ba
 3
 a
 9
 S

 3

 Ss

 2
 E

 2
 o
 2
 2
 o
 3S
 nn
 z

 <
 Zz
 é
 3
 g
 3
 Ea
 DD
 2
 &

 3
 3
 3
 n
 ot
 =
 FA
 a
 8

 Preface to the First Edition xv

 linear equations (Chapter 2), interpolation and extrapolation (Chaper 3), integration
 (Chaper 4), nonlinear root-finding (Chapter 9), eigensystems (Chapter 11), and
 ordinary differential equations (Chapter 16). Most of these topics have been taken
 beyond their standard treatments into some advanced material which we have felt
 to be particularly important or useful.

 Some other subjects that we cover in detail are not usually found in the standard
 numerical analysis texts. These include the evaluation of functions and of particular
 special functions of higher mathematics (Chapters 5 and 6); random numbers and
 Monte Carlo methods (Chapter 7); sorting (Chapter 8); optimization, including
 multidimensional methods (Chapter 10); Fourier transform methods, including FFT
 methods and other spectral methods (Chapters 12 and 13); two chapters on the
 statistical description and modeling of data (Chapters 14 and 15); and two-point
 boundary value problems, both shooting and relaxation methods (Chapter 17).

 The programs in this book are included in ANSI-standard C. Versions of the
 book in FORTRAN, Pascal, and BASIC are available separately. We have more
 to say about the C language, and the computational environment assumed by our
 routines, in §1.1 (Introduction).

 Acknowledgments

 Many colleagues have been generous in giving us the benefit of their numerical
 and computational experience, in providing us with programs, in commenting on
 the manuscript, or in general encouragement. We particularly wish to thank George
 Rybicki, Douglas Eardley, Philip Marcus, Stuart Shapiro, Paul Horowitz, Bruce
 Musicus, Irwin Shapiro, Stephen Wolfram, Henry Abarbanel, Larry Smarr, Richard
 Muller, John Bahcall, and A.G.W. Cameron.

 We also wish to acknowledge two individuals whom we have never met: Forman
 Acton, whose 1970 textbook Numerical Methods that Work (New York: Harper and
 Row) has surely left its stylistic mark on us; and Donald Knuth, both for his series
 of books on The Art of Computer Programming (Reading, MA: Addison-Wesley),
 and for TgX, the computer typesetting language which immensely aided production
 of this book.

 Research by the authors on computational methods was supported in part by
 the U.S. National Science Foundation.

 October, 1985 William H. Press
 Brian P. Flannery
 Saul A. Teukolsky
 William T. Vetterling

 Jeo JO Woo suMMy/:dy

 ‘(Ajuo eouewy YUON) EZrZ-228-008-

 *(eoveWY YUON episyno) B10‘eBpuquiex® Mes}snojoauIp 0} |reWa pues

 “sayndwiod Jansas Aue 0} (aU0 S

 ($-801€b-12S-0 NASI) ONILNdWOD OISILNSIOS JO LYV SHL:0 NI SAdIO3Y TWOIMSINNN Woy eBed aides

 “aremyos sedisay jeouewnn Aq Z661-B861. (9) 1UBUAdOD susesBolg "ssaid AysienluN eBpuquued Kq Z661-BB6l

 License Information

 Read this section if you want to use the programs in this book on a computer.
 You’ll need to read the following Disclaimer of Warranty, get the programs onto your
 computer, and acquire a Numerical Recipes software license. (Without this license,
 which can be the free “immediate license” under terms described below, the book is
 intended as a text and reference book, for reading purposes only.)

 Disclaimer of Warranty

 We make no warranties, express or implied, that the programs contained
 in this volume are free of error, or are consistent with any particular standard
 of merchantability, or that they will meet your requirements for any particular
 application. They should not be relied on for solving a problem whose incorrect
 solution could result in injury to a person or loss of property. If you do use the
 programs in such a manner, it is at your own risk. The authors and publisher
 disclaim all liability for direct or consequential damages resulting from your
 use of the programs.

 How to Get the Code onto Your Computer

 Pick one of the following methods:

 e You can type the programs from this book directly into your computer. In this
 case, the only kind of license available to you is the free “immediate license”
 (see below). You are not authorized to transfer or distribute a machine-readable
 copy to any other person, nor to have any other person type the programs into a
 computer on your behalf. We do not want to hear bug reports from you if you
 choose this option, because experience has shown that virtually all reported bugs
 in such cases are typing errors!

 e You can download the Numerical Recipes programs electronically from the
 Numerical Recipes On-Line Software Store, located at http: //www.nr.com, our
 Web site. All the files (Recipes and demonstration programs) are packaged as
 a single compressed file. You'll need to purchase a license to download and
 unpack them. Any number of single-screen licenses can be purchased instantly
 (with discount for multiple screens) from the On-Line Store, with fees that depend
 on your operating system (Windows or Macintosh versus Linux or UNIX) and
 whether you are affiliated with an educational institution. Purchasing a single-
 screen license is also the way to start if you want to acquire a more general (site
 or corporate) license; your single-screen cost will be subtracted from the cost of
 any later license upgrade.

 e You can purchase media containing the programs from Cambridge University Press.
 A CD-ROM version in ISO-9660 format for Windows and Macintosh systems
 contains the complete C software, and also the C++ version. More extensive CD-
 ROMs in ISO-9660 format for Windows, Macintosh, and UNIX/Linux systems are
 also available; these include the C, C++, and Fortran versions on a single CD-ROM
 (as well as versions in Pascal and BASIC from the first edition). These CD-ROMs
 are available with a single-screen license for Windows or Macintosh (order ISBN
 0 521 750350), or (at a slightly higher price) with a single-screen license for
 UNIX/Linux workstations (order ISBN 0 521 750369). Orders for media from
 Cambridge University Press can be placed at 800 872-7423 (North America only)
 or by email to orders@cup.org (North America) or directcustserv@cambridge.org
 (rest of world). Or, visit the Web site http: //www.cambridge. org.

 xvi

 SILO

 *(eoewy YON epis}no) B10'eBpuquies @AJes}sno}O~1IP 0} [ea PUSS JO ‘(AJUO BOVBWIY YON) EZPZ-ZZ8-008- | [129 10 WOoU'MMMy/:dAY,
 O'USGOM IISIA ‘SWWOHGD 40 Sy00g sedisay jeOUEWINN Japso OF “payiqiyoid Ajolys si ‘ayndwios Ja/as Aue 0} (UO Siu} Bulpnjoul) sally ajqepees

 2
 @
 3
 2
 3
 a
 s
 =
 8
 3
 2
 ©
 &
 8
 3
 3
 3
 a
 ES
 3
 °
 s
 3
 3
 3
 3
 g
 3
 fe}
 3
 2
 s
 Fa
 2
 °
 =
 5
 3
 8
 Fa
 °
 5
 2
 ©
 &
 ®
 n
 s
 Ea
 2
 3
 3
 °
 Qa
 2
 S
 &
 P
 fa
 2
 e}
 2
 8
 fo}
 3
 s.
 5
 a
 g
 3
 3
 8
 2
 5
 ?

 uAdog

 n
 Ey
 3
 3
 g
 3
 Ey
 a
 3
 fei
 3
 Zz
 i
 =
 m
 2
 fe)
 >
 =
 D
 m
 Q
 vu
 m
 n
 2
 2
 4
 x
 m
 >
 D
 4
 fe)
 9
 n
 Q
 m
 Zz
 a
 al
 ie)
 Q
 fe}
 =
 vu
 Cc
 a
 2
 fo)
 D
 jes)
 Zz
 2
 a
 X
 h
 g
 3
 ha
 Ro)

 2
 o
 2
 e
 o
 S
 8

 z
 1?)
 2
 3
 ic
 z

 a
 o
 Cc
 Es
 Fe
 g
 gZ

 =
 3
 3
 S
 9
 2
 3

 Q
 Ba
 3
 a
 9
 S

 3

 Ss

 2
 E

 2
 o
 2
 2
 o
 3S
 nn
 z

 <
 Zz
 é
 3
 g
 3
 Ea
 DD
 2
 &

 3
 3
 3
 n
 ot
 =
 FA
 a
 8

 License Information xvii

 Types of License Offered

 Here are the types of licenses that we offer. Note that some types are
 automatically acquired with the purchase of media from Cambridge University
 Press, or of an unlocking password from the Numerical Recipes On-Line Software
 Store, while other types of licenses require that you communicate specifically with
 Numerical Recipes Software (email: orders@nr.com or fax: 781 863-1739). Our
 Web site http: //www.nr.com has additional information.

 e [Immediate License”] If you are the individual owner of a copy of this book and
 you type one or more of its routines into your computer, we authorize you to use
 them on that computer for your own personal and noncommercial purposes. You
 are not authorized to transfer or distribute machine-readable copies to any other
 person, or to use the routines on more than one machine, or to distribute executable
 programs containing our routines. This is the only free license.

 e [‘Single-Screen License”] This is the most common type of low-cost license, with
 terms governed by our Single Screen (Shrinkwrap) License document (complete
 terms available through our Web site). Basically, this license lets you use Numerical
 Recipes routines on any one screen (PC, workstation, X-terminal, etc.). You may
 also, under this license, transfer pre-compiled, executable programs incorporating
 our routines to other, unlicensed, screens or computers, providing that (i) your
 application is noncommercial (i.e., does not involve the selling of your program
 for a fee), (ii) the programs were first developed, compiled, and successfully run
 on a licensed screen, and (iii) our routines are bound into the programs in such a
 manner that they cannot be accessed as individual routines and cannot practicably
 be unbound and used in other programs. That is, under this license, your program
 user must not be able to use our programs as part of a program library or “mix-and-
 match” workbench. Conditions for other types of commercial or noncommercial
 distribution may be found on our Web site (http: //www.nr.com).

 e [“Multi-Screen, Server, Site, and Corporate Licenses”] The terms of the Single
 Screen License can be extended to designated groups of machines, defined by
 number of screens, number of machines, locations, or ownership. Significant
 discounts from the corresponding single-screen prices are available when the
 estimated number of screens exceeds 40. Contact Numerical Recipes Software
 (email: orders@nr.com or fax: 781 863-1739) for details.

 e [Course Right-to-Copy License”] Instructors at accredited educational institutions
 who have adopted this book for a course, and who have already purchased a Single
 Screen License (either acquired with the purchase of media, or from the Numerical
 Recipes On-Line Software Store), may license the programs for use in that course
 as follows: Mail your name, title, and address; the course name, number, dates,
 and estimated enrollment; and advance payment of $5 per (estimated) student
 to Numerical Recipes Software, at this address: P.O. Box 243, Cambridge, MA
 02238 (USA). You will receive by return mail a license authorizing you to make
 copies of the programs for use by your students, and/or to transfer the programs to
 a machine accessible to your students (but only for the duration of the course).

 About Copyrights on Computer Programs

 Like artistic or literary compositions, computer programs are protected by
 copyright. Generally it is an infringement for you to copy into your computer a
 program from a copyrighted source. (It is also not a friendly thing to do, since it
 deprives the program’s author of compensation for his or her creative effort.) Under

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 doa,

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 xviii License Information

 copyright law, all “derivative works” (modified versions, or translations into another
 computer language) also come under the same copyright as the original work.

 Copyright does not protect ideas, but only the expression of those ideas in
 a particular form. In the case of a computer program, the ideas consist of the
 program’s methodology and algorithm, including the necessary sequence of steps
 adopted by the programmer. The expression of those ideas is the program source
 code (particularly any arbitrary or stylistic choices embodied in it), its derived object
 code, and any other derivative works.

 If you analyze the ideas contained in a program, and then express those
 ideas in your own completely different implementation, then that new program
 implementation belongs to you. That is what we have done for those programs in
 this book that are not entirely of our own devising. When programs in this book are
 said to be “based” on programs published in copyright sources, we mean that the
 ideas are the same. The expression of these ideas as source code is our own. We
 believe that no material in this book infringes on an existing copyright.

 Trademarks

 Several registered trademarks appear within the text of this book: Sun is a
 trademark of Sun Microsystems, Inc. SPARC and SPARCstation are trademarks
 of SPARC International, Inc. Microsoft, Windows 95, Windows NT, PowerStation,
 and MS are trademarks of Microsoft Corporation. DEC, VMS, Alpha AXP, and
 ULTRIX are trademarks of Digital Equipment Corporation. IBM is a trademark of
 International Business Machines Corporation. Apple and Macintosh are trademarks
 of Apple Computer, Inc. UNIX is a trademark licensed exclusively through X/Open
 Co. Ltd. IMSL is a trademark of Visual Numerics, Inc. NAG refers to proprietary
 computer software of Numerical Algorithms Group (USA) Inc. PostScript and
 Adobe Illustrator are trademarks of Adobe Systems Incorporated. Last, and no doubt
 least, Numerical Recipes (when identifying products) is a trademark of Numerical
 Recipes Software.

 Attributions

 The fact that ideas are legally “free as air” in no way supersedes the ethical
 requirement that ideas be credited to their known originators. When programs in
 this book are based on known sources, whether copyrighted or in the public domain,
 published or “handed-down,” we have attempted to give proper attribution. Unfor-
 tunately, the lineage of many programs in common circulation is often unclear. We
 would be grateful to readers for new or corrected information regarding attributions,
 which we will attempt to incorporate in subsequent printings.

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.0
 1.1
 1.1
 1.1

 2.1

 23
 23
 24
 24
 24
 24
 25
 2.6
 2.6
 2.6
 27
 27
 27
 27
 27
 27
 27
 27
 27
 27
 27
 28
 28
 2.9
 2.9
 2.10
 2.10
 2.10
 2.10
 2.10

 3.1
 3.2
 33
 33
 34

 Computer Programs

 by Chapter and Section

 flmoon
 julday
 badluk
 caldat

 gaussj

 ludcmp
 lubksb
 tridag
 banmul
 bandec
 banbks
 mprove
 svbksb
 svdcmp
 pythag
 cyclic
 sprsin
 sprsax
 sprstx
 sprstp
 sprspm
 sprstm
 linbcg
 snrm
 atimes
 asolve
 vander
 toep1z
 choldc
 cholsl
 qrdcmp
 qrsolv
 rsolv
 qrupdt
 rotate

 polint
 ratint
 spline
 splint
 locate

 calculate phases of the moon by date

 Julian Day number from calendar date
 Friday the 13th when the moon is full
 calendar date from Julian day number

 Gauss-Jordan matrix inversion and linear equation

 solution

 linear equation solution, LU decomposition
 linear equation solution, backsubstitution
 solution of tridiagonal systems

 multiply vector by band diagonal matrix
 band diagonal systems, decomposition
 band diagonal systems, backsubstitution
 linear equation solution, iterative improvement
 singular value backsubstitution

 singular value decomposition of a matrix
 calculate (a? + b?)!/? without overflow
 solution of cyclic tridiagonal systems
 convert matrix to sparse format

 product of sparse matrix and vector
 product of transpose sparse matrix and vector
 transpose of sparse matrix

 pattern multiply two sparse matrices
 threshold multiply two sparse matrices
 biconjugate gradient solution of sparse systems
 used by linbcg for vector norm

 used by linbcg for sparse multiplication
 used by linbcg for preconditioner

 solve Vandermonde systems

 solve Toeplitz systems

 Cholesky decomposition

 Cholesky backsubstitution

 QR decomposition

 QR backsubstitution

 right triangular backsubstitution

 update a QR decomposition

 Jacobi rotation used by qrupdt

 polynomial interpolation

 rational function interpolation
 construct a cubic spline

 cubic spline interpolation

 search an ordered table by bisection

 xix

 *(eoLaWy YON episyno) Bio‘eBpuquies@AJesysno}Oa1Ip 0} [EWE PUas JO ‘(AJUO BOVEWY YVON) E%PZ-ZZ8-008-| [fe 40 WOO UMMM): daY

 O'USGOM IISIA ‘SWWOHGD 40 Sy00g sedisay jeOUEWINN Japso OF “payiqiyoid Ajolys si ‘ayndwios Ja/as Aue 0} (UO Siu} Bulpnjoul) sally ajqepees
 -auiyoeul jo BuiAdoo Aue Jo ‘uononpoidas ayjin4 ‘asn jeuosiad UMO JIAaU} 10} Adoo saded auo ayeW 0} Suasn JEUJa\U! 10} Pa}UeJGH SI UOISSIULOg

 ($-80L€b-12S-0 NS!) ONILNdWOOD OISILNAIOS 4O LYV SHL 'O NI SAdIOSY TWOINSWNN Woy e6ed ajdwes

 “AIEMYOS Sadioay ;eOUOWNN Aq Z661-8B6l (D) IYBUAdOD swesBOlY “‘ssalg AysIaAIUN EBpLqueD Aq 2661-8861 (D) jyBUAdOD

 XX Computer Programs by Chapter and Section
 34 hunt search a table when calls are correlated
 3.5 polcoe polynomial coefficients from table of values
 3.5 polcof polynomial coefficients from table of values
 3.6 polin2 two-dimensional polynomial interpolation
 3.6 beucof construct two-dimensional bicubic
 3.6 beuint two-dimensional bicubic interpolation
 3.6 splie2 construct two-dimensional spline
 3.6 splin2 two-dimensional spline interpolation
 42 trapzd trapezoidal rule
 42 qtrap integrate using trapezoidal rule
 42 qsimp integrate using Simpson’s rule
 43 qromb integrate using Romberg adaptive method
 44 midpnt extended midpoint rule
 44 qromo integrate using open Romberg adaptive method
 44 midinf integrate a function on a semi-infinite interval
 44 midsql integrate a function with lower square-root singularity
 44 midsqu integrate a function with upper square-root singularity
 44 midexp integrate a function that decreases exponentially
 45 qgaus integrate a function by Gaussian quadratures
 45 gauleg Gauss-Legendre weights and abscissas
 45 gaulag Gauss-Laguerre weights and abscissas
 45 gauher Gauss-Hermite weights and abscissas
 45 gaujac Gauss-Jacobi weights and abscissas
 45 gaucof quadrature weights from orthogonal polynomials
 45 orthog construct nonclassical orthogonal polynomials
 46 quad3d integrate a function over a three-dimensional space
 5.1 eulsum sum a series by Euler—van Wijngaarden algorithm
 5.3 ddpoly evaluate a polynomial and its derivatives
 5.3 poldiv divide one polynomial by another
 53 ratval evaluate a rational function
 57 dfridr numerical derivative by Ridders’ method
 5.8 chebft fit a Chebyshev polynomial to a function
 5.8 chebev Chebyshev polynomial evaluation
 5.9 chder derivative of a function already Chebyshev fitted
 5.9 chint integrate a function already Chebyshev fitted
 5.10 chebpc polynomial coefficients from a Chebyshev fit
 5.10 peshft polynomial coefficients of a shifted polynomial
 5.11 pccheb inverse of chebpc; use to economize power series
 5.12 pade Padé approximant from power series coefficients
 5.13 ratlsq rational fit by least-squares method
 6. gammln logarithm of gamma function
 6. factrl factorial function
 6. bico binomial coefficients function
 6. factln logarithm of factorial function

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.
 -eulyoew jo BulAdoo Aue Jo ‘uojonpoides sayyin4 “asn seuosied UMO 4194} 10} Adoo seded auo eyeW 0} suas JeUJE}U! 10} PayUeJGH SI UOISSILAg

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Computer Programs by Chapter and Section xxi

 ANNNNNNNNNNDNANNNNNN NNN NNN NNN NNN NW DW
 CbeSm®YUUUNUUADDAADADAUUUUNUUARWWHNHHNHHNHNHE

 DAAHRAAHRAAAA

 ~_

 VHnveseeseeeees

 beta
 gammp
 gammq
 gser
 gcf
 erff
 erffc
 erfcc
 expint
 ei
 betai
 betacf
 bessjO
 bessy0
 bessji
 bessy1
 bessy
 bessj
 bessi0
 bessk0O
 bessil
 bessk1i
 bessk
 bessi
 bessjy
 beschb
 bessik
 airy
 sphbes
 plgndr
 frenel
 cisi
 dawson
 rf

 rd

 rj

 re
 ellf
 elle
 ellpi
 sncndn
 hypgeo
 hypser
 hypdrv

 ran0O
 rant

 beta function

 incomplete gamma function

 complement of incomplete gamma function
 series used by gammp and gammq

 continued fraction used by gammp and gammq
 error function

 complementary error function
 complementary error function, concise routine
 exponential integral EF,

 exponential integral Ei

 incomplete beta function

 continued fraction used by betai

 Bessel function Jo

 Bessel function Yo

 Bessel function J;

 Bessel function Y;

 Bessel function Y of general integer order
 Bessel function J of general integer order
 modified Bessel function Jo

 modified Bessel function Ko

 modified Bessel function J,

 modified Bessel function Ky;

 modified Bessel function Ix of integer order
 modified Bessel function I of integer order
 Bessel functions of fractional order
 Chebyshev expansion used by bessjy
 modified Bessel functions of fractional order
 Airy functions

 spherical Bessel functions j,, and yp,
 Legendre polynomials, associated (spherical harmonics)
 Fresnel integrals S(a) and C(x)

 cosine and sine integrals Ci and Si
 Dawson’s integral

 Carlson’s elliptic integral of the first kind
 Carlson’s elliptic integral of the second kind
 Carlson’s elliptic integral of the third kind
 Carlson’s degenerate elliptic integral
 Legendre elliptic integral of the first kind
 Legendre elliptic integral of the second kind
 Legendre elliptic integral of the third kind
 Jacobian elliptic functions

 complex hypergeometric function

 complex hypergeometric function, series evaluation
 complex hypergeometric function, derivative of

 random deviate by Park and Miller minimal standard
 random deviate, minimal standard plus shuffle

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.
 -eulyoew jo BulAdoo Aue Jo ‘uojonpoides sayyin4 “asn seuosied UMO 4194} 10} Adoo seded auo eyeW 0} suas JeUJE}U! 10} PayUeJGH SI UOISSILAg

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 xxii Computer Programs by Chapter and Section
 7A ran2 random deviate by L’Ecuyer long period plus shuffle
 7A ran3 random deviate by Knuth subtractive method
 72 expdev exponential random deviates
 72 gasdev normally distributed random deviates
 73 gamdev gamma-law distribution random deviates
 73 poidev Poisson distributed random deviates
 73 bnidev binomial distributed random deviates
 TA irbit1 random bit sequence
 TA irbit2 random bit sequence
 75 psdes “pseudo-DES” hashing of 64 bits
 75 ran4 random deviates from DES-like hashing
 77 sobseq Sobol’s quasi-random sequence
 78 vegas adaptive multidimensional Monte Carlo integration
 78 rebin sample rebinning used by vegas
 78 miser recursive multidimensional Monte Carlo integration
 78 ranpt get random point, used by miser
 8.1 piksrt sort an array by straight insertion
 8.1 piksr2 sort two arrays by straight insertion
 8.1 shell sort an array by Shell’s method
 8.2 sort sort an array by quicksort method
 8.2 sort2 sort two arrays by quicksort method
 8.3 hpsort sort an array by heapsort method
 84 indexx construct an index for an array
 84 sort3 sort, use an index to sort 3 or more arrays
 84 rank construct a rank table for an array
 8.5 select find the Nth largest in an array
 8.5 selip find the Nth largest, without altering an array
 8.5 hpsel find M largest values, without altering an array
 8.6 eclass determine equivalence classes from list
 8.6 eclazz determine equivalence classes from procedure
 9.0 scrsho graph a function to search for roots
 91 zbrac outward search for brackets on roots
 91 zbrak inward search for brackets on roots
 91 rtbis find root of a function by bisection
 92 rtflsp find root of a function by false-position
 92 rtsec find root of a function by secant method
 92 zriddr find root of a function by Ridders’ method
 93 zbrent find root of a function by Brent’s method
 94 rtnewt find root of a function by Newton-Raphson
 94 rtsafe find root of a function by Newton-Raphson and bisection
 95 laguer find a root of a polynomial by Laguerre’s method
 95 zroots roots of a polynomial by Laguerre’s method with
 deflation
 95 zrhqr roots of a polynomial by eigenvalue methods
 95 qroot complex or double root of a polynomial, Bairstow

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.
 -eulyoew jo BulAdoo Aue Jo ‘uojonpoides sayyin4 “asn seuosied UMO 4194} 10} Adoo seded auo eyeW 0} suas JeUJE}U! 10} PayUeJGH SI UOISSILAg

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Computer Programs by Chapter and Section xxiii

 9.6
 97
 97
 97
 97
 97

 0.1
 0.1
 0.2
 0.3
 04
 04
 0.5
 0.5
 0.5
 0.6
 0.6
 0.6
 0.7
 0.8
 0.8
 0.8
 0.8
 09
 09
 09
 09
 09
 09
 09
 09

 1.1
 1.1
 12
 13
 15
 15
 1.6

 2.2
 23
 23
 23
 23
 23

 mnewt
 insrch
 newt
 fdjac
 fmin
 broydn

 mnbrak
 golden
 brent
 dbrent
 amoeba
 amotry
 powell
 linmin
 fidim
 frprmn
 dlinmin
 dfidim
 dfpmin
 simplx
 simp1
 simp2
 simp3
 anneal
 revcst
 reverse
 trncst
 trnspt
 metrop
 amebsa
 amotsa

 jacobi
 eigsrt
 tred2
 tqli
 balanc
 elmhes
 hqr

 fourl
 twofft
 realft
 sinft
 cosft1
 cosft2

 Newton’s method for systems of equations

 search along a line, used by newt

 globally convergent multi-dimensional Newton’s method
 finite-difference Jacobian, used by newt

 norm of a vector function, used by newt

 secant method for systems of equations

 bracket the minimum of a function

 find minimum of a function by golden section search
 find minimum of a function by Brent’s method

 find minimum of a function using derivative information
 minimize in N-dimensions by downhill simplex method
 evaluate a trial point, used by amoeba

 minimize in -dimensions by Powell’s method
 minimum of a function along a ray in V-dimensions
 function used by linmin

 minimize in V-dimensions by conjugate gradient
 minimum of a function along a ray using derivatives
 function used by dlinmin

 minimize in V-dimensions by variable metric method
 linear programming maximization of a linear function
 linear programming, used by simp1x

 linear programming, used by simp1x

 linear programming, used by simp1x

 traveling salesman problem by simulated annealing
 cost of a reversal, used by anneal

 do a reversal, used by anneal

 cost of a transposition, used by anneal

 do a transposition, used by anneal

 Metropolis algorithm, used by anneal

 simulated annealing in continuous spaces

 evaluate a trial point, used by amebsa

 eigenvalues and eigenvectors of a symmetric matrix
 eigenvectors, sorts into order by eigenvalue
 Householder reduction of a real, symmetric matrix
 eigensolution of a symmetric tridiagonal matrix
 balance a nonsymmetric matrix

 reduce a general matrix to Hessenberg form
 eigenvalues of a Hessenberg matrix

 fast Fourier transform (FFT) in one dimension
 fast Fourier transform of two real functions
 fast Fourier transform of a single real function
 fast sine transform

 fast cosine transform with endpoints
 “staggered” fast cosine transform

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Xxiv Computer Programs by Chapter and Section
 24 fourn fast Fourier transform in multidimensions
 25 rlft3 FFT of real data in two or three dimensions
 2.6 fourfs FFT for huge data sets on external media
 2.6 fourew rewind and permute files, used by fourfs
 3.1 convlv convolution or deconvolution of data using FFT
 3.2 correl correlation or autocorrelation of data using FFT
 3.4 spctrm power spectrum estimation using FFT
 3.6 memcof evaluate maximum entropy (MEM) coefficients
 3.6 fixrts reflect roots of a polynomial into unit circle
 3.6 predic linear prediction using MEM coefficients
 3.7 evlmem power spectral estimation from MEM coefficients
 3.8 period power spectrum of unevenly sampled data
 3.8 fasper power spectrum of unevenly sampled larger data sets
 3.8 spread extirpolate value into array, used by fasper
 3.9 dftcor compute endpoint corrections for Fourier integrals
 3.9 dftint high-accuracy Fourier integrals
 3.10 wtt one-dimensional discrete wavelet transform
 3.10 daub4 Daubechies 4-coefficient wavelet filter
 3.10 pwtset initialize coefficients for pwt
 3.10 pwt partial wavelet transform
 3.10 wtn multidimensional discrete wavelet transform
 4.1 moment calculate moments of a data set
 42 ttest Student’s t-test for difference of means
 42 avevar calculate mean and variance of a data set
 42 tutest Student’s t-test for means, case of unequal variances
 42 tptest Student’s t-test for means, case of paired data
 42 ftest F-test for difference of variances
 43 chsone chi-square test for difference between data and model
 43 chstwo chi-square test for difference between two data sets
 43 ksone Kolmogorov-Smirnov test of data against model
 43 kstwo Kolmogorov-Smirnov test between two data sets
 43 probks Kolmogorov-Smirnov probability function
 44 cntabl contingency table analysis using chi-square
 44 cntab2 contingency table analysis using entropy measure
 45 pearsn Pearson’s correlation between two data sets
 4.6 spear Spearman’s rank correlation between two data sets
 4.6 crank replaces array elements by their rank
 46 kendl11 correlation between two data sets, Kendall’s tau
 4.6 kend12 contingency table analysis using Kendall’s tau
 47 ks2d1s K-S test in two dimensions, data vs. model
 47 quadct count points by quadrants, used by ks2d1s
 47 quadvl quadrant probabilities, used by ks2d1s
 47 ks2d2s K-S test in two dimensions, data vs. data
 48 savgol Savitzky-Golay smoothing coefficients

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Computer Programs by Chapter and Section XXV

 5.2
 5.3
 5.3
 5.4
 5.4
 5.4
 5.4
 5.4
 5.4
 5.5
 5.5
 5.5
 5.7
 5.7

 6.1
 6.1
 6.2
 6.2
 6.2
 63
 64
 64
 64
 6.5
 6.6
 6.6
 6.6
 6.6
 6.6

 7A
 72
 73
 73
 73
 73
 7A
 7A
 7A
 7A

 8.1
 8.1
 8.2
 8.3
 8.3

 fit
 fitexy
 chixy
 1fit
 covsrt
 svdfit
 svdvar
 fpoly
 fleg
 mrqmin
 mrqcof
 fgauss
 medfit
 rofunc

 rk4
 rkdumb
 rkqs
 rkck
 odeint
 mmid
 bsstep
 pzextr
 rzextr
 stoerm
 stiff
 jacobn
 derivs
 simpr
 stifbs

 shoot
 shootf
 solvde
 bksub
 pinvs
 red
 sfroid
 difeq
 sphoot
 sphfpt

 fred2

 fredin
 voltra
 wwghts
 kermom

 least-squares fit data to a straight line

 fit data to a straight line, errors in both x and y

 used by fitexy to calculate a 7

 general linear least-squares fit by normal equations
 rearrange covariance matrix, used by 1fit

 linear least-squares fit by singular value decomposition
 variances from singular value decomposition

 fit a polynomial using 1fit or svdfit

 fit a Legendre polynomial using 1fit or svdfit
 nonlinear least-squares fit, Marquardt’s method

 used by mrqmin to evaluate coefficients

 fit a sum of Gaussians using mrqmin

 fit data to a straight line robustly, least absolute deviation
 fit data robustly, used by medfit

 integrate one step of ODEs, fourth-order Runge-Kutta
 integrate ODEs by fourth-order Runge-Kutta
 integrate one step of ODEs with accuracy monitoring
 Cash-Karp-Runge-Kutta step used by rkqs

 integrate ODEs with accuracy monitoring

 integrate ODEs by modified midpoint method
 integrate ODEs, Bulirsch-Stoer step

 polynomial extrapolation, used by bsstep

 rational function extrapolation, used by bsstep
 integrate conservative second-order ODEs

 integrate stiff ODEs by fourth-order Rosenbrock
 sample Jacobian routine for stiff

 sample derivatives routine for stiff

 integrate stiff ODEs by semi-implicit midpoint rule
 integrate stiff ODEs, Bulirsch-Stoer step

 solve two point boundary value problem by shooting
 ditto, by shooting to a fitting point

 two point boundary value problem, solve by relaxation
 backsubstitution, used by solvde

 diagonalize a sub-block, used by solvde

 reduce columns of a matrix, used by solvde
 spheroidal functions by method of solvde

 spheroidal matrix coefficients, used by sfroid
 spheroidal functions by method of shoot

 spheroidal functions by method of shootf

 solve linear Fredholm equations of the second kind
 interpolate solutions obtained with fred2

 linear Volterra equations of the second kind
 quadrature weights for an arbitrarily singular kernel
 sample routine for moments of a singular kernel

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.
 -eulyoew jo BulAdoo Aue Jo ‘uojonpoides sayyin4 “asn seuosied UMO 4194} 10} Adoo seded auo eyeW 0} suas JeUJE}U! 10} PayUeJGH SI UOISSILAg

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Xxvi Computer Programs by Chapter and Section
 8.3 quadmx sample routine for a quadrature matrix
 8.3 fredex example of solving a singular Fredholm equation
 95 sor elliptic PDE solved by successive overrelaxation method
 9.6 mglin linear elliptic PDE solved by multigrid method
 9.6 rstrct half-weighting restriction, used by mglin, mgfas
 9.6 interp bilinear prolongation, used by mglin, mgfas
 9.6 addint interpolate and add, used by mglin
 9.6 slvsml solve on coarsest grid, used by mglin
 9.6 relax Gauss-Seidel relaxation, used by mglin
 9.6 resid calculate residual, used by mglin
 9.6 copy utility used by mglin, mgfas
 9.6 £1110 utility used by mglin
 9.6 mgfas nonlinear elliptic PDE solved by multigrid method
 9.6 relax2 Gauss-Seidel relaxation, used by mgfas
 9.6 slvsm2 solve on coarsest grid, used by mgfas
 9.6 lop applies nonlinear operator, used by mgfas
 9.6 matadd utility used by mgfas
 9.6 matsub utility used by mgfas
 9.6 anorm2 utility used by mgfas
 20.1 machar diagnose computer’s floating arithmetic
 20.2 igray Gray code and its inverse
 20.3 icrcl cyclic redundancy checksum, used by icre
 20.3 icre cyclic redundancy checksum
 20.3 decchk decimal check digit calculation or verification
 20.4 hufmak construct a Huffman code
 20.4 hufapp append bits to a Huffman code, used by hufmak
 20.4 hufenc use Huffman code to encode and compress a character
 20.4 hufdec use Huffman code to decode and decompress a character
 20.5 arcmak construct an arithmetic code
 20.5 arcode encode or decode a character using arithmetic coding
 20.5 arcsum add integer to byte string, used by arcode
 20.6 mpops multiple precision arithmetic, simpler operations
 20.6 mpmul multiple precision multiply, using FFT methods
 20.6 mpinv multiple precision reciprocal
 20.6 mpdiv multiple precision divide and remainder
 20.6 mpsqrt multiple precision square root
 20.6 mp2dfr multiple precision conversion to decimal base
 20.6 mppi multiple precision example, compute many digits of 7

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.
 -eulyoew jo BulAdoo Aue Jo ‘uojonpoides sayyin4 “asn seuosied UMO 4194} 10} Adoo seded auo eyeW 0} suas JeUJE}U! 10} PayUeJGH SI UOISSILAg

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 Chapter 1. Preliminaries

 1.0 Introduction

 This book, like its predecessor edition, is supposed to teach you methods of
 numerical computing that are practical, efficient, and (insofar as possible) elegant.
 We presume throughout this book that you, the reader, have particular tasks that you
 want to get done. We view our job as educating you on how to proceed. Occasionally
 we may try to reroute you briefly onto a particularly beautiful side road; but by and
 large, we will guide you along main highways that lead to practical destinations.

 Throughout this book, you will find us fearlessly editorializing, telling you
 what you should and shouldn’t do. This prescriptive tone results from a conscious
 decision on our part, and we hope that you will not find it irritating. We do not
 claim that our advice is infallible! Rather, we are reacting against a tendency, in
 the textbook literature of computation, to discuss every possible method that has
 ever been invented, without ever offering a practical judgment on relative merit. We
 do, therefore, offer you our practical judgments whenever we can. As you gain
 experience, you will form your own opinion of how reliable our advice is.

 We presume that you are able to read computer programs in C, that being
 the language of this version of Numerical Recipes (Second Edition). The book
 Numerical Recipes in FORTRAN (Second Edition) is separately available, if you
 prefer to program in that language. Earlier editions of Numerical Recipes in Pascal
 and Numerical Recipes Routines and Examples in BASIC are also available; while
 not containing the additional material of the Second Edition versions in C and
 FORTRAN, these versions are perfectly serviceable if Pascal or BASIC is your
 language of choice.

 When we include programs in the text, they look like this:

 #include <math.h>
 #define RAD (3.14159265/180.0)

 void flmoon(int n, int nph, long *jd, float *frac)
 Our programs begin with an introductory comment summarizing their purpose and explaining
 their calling sequence. This routine calculates the phases of the moon. Given an integer n and
 a code nph for the phase desired (nph = 0 for new moon, 1 for first quarter, 2 for full, 3 for last
 quarter), the routine returns the Julian Day Number jd, and the fractional part of a day frac
 to be added to it, of the nth such phase since January, 1900. Greenwich Mean Time is assumed.
 {

 void nrerror(char error_text[]);

 int i;

 float am,as,c,t,t2,xtra;

 c=ntnph/4.0; This is how we comment an individual
 line.

 *(eoLaWy YON episyno) Bio‘eBpuquies@AJesysno}Oa1Ip 0} [EWE PUas JO ‘(AJUO BOVEWY YVON) E%PZ-ZZ8-008-| [fe 40 WOO UMMM): daY

 O'SGOM IISIA ‘SWWOHGD 40 Sy00q sedivay jEOUAWINN Japs0 OF “payiqiyoud Ajolys si ‘wayndwios Ja/as Aue 0} (auUO sy} Buipnjoul) s:
 -aulyoeul jo BulAdoo Aue Jo ‘uolonpoidas sayjin4 ‘“asn jeuosiad UMO JIAaU} 10} Adoo Jaded auo ayew O} Suasn JeUJE\U! 10} payuRJB S|

 vU
 g
 3
 i
 @.

 ($-80L€b-12S-0 NS!) ONILNdWOOD OISILNAIOS 4O LYV SHL 'O NI SAdIOSY TWOINSWNN Woy e6ed ajdwes

 “AIEMYOS Sadioay ;eOUOWNN Aq Z661-8B6l (D) IYBUAdOD swesBOlY “‘ssalg AysIaAIUN EBpLqueD Aq 2661-8861 (D) jyBUAdOD

 2 Chapter 1. Preliminaries

 t=c/1236.85;
 t2=trt;
 as=359.2242+29.105356*c; You aren't really intended to understand
 am=306 .0253+385 .816918*c+0.010730*t2; this algorithm, but it does work!
 *jd=2415020+28L*n+7L*nph ;
 xtra=0.75933+1 .53058868*c+((1.178e-4)-(1.55e-7) *t) *t2;
 if (mph == 0 || nph == 2)
 xtra += (0.1734-3.93e-4*t)*sin(RAD¥as)-0.4068*sin(RAD*am) ;
 else if (mph == 1 || nph == 3)
 xtra += (0.1721-4.0e-4*t) *sin(RAD*as) -0.6280*sin(RAD*am) ;

 else nrerror("nph is unknown in flmoon"); This is how we will indicate error
 i=(int) (xtra >= 0.0 ? floor(xtra) : ceil(xtra-1.0)); conditions.
 xjd += i;

 *frac=xtra-i;

 If the syntax of the function definition above looks strange to you, then you are
 probably used to the older Kernighan and Ritchie (“K&R”) syntax, rather than that of
 the newer ANSI C-. In this edition, we adopt ANSI C as our standard. You might want
 to look ahead to $1.2 where ANSI C function prototypes are discussed in more detail.

 Note our convention of handling all errors and exceptional cases with a statement
 like nrerror("some error message") ;. The function nrerror() is part of a
 small file of utility programs, nrutil.c, listed in Appendix B at the back of the
 book. This Appendix includes a number of other utilities that we will describe later in
 this chapter. Function nrerror () prints the indicated error message to your stderr
 device (usually your terminal screen), and then invokes the function exit (), which
 terminates execution. The function exit () is in every C library we know of; but if
 you find it missing, you can modify nrerror () so that it does anything else that will
 halt execution. For example, you can have it pause for input from the keyboard, and
 then manually interrupt execution. In some applications, you will want to modify
 nrerror () to do more sophisticated error handling, for example to transfer control
 somewhere else, with an error flag or error code set.

 We will have more to say about the C programming language, its conventions
 and style, in §1.1 and §1.2.

 Computational Environment and Program Validation

 Our goal is that the programs in this book be as portable as possible, across
 different platforms (models of computer), across different operating systems, and
 across different C compilers. C was designed with this type of portability in
 mind. Nevertheless, we have found that there is no substitute for actually checking
 all programs on a variety of compilers, in the process uncovering differences in
 library structure or contents, and even occasional differences in allowed syntax. As
 surrogates for the large number of possible combinations, we have tested all the
 programs in this book on the combinations of machines, operating systems, and
 compilers shown on the accompanying table. More generally, the programs should
 run without modification on any compiler that implements the ANSI C standard,
 as described for example in Harbison and Steele’s excellent book [1]. With small
 modifications, our programs should run on any compiler that implements the older,
 de facto K&R standard [2]. An example of the kind of trivial incompatibility to
 watch out for is that ANSI C requires the memory allocation functions malloc ()

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 e)

 “aleEMYOS Sedioay |eEouEWNN Aq Z66 1-886} (O) UBUAdOD sweiGo1g “ssl AsionluN eBpuquied Aq 2661-886 (

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.0 Introduction

 Tested Machines and Compilers

 Hardware

 O/S Version

 Compiler Version

 IBM PC compatible 486/33

 MS-DOS 5.0/Windows 3.1

 Microsoft C/C++ 7.0

 IBM PC compatible 486/33 MS-DOS 5.0 Borland C/C++ 2.0

 IBM RS/6000 AIX 3.2 IBM xlc 1.02

 DECstation 5000/25 ULTRIX 4.2A CodeCenter (Saber) C 3.1.1
 DECsystem 5400 ULTRIX 4.1 GNU C Compiler 2.1

 Sun SPARCstation 2 SunOS 4.1 GNU C Compiler 1.40
 DECstation 5000/200 ULTRIX 4.2 DEC RISC C 2.1*

 Sun SPARCstation 2 SunOS 4.1 Sun ce 1.1*

 *compiler version does not fully implement ANSI C; only K&R validated

 and free() to be declared via the header stdlib.h; some older compilers require
 them to be declared with the header file malloc.h, while others regard them as
 inherent in the language and require no header file at all.

 In validating the programs, we have taken the program source code directly
 from the machine-readable form of the book’s manuscript, to decrease the chance
 of propagating typographical errors. “Driver” or demonstration programs that we
 used as part of our validations are available separately as the Numerical Recipes
 Example Book (C), as well as in machine-readable form. If you plan to use more
 than a few of the programs in this book, or if you plan to use programs in this book
 on more than one different computer, then you may find it useful to obtain a copy
 of these demonstration programs.

 Of course we would be foolish to claim that there are no bugs in our programs,
 and we do not make such a claim. We have been very careful, and have benefitted
 from the experience of the many readers who have written to us. If you find a new
 bug, please document it and tell us!

 Compatibility with the First Edition

 If you are accustomed to the Numerical Recipes routines of the First Edition, rest
 assured: almost all of them are still here, with the same names and functionalities,
 often with major improvements in the code itself. In addition, we hope that you
 will soon become equally familiar with the added capabilities of the more than 100
 routines that are new to this edition.

 We have retired a small number of First Edition routines, those that we believe
 to be clearly dominated by better methods implemented in this edition. A table,
 following, lists the retired routines and suggests replacements.

 First Edition users should also be aware that some routines common to both
 editions have alterations in their calling interfaces, so are not directly “plug compat-
 ible.” A fairly complete list is: chsone, chstwo, covsrt, dfpmin, laguer, 1fit,
 memcof,mrqcof, mrqmin, pzextr, ran4, realft, rzextr, shoot, shootf. There
 may be others (depending in part on which printing of the First Edition is taken
 for the comparison). If you have written software of any appreciable complexity

 *(eouaWy YLON epis}no) Bio’ aBpuquieo® les}sno}0~a11p 0} |fewWa PUBS JO ‘(KjUO BOUV@WIY YUON) EZPZ-ZZ8-008- | [29 10 WOO™U'MMy/: cy
 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.

 -aulyoew jo BulAdoo Aue Jo ‘uojonposdes sayyin4 “asn euossed uMO 4194} 10} Adoo seded auo ayeW! 0} suasn JeUsE}UI 10} payue6 si

 “aremyog sedivay /eouawinn Aq 2661-8861 (9) 1UBUIAdOD suIesBolg ‘ssalg AyIsIanlu eBPUqUIeD Kq Z661-BB6L (9) 1YBUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 4 Chapter 1. Preliminaries

 Previous Routines Omitted from This Edition

 Name(s) Replacement(s) Comment
 adi mglin or mgfas better method
 cosft cosfti or cosft2 choice of boundary conditions
 cel,e12 rf,rd,rj,rc better algorithms
 des, desks ran4 now uses psdes was too slow
 mdiani,mdian2 select, selip more general
 qcksrt sort name change (sort is now hpsort)
 rkqc rkqs better method
 smooft use convlv with coefficients from savgol
 sparse linbcg more general

 that is dependent on First Edition routines, we do not recommend blindly replacing
 them by the corresponding routines in this book. We do recommend that any new
 programming efforts use the new routines.

 About References

 You will find references, and suggestions for further reading, listed at the
 end of most sections of this book. References are cited in the text by bracketed
 numbers like this [3].

 Because computer algorithms often circulate informally for quite some time
 before appearing in a published form, the task of uncovering “primary literature”
 is sometimes quite difficult. We have not attempted this, and we do not pretend
 to any degree of bibliographical completeness in this book. For topics where a
 substantial secondary literature exists (discussion in textbooks, reviews, etc.) we
 have consciously limited our references to a few of the more useful secondary
 sources, especially those with good references to the primary literature. Where the
 existing secondary literature is insufficient, we give references to a few primary
 sources that are intended to serve as starting points for further reading, not as
 complete bibliographies for the field.

 The order in which references are listed is not necessarily significant. It reflects a
 compromise between listing cited references in the order cited, and listing suggestions
 for further reading in a roughly prioritized order, with the most useful ones first.

 The remaining three sections of this chapter review some basic concepts of
 programming (control structures, etc.), discuss a set of conventions specific to C
 that we have adopted in this book, and introduce some fundamental concepts in
 numerical analysis (roundoff error, etc.). Thereafter, we plunge into the substantive
 material of the book.

 CITED REFERENCES AND FURTHER READING:

 Harbison, S.P., and Steele, G.L., Jr. 1991, C: A Reference Manual, 3rd ed. (Englewood Cliffs,
 NJ: Prentice-Hall). [1]

 *(eouaWy YLON epis}no) Bio’ aBpuquieo® les}sno}0~a11p 0} |fewWa PUBS JO ‘(KjUO BOUV@WIY YUON) EZPZ-ZZ8-008- | [29 10 WOO™U'MMy/: cy
 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.

 -aulyoew jo BulAdoo Aue Jo ‘uojonposdes sayyin4 “asn euossed uMO 4194} 10} Adoo seded auo ayeW! 0} suasn JeUsE}UI 10} payue6 si

 “aremyog sedivay /eouawinn Aq 2661-8861 (9) 1UBUIAdOD suIesBolg ‘ssalg AyIsIanlu eBPUqUIeD Kq Z661-BB6L (9) 1YBUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.1 Program Organization and Control Structures 5

 Kernighan, B., and Ritchie, D. 1978, The C Programming Language (Englewood Cliffs, NJ:
 Prentice-Hall). [2] [Reference for K&R “traditional” C. Later editions of this book conform
 to the ANSI C standard.]

 Meeus, J. 1982, Astronomical Formulae for Calculators, 2nd ed., revised and enlarged (Rich-
 mond, VA: Willmann-Bell). [3]

 1.1 Program Organization and Control
 Structures

 We sometimes like to point out the close analogies between computer programs,
 on the one hand, and written poetry or written musical scores, on the other. All
 three present themselves as visual media, symbols on a two-dimensional page or
 computer screen. Yet, in all three cases, the visual, two-dimensional, frozen-in-time
 representation communicates (or is supposed to communicate) something rather
 different, namely a process that unfolds in time. A poem is meant to be read; music,
 played; a program, executed as a sequential series of computer instructions.

 In all three cases, the target of the communication, in its visual form, is a human
 being. The goal is to transfer to him/her, as efficiently as can be accomplished,
 the greatest degree of understanding, in advance, of how the process will unfold in
 time. In poetry, this human target is the reader. In music, it is the performer. In
 programming, it is the program user.

 Now, you may object that the target of communication of a program is not
 a human but a computer, that the program user is only an irrelevant intermediary,
 a lackey who feeds the machine. This is perhaps the case in the situation where
 the business executive pops a diskette into a desktop computer and feeds that
 computer a black-box program in binary executable form. The computer, in this
 case, doesn’t much care whether that program was written with “good programming
 practice” or not.

 We envision, however, that you, the readers of this book, are in quite a different
 situation. You need, or want, to know not just what a program does, but also how
 it does it, so that you can tinker with it and modify it to your particular application.
 You need others to be able to see what you have done, so that they can criticize or
 admire. In such cases, where the desired goal is maintainable or reusable code, the
 targets of a program’s communication are surely human, not machine.

 One key to achieving good programming practice is to recognize that pro-
 gramming, music, and poetry — all three being symbolic constructs of the human
 brain — are naturally structured into hierarchies that have many different nested
 levels. Sounds (phonemes) form small meaningful units (morphemes) which in turn
 form words; words group into phrases, which group into sentences; sentences make
 paragraphs, and these are organized into higher levels of meaning. Notes form
 musical phrases, which form themes, counterpoints, harmonies, etc.; which form
 movements, which form concertos, symphonies, and so on.

 The structure in programs is equally hierarchical. Appropriately, good program-
 ming practice brings different techniques to bear on the different levels [1-3]. Ata low
 level is the ascii character set. Then, constants, identifiers, operands, operators.

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 6 Chapter 1. Preliminaries

 Then program statements, like a[j+1]=b+c/3.0;. Here, the best programming
 advice is simply be clear, or (correspondingly) don’t be too tricky. You might
 momentarily be proud of yourself at writing the single line

 k=(2-j)*(1+3*j)/2;

 if you want to permute cyclically one of the values j = (0,1, 2) into respectively
 k = (1,2,0). You will regret it later, however, when you try to understand that
 line. Better, and likely also faster, is

 k=j+1;
 if (k == 3) k=0;

 Many programming stylists would even argue for the ploddingly literal

 switch (j) {
 case 0: k=1; break;
 case 1: k=2; break;
 case 2: k=0; break;
 default: {
 fprintf(stderr,"unexpected value for j");
 exit(1);

 on the grounds that it is both clear and additionally safeguarded from wrong assump-
 tions about the possible values of j. Our preference among the implementations
 is for the middle one.

 In this simple example, we have in fact traversed several levels of hierarchy:
 Statements frequently come in “groups” or “blocks” which make sense only taken
 as a whole. The middle fragment above is one example. Another is

 swap=a[j];
 alj]=b(jl;
 b[jl=swap;

 which makes immediate sense to any programmer as the exchange of two variables,
 while

 ans=sum=0.0;
 n=1;

 is very likely to be an initialization of variables prior to some iterative process. This
 level of hierarchy in a program is usually evident to the eye. It is good programming
 practice to put in comments at this level, e.g., “initialize” or “exchange variables.”

 The next level is that of control structures. These are things like the switch
 construction in the example above, for loops, and so on. This level is sufficiently
 important, and relevant to the hierarchical level of the routines in this book, that
 we will come back to it just below.

 At still higher levels in the hierarchy, we have functions and modules, and the
 whole “global” organization of the computational task to be done. In the musical
 analogy, we are now at the level of movements and complete works. At these levels,

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.1 Program Organization and Control Structures 7

 modularization and encapsulation become important programming concepts, the
 general idea being that program units should interact with one another only through
 clearly defined and narrowly circumscribed interfaces. Good modularization practice
 is an essential prerequisite to the success of large, complicated software projects,
 especially those employing the efforts of more than one programmer. It is also good
 practice (if not quite as essential) in the less massive programming tasks that an
 individual scientist, or reader of this book, encounters.

 Some computer languages, such as Modula-2 and C++, promote good modular-
 ization with higher-level language constructs absent in C. In Modula-2, for example,
 functions, type definitions, and data structures can be encapsulated into “modules”
 that communicate through declared public interfaces and whose internal workings
 are hidden from the rest of the program [4]. In the C++ language, the key concept
 is “class,” a user-definable generalization of data type that provides for data hiding,
 automatic initialization of data, memory management, dynamic typing, and operator
 overloading (i.e., the user-definable extension of operators like + and * so as to be
 appropriate to operands in any particular class) [5]. Properly used in defining the data
 structures that are passed between program units, classes can clarify and circumscribe
 these units’ public interfaces, reducing the chances of programming error and also
 allowing a considerable degree of compile-time and run-time error checking.

 Beyond modularization, though depending on it, lie the concepts of object-
 oriented programming. Here a programming language, such as C++ or Turbo Pascal
 5.5 [6], allows a module’s public interface to accept redefinitions of types or actions,
 and these redefinitions become shared all the way down through the module’s
 hierarchy (so-called polymorphism). For example, a routine written to invert a matrix
 of real numbers could — dynamically, at run time — be made able to handle complex
 numbers by overloading complex data types and corresponding definitions of the
 arithmetic operations. Additional concepts of inheritance (the ability to define a data
 type that “inherits” all the structure of another type, plus additional structure of its
 own), and object extensibility (the ability to add functionality to a module without
 access to its source code, e.g., at run time), also come into play.

 We have not attempted to modularize, or make objects out of, the routines in this
 book, for at least two reasons. First, the chosen language, C, does not really make
 this possible. Second, we envision that you, the reader, might want to incorporate
 the algorithms in this book, a few at a time, into modules or objects with a structure
 of your own choosing. There does not exist, at present, a standard or accepted set
 of “classes” for scientific object-oriented computing. While we might have tried to
 invent such a set, doing so would have inevitably tied the algorithmic content of the
 book (which is its raison d’étre) to some rather specific, and perhaps haphazard, set
 of choices regarding class definitions.

 On the other hand, we are not unfriendly to the goals of modular and object-
 oriented programming. Within the limits of C, we have therefore tried to structure
 our programs to be “object friendly.” That is one reason we have adopted ANSI
 C with its function prototyping as our default C dialect (see §1.2). Also, within
 our implementation sections, we have paid particular attention to the practices of
 structured programming, as we now discuss.

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 8 Chapter 1. Preliminaries

 Control Structures

 An executing program unfolds in time, but not strictly in the linear order in
 which the statements are written. Program statements that affect the order in which
 statements are executed, or that affect whether statements are executed, are called
 control statements. Control statements never make useful sense by themselves. They
 make sense only in the context of the groups or blocks of statements that they in turn
 control. If you think of those blocks as paragraphs containing sentences, then the
 control statements are perhaps best thought of as the indentation of the paragraph
 and the punctuation between the sentences, not the words within the sentences.

 We can now say what the goal of structured programming is. It is to make
 program control manifestly apparent in the visual presentation of the program. You
 see that this goal has nothing at all to do with how the computer sees the program.
 As already remarked, computers don’t care whether you use structured programming
 or not. Human readers, however, do care. You yourself will also care, once you
 discover how much easier it is to perfect and debug a well-structured program than
 one whose control structure is obscure.

 You accomplish the goals of structured programming in two complementary
 ways. First, you acquaint yourself with the small number of essential control
 structures that occur over and over again in programming, and that are therefore
 given convenient representations in most programming languages. You should learn
 to think about your programming tasks, insofar as possible, exclusively in terms of
 these standard control structures. In writing programs, you should get into the habit
 of representing these standard control structures in consistent, conventional ways.

 “Doesn’t this inhibit creativity?” our students sometimes ask. Yes, just
 as Mozart’s creativity was inhibited by the sonata form, or Shakespeare’s by the
 metrical requirements of the sonnet. The point is that creativity, when it is meant to
 communicate, does well under the inhibitions of appropriate restrictions on format.

 Second, you avoid, insofar as possible, control statements whose controlled
 blocks or objects are difficult to discern at a glance. This means, in practice, that you
 must try to avoid named labels on statements and goto’s. It is not the goto’s that
 are dangerous (although they do interrupt one’s reading of a program); the named
 statement labels are the hazard. In fact, whenever you encounter a named statement
 label while reading a program, you will soon become conditioned to get a sinking
 feeling in the pit of your stomach. Why? Because the following questions will, by
 habit, immediately spring to mind: Where did control come from in a branch to this
 label? It could be anywhere in the routine! What circumstances resulted in a branch
 to this label? They could be anything! Certainty becomes uncertainty, understanding
 dissolves into a morass of possibilities.

 Some examples are now in order to make these considerations more concrete
 (see Figure 1.1.1).

 Catalog of Standard Structures

 Iteration. In C, simple iteration is performed with a for loop, for example

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 Se
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ac
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 a3
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.1 Program Organization and Control Structures

 Sample page from NUMERICAL RECIPES IN C: THE ART OF SCIENTIFIC COMPUTING (ISBN 0-521-43108-5)

 Copyright (C) 1988-1992 by Cambridge University Press. Programs Copyright (C) 1988-1992 by Numerical Recipes Software.
 i granted for internet users to make one paper copy for their own personal use. Further reproduction, or any copying of machine-
 Ss (including this one) to any server computer, is strictly prohibited. To order Numerical Recipes books or CDROMs,

 http:/Awww.nr.com or call 1-800-872-7423 (North America only), or send email to directcustserv @cambridge.org (outside North America).

 false

 ck
 (b)

 blo
 WHILE iteration

 iteration
 complete?
 increment
 index
 FOR iteration
 (a)
 block

 (5
 2
 S

 BREAK iteration

 DO WHILE iteration

 isit website

 (d)

 Standard control structures used in structured programming: (a) for iteration; (b) while

 iteration; (c) do while iteration; (d) break iteration; (e) if structure; (f) switch structure

 Figure 1.1.1.

 Preliminaries

 Chapter 1.

 10

 false

 false

 condition

 Sample page from NUMERICAL RECIPES IN C: THE ART OF SCIENTIFIC COMPUTING (ISBN 0-521-43108-5)

 Copyright (C) 1988-1992 by Cambridge Univer: Press. Programs Copyright (C) 1988-1992 by Numerical Recipes Software.

 Permission is granted for internet users to make one paper copy for their own personal use. Further reproduction, or any copying of machine-
 readable files (including this one) to any server computer, is strictly prohibited. To order Numerical Recipes books or CDROMs, visit website
 http:/Avww.nr.com or call 1-800-872-7423 (North America only), or send email to directcustserv @cambridge.org (outside North America).

 else block

 IF structure
 ()

 “4

 2
 s
 3
 &

 By
 3

 SWITCH structure

 (f)
 Standard control structures used in structured programming (see caption on previous page).

 Figure 1.1.1.

 1.1 Program Organization and Control Structures 11

 Notice how we always indent the block of code that is acted upon by the control
 structure, leaving the structure itself unindented. Notice also our habit of putting the
 initial curly brace on the same line as the for statement, instead of on the next line.
 This saves a full line of white space, and our publisher loves us for it.

 IF structure. This structure in C is similar to that found in Pascal, Algol,
 FORTRAN and other languages, and typically looks like

 if (4

 +
 else if (...) {

 +

 else {

 +

 Since compound-statement curly braces are required only when there is more
 than one statement in a block, however, C’s if construction can be somewhat less
 explicit than the corresponding structure in FORTRAN or Pascal. Some care must be
 exercised in constructing nested if clauses. For example, consider the following:

 if (b > 3)
 if (a > 3) b += 1;
 else b -= 1; /* questionable! */

 As judged by the indentation used on successive lines, the intent of the writer of
 this code is the following: ‘If b is greater than 3 and a is greater than 3, then
 increment b. If b is not greater than 3, then decrement b.’ According to the rules
 of C, however, the actual meaning is ‘If b is greater than 3, then evaluate a. If a is
 greater than 3, then increment b, and if a is less than or equal to 3, decrement b.’ The
 point is that an else clause is associated with the most recent open if statement,
 no matter how you lay it out on the page. Such confusions in meaning are easily
 resolved by the inclusion of braces. They may in some instances be technically
 superfluous; nevertheless, they clarify your intent and improve the program. The
 above fragment should be written as

 if (b> 3) {

 if (a > 3) b += 1;
 } else {

 b -= 1;
 +

 Here is a working program that consists dominantly of if control statements:

 #include <math.h>
 #define IGREG (15+31L*(10+12L*1582) ) Gregorian Calendar adopted Oct. 15, 1582.

 long julday(int mm, int id, int iyyy)

 In this routine julday returns the Julian Day Number that begins at noon of the calendar date
 specified by month mm, day id, and year iyyy, all integer variables. Positive year signifies A.D.;
 negative, B.C. Remember that the year after 1 B.C. was 1 A.D.

 {

 void nrerror(char error_text[]);

 *(eouaWy YLON epis}no) Bio’ aBpuquieo® les}sno}0~a11p 0} |fewWa PUBS JO ‘(KjUO BOUV@WIY YUON) EZPZ-ZZ8-008- | [29 10 WOO™U'MMy/: cy
 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.

 -aulyoew jo BulAdoo Aue Jo ‘uojonposdes sayyin4 “asn euossed uMO 4194} 10} Adoo seded auo ayeW! 0} suasn JeUsE}UI 10} payue6 si

 “aremyog sedivay /eouawinn Aq 2661-8861 (9) 1UBUIAdOD suIesBolg ‘ssalg AyIsIanlu eBPUqUIeD Kq Z661-BB6L (9) 1YBUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 12 Chapter 1. Preliminaries

 long jul;

 int ja, jy=iyyy, jm;

 if (jy == 0) nrerror("julday: there is no year zero.");

 if (jy < 0) ++jy;

 if (mm > 2) { Here is an example of a block IF-structure.
 jm=mm+1 ;

 } else {
 ~Sys
 jm=mm+13;

 +

 jul = (long) (floor(365.25*jy)+floor(30.6001* jm) +id+1720995) ;

 if (id+31L*(mm+12L*iyyy) >= IGREG) { Test whether to change to Gregorian Cal-
 ja=(int) (0.01*jy); endar.

 jul += 2-jat(int) (0.25*ja);
 +

 return jul;

 (Astronomers number each 24-hour period, starting and ending at noon, with
 a unique integer, the Julian Day Number [7]. Julian Day Zero was a very long
 time ago; a convenient reference point is that Julian Day 2440000 began at noon
 of May 23, 1968. If you know the Julian Day Number that begins at noon of a
 given calendar date, then the day of the week of that date is obtained by adding
 1 and taking the result modulo base 7; a zero answer corresponds to Sunday, | to
 Monday, ..., 6 to Saturday.)

 While iteration. Most languages (though not FORTRAN, incidentally) provide
 for structures like the following C example:

 while (n < 1000) {
 n *= 2;
 j t= 1;

 It is the particular feature of this structure that the control-clause (in this case
 n < 1000) is evaluated before each iteration. If the clause is not true, the enclosed
 statements will not be executed. In particular, if this code is encountered at a time
 when n is greater than or equal to 1000, the statements will not even be executed once.

 Do-While iteration. | Companion to the while iteration is a related control-
 structure that tests its control-clause at the end of each iteration. In C, it looks
 like this:

 do {
 n *= 2;
 j t= 1;
 } while (mn < 1000);

 In this case, the enclosed statements will be executed at least once, independent
 of the initial value of n.

 Break. In this case, you have a loop that is repeated indefinitely until some
 condition tested somewhere in the middle of the loop (and possibly tested in more

 *(eouaWy YLON epis}no) Bio’ aBpuquieo® les}sno}0~a11p 0} |fewWa PUBS JO ‘(KjUO BOUV@WIY YUON) EZPZ-ZZ8-008- | [29 10 WOO™U'MMy/: cy
 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.

 -aulyoew jo BulAdoo Aue Jo ‘uojonposdes sayyin4 “asn euossed uMO 4194} 10} Adoo seded auo ayeW! 0} suasn JeUsE}UI 10} payue6 si

 “aremyog sedivay /eouawinn Aq 2661-8861 (9) 1UBUIAdOD suIesBolg ‘ssalg AyIsIanlu eBPUqUIeD Kq Z661-BB6L (9) 1YBUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.1 Program Organization and Control Structures 13

 than one place) becomes true. At that point you wish to exit the loop and proceed
 with what comes after it. In C the structure is implemented with the simple break
 statement, which terminates execution of the innermost for, while, do, or switch
 construction and proceeds to the next sequential instruction. (In Pascal and standard
 FORTRAN, this structure requires the use of statement labels, to the detriment of clear
 programming.) A typical usage of the break statement is:

 for(;;) {
 [statements before the test]
 if (...) break;
 [statements after the test]
 +

 [next sequential instruction]

 Here is a program that uses several different iteration structures. One of us was
 once asked, for a scavenger hunt, to find the date of a Friday the 13th on which the
 moon was full. This is a program which accomplishes that task, giving incidentally
 all other Fridays the 13th as a by-product.

 #include <stdio.h>

 #include <math.h>

 #define ZON -5.0 Time zone —5 is Eastern Standard Time.
 #tdefine IYBEG 1900 The range of dates to be searched.
 #define IYEND 2000

 int main(void) /* Program badluk */
 {
 void flmoon(int n, int nph, long *jd, float *frac);
 long julday(int mm, int id, int iyyy);
 int ic,icon,idwk,im,iyyy,n;
 float timzon = ZON/24.0,frac;
 long jd,jday;

 printf("\nFull moons on Friday the 13th from %5d to %5d\n",IYBEG,IYEND) ;
 for (iyyy=IYBEG;iyyy<=IYEND;iyyy++) { Loop over each year,
 for (im=1;im<=12;im++) { and each month.
 jday=julday(im,13,iyyy) ; Is the 13th a Friday?
 idwk=(int) ((jdayt+1) % 7);
 if (idwk == 5) {
 n=(int) (12.37*(iyyy-1900+(im-0.5)/12.0));
 This value n is a first approximation to how many full moons have occurred
 since 1900. We will feed it into the phase routine and adjust it up or down
 until we determine that our desired 13th was or was not a full moon. The
 variable icon signals the direction of adjustment.

 icon=0;
 for (;;) {
 flmoon(n,2,&jd,&frac) ; Get date of full moon n.
 frac=24.0*(fracttimzon) ; Convert to hours in correct time zone.
 if (frac < 0.0) { Convert from Julian Days beginning at
 --jd; noon to civil days beginning at mid-
 frac += 24.0; night.
 +
 if (frac > 12.0) {
 ++jd;
 frac -= 12.0;
 } else
 frac += 12.0;
 if (jd == jday) { Did we hit our target day?

 printf ("\n42d/13/%4d\n" , im, iyyy) ;
 printf("4s %5.1f %s\n","Full moon",frac,

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 doa,

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 14 Chapter 1. Preliminaries

 "hrs after midnight (EST)");

 break; Part of the break-structure, a match.
 } else { Didn't hit it.
 ic=(jday >= jd ? 1: -1);
 if (ic == (-icon)) break; Another break, case of no match.
 icon=ic;
 n += ic;
 +
 }
 }
 }
 +
 return 0;

 If you are merely curious, there were (or will be) occurrences of a full moon
 on Friday the 13th (time zone GMT—5) on: 3/13/1903, 10/13/1905, 6/13/1919,
 1/13/1922, 11/13/1970, 2/13/1987, 10/13/2000, 9/13/2019, and 8/13/2049.

 Other “standard” structures. Our advice is to avoid them. Every pro-
 gramming language has some number of “goodies” that the designer just couldn’t
 resist throwing in. They seemed like a good idea at the time. Unfortunately they
 don’t stand the test of time! Your program becomes difficult to translate into other
 languages, and difficult to read (because rarely used structures are unfamiliar to the
 reader). You can almost always accomplish the supposed conveniences of these
 structures in other ways.

 In C, the most problematic control structure is the switch...case...default
 construction (see Figure 1.1.1), which has historically been burdened by uncertainty,
 from compiler to compiler, about what data types are allowed in its control expression.
 Data types char and int are universally supported. For other data types, e.g., float
 or doub1e, the structure should be replaced by a more recognizable and translatable
 if...else construction. ANSI C allows the control expression to be of type long,
 but many older compilers do not.

 The continue; construction, while benign, can generally be replaced by an
 if construction with no loss of clarity.

 About “Advanced Topics”

 Material set in smaller type, like this, signals an “advanced topic,” either one outside of
 the main argument of the chapter, or else one requiring of you more than the usual assumed
 mathematical background, or else (in a few cases) a discussion that is more speculative or an
 algorithm that is less well-tested. Nothing important will be lost if you skip the advanced
 topics on a first reading of the book.

 You may have noticed that, by its looping over the months and years, the program badluk
 avoids using any algorithm for converting a Julian Day Number back into a calendar date. A
 routine for doing just this is not very interesting structurally, but it is occasionally useful:

 #include <math.h>
 #tdefine IGREG 2299161

 void caldat(long julian, int *mm, int *id, int *iyyy)
 Inverse of the function julday given above. Here julian is input as a Julian Day Number,
 and the routine outputs mm,id, and iyyy as the month, day, and year on which the specified
 Julian Day started at noon.
 t

 long ja, jalpha, jb, jc, jd, je;

 *(eouaWy YLON epis}no) Bio’ aBpuquieo® les}sno}0~a11p 0} |fewWa PUBS JO ‘(KjUO BOUV@WIY YUON) EZPZ-ZZ8-008- | [29 10 WOO™U'MMy/: cy
 OUSGOM IISIA ‘SIWOHGD JO Sy00q sedioey jedaWINN Japso OF “payiqiyoud Ajyouys SI ‘“aNdwios JaAsas Aue 0} (aUO Siu} Bulpnjoul) sajy ajqepea.

 -aulyoew jo BulAdoo Aue Jo ‘uojonposdes sayyin4 “asn euossed uMO 4194} 10} Adoo seded auo ayeW! 0} suasn JeUsE}UI 10} payue6 si

 “aremyog sedivay /eouawinn Aq 2661-8861 (9) 1UBUIAdOD suIesBolg ‘ssalg AyIsIanlu eBPUqUIeD Kq Z661-BB6L (9) 1YBUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.2 Some C Conventions for Scientific Computing 15

 if (julian >= IGREG) { Cross-over to Gregorian Calendar produces this correc-
 jalpha=(long)(((double) (julian-1867216)-0.25)/36524.25) ; tion.
 ja=julian+i+jalpha-(long) (0.25*jalpha) ;

 } else if (julian < 0) { Make day number positive by adding integer number of

 ja=julian+36525*(1-julian/36525) ; Julian centuries, then subtract them off
 } else at the end.

 ja=julian;
 jb=jat1524;

 jc=Clong) (6680.0+((double) (jb-2439870)-122.1)/365.25) ;
 j= (long) (365+jc+(0.25+jc));

 je=(long) ((jb-jd) /30.6001) ;

 *id=jb-jd-(long) (30.6001*je) ;

 *mm=je-1;

 if (*mm > 12) *mm -= 12;

 *iyyy=jc-4715;

 aif (*mm > 2) --(*iyyy);

 if (*iyyy <= 0) --(+iyyy);

 if (julian < 0) *iyyy -= 100*(1-julian/36525) ;

 (For additional calendrical algorithms, applicable to various historical calendars, see [8].)

 CITED REFERENCES AND FURTHER READING:

 Harbison, S.P., and Steele, G.L., Jr. 1991, C: A Reference Manual, 3rd ed. (Englewood Cliffs,
 NJ: Prentice-Hall).

 Kernighan, B.W. 1978, The Elements of Programming Style (New York: McGraw-Hill). [1]

 Yourdon, E. 1975, Techniques of Program Structure and Design (Englewood Cliffs, NJ: Prentice-
 Hall). [2]

 Jones, R., and Stewart, I. 1987, The Art of C Programming (New York: Springer-Verlag). [3]

 Hoare, C.A.R. 1981, Communications of the ACM, vol. 24, pp. 75-83.

 Wirth, N. 1983, Programming in Modula-2, 3rd ed. (New York: Springer-Verlag). [4]

 Stroustrup, B. 1986, The C++ Programming Language (Reading, MA: Addison-Wesley). [5]

 Borland International, Inc. 1989, Turbo Pascal 5.5 Object-Oriented Programming Guide (Scotts
 Valley, CA: Borland International). [6]

 Meeus, J. 1982, Astronomical Formulae for Calculators, 2nd ed., revised and enlarged (Rich-
 mond, VA: Willmann-Bell). [7]

 Hatcher, D.A. 1984, Quarterly Journal of the Royal Astronomical Society, vol. 25, pp. 583-55; see
 also op. cit. 1985, vol. 26, pp. 151-155, and 1986, vol. 27, pp. 506-507. [8]

 1.2 Some C Conventions for Scientific
 Computing

 The C language was devised originally for systems programming work, not for
 scientific computing. Relative to other high-level programming languages, C puts
 the programmer “‘very close to the machine” in several respects. It is operator-rich,
 giving direct access to most capabilities of a machine-language instruction set. It
 has a large variety of intrinsic data types (short and long, signed and unsigned
 integers; floating and double-precision reals; pointer types; etc.), and a concise
 syntax for effecting conversions and indirections. It defines an arithmetic on pointers
 (addresses) that relates gracefully to array addressing and is highly compatible with
 the index register structure of many computers.

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 16 Chapter 1. Preliminaries

 Portability has always been another strong point of the C language. C is the
 underlying language of the UNIX operating system; both the language and the
 operating system have by now been implemented on literally hundreds of different
 computers. The language’s universality, portability, and flexibility have attracted
 increasing numbers of scientists and engineers to it. It is commonly used for the
 real-time control of experimental hardware, often in spite of the fact that the standard
 UNIX kernel is less than ideal as an operating system for this purpose.

 The use of C for higher level scientific calculations such as data analysis,
 modeling, and floating-point numerical work has generally been slower in developing.
 In part this is due to the entrenched position of FORTRAN as the mother-tongue of
 virtually all scientists and engineers born before 1960, and most born after. In
 part, also, the slowness of C’s penetration into scientific computing has been due to
 deficiencies in the language that computer scientists have been (we think, stubbornly)
 slow to recognize. Examples are the lack of a good way to raise numbers to small
 integer powers, and the “implicit conversion of float to double” issue, discussed
 below. Many, though not all, of these deficiencies are overcome in the ANSI C
 Standard. Some remaining deficiencies will undoubtedly disappear over time.

 Yet another inhibition to the mass conversion of scientists to the C cult has been,
 up to the time of writing, the decided lack of high-quality scientific or numerical
 libraries. That is the lacuna into which we thrust this edition of Numerical Recipes.
 We certainly do not claim to be a complete solution to the problem. We do hope
 to inspire further efforts, and to lay out by example a set of sensible, practical
 conventions for scientific C programming.

 The need for programming conventions in C is very great. Far from the problem
 of overcoming constraints imposed by the language (our repeated experience with
 Pascal), the problem in C is to choose the best and most natural techniques from
 multiple opportunities — and then to use those techniques completely consistently
 from program to program. In the rest of this section, we set out some of the issues,
 and describe the adopted conventions that are used in all of the routines in this book.

 Function Prototypes and Header Files

 ANSI C allows functions to be defined with function prototypes, which specify
 the type of each function parameter. If a function declaration or definition with
 a prototype is visible, the compiler can check that a given function call invokes
 the function with the correct argument types. All the routines printed in this book
 are in ANSI C prototype form. For the benefit of readers with older “traditional
 K&R” C compilers, the Numerical Recipes C Diskette includes two complete sets of
 programs, one in ANSI, the other in K&R.

 The easiest way to understand prototypes is by example. A function definition
 that would be written in traditional C as

 int g(x,y,z)
 int x,y;
 float z;

 becomes in ANSI C

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.2 Some C Conventions for Scientific Computing 17

 int g(int x, int y, float z)

 A function that has no parameters has the parameter type list void.

 A function declaration (as contrasted to a function definition) is used to
 “introduce” a function to a routine that is going to call it. The calling routine needs
 to know the number and type of arguments and the type of the returned value. In
 a function declaration, you are allowed to omit the parameter names. Thus the
 declaration for the above function is allowed to be written

 int g(int, int, float);

 If a C program consists of multiple source files, the compiler cannot check the
 consistency of each function call without some additional assistance. The safest
 way to proceed is as follows:

 e Every external function should have a single prototype declaration in a
 header (.h) file.

 e The source file with the definition (body) of the function should also
 include the header file so that the compiler can check that the prototypes
 in the declaration and the definition match.

 e Every source file that calls the function should include the appropriate
 header (.h) file.

 e Optionally, a routine that calls a function can also include that function’s
 prototype declaration internally. This is often useful when you are
 developing a program, since it gives you a visible reminder (checked by
 the compiler through the common .nh file) of a function’s argument types.
 Later, after your program is debugged, you can go back and delete the
 supernumary internal declarations.

 For the routines in this book, the header file containing all the prototypes is nr.h,
 listed in Appendix A. You should put the statement #include nr.h at the top of
 every source file that contains Numerical Recipes routines. Since, more frequently
 than not, you will want to include more than one Numerical Recipes routine in a
 single source file, we have not printed this #include statement in front of this
 book’s individual program listings, but you should make sure that it is present in
 your programs.

 As backup, and in accordance with the last item on the indented list above,
 we declare the function prototype of all Numerical Recipes routines that are called
 by other Numerical Recipes routines internally to the calling routine. (That also
 makes our routines much more readable.) The only exception to this rule is that
 the small number of utility routines that we use repeatedly (described below) are
 declared in the additional header file nrutil.h, and the line #include nrutil.h
 is explicitly printed whenever it is needed.

 A final important point about the header file nr.h is that, as furnished on
 the diskette, it contains both ANSI C and traditional K&R-style declarations. The
 ANSI forms are invoked if any of the following macros are defined: __STDC__,
 ANSI, or NRANSI. (The purpose of the last name is to give you an invocation that
 does not conflict with other possible uses of the first two names.) If you have an
 ANSI compiler, it is essential that you invoke it with one or more of these macros

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 18 Chapter 1. Preliminaries

 defined. The typical means for doing so is to include a switch like “-DANSI” on
 the compiler command line.
 Some further details about the file nr.h are given in Appendix A.

 Vectors and One-Dimensional Arrays

 There is a close, and elegant, correspondence in C between pointers and arrays.
 The value referenced by an expression like a[j] is defined to be *((a)+(j)),
 that is, “the contents of the address obtained by incrementing the pointer a by
 j-’ A consequence of this definition is that if a points to a legal data location,
 the array element a[0] is always defined. Arrays in C are natively “zero-origin”
 or “zero-offset.’ An array declared by the statement float b[4]; has the valid
 references b[0], b[1], b[2], and b[3], but not b[4].

 Right away we need a notation to indicate what is the valid range of an array
 index. (The issue comes up about a thousand times in this book!) For the above
 example, the index range of b will be henceforth denoted b[0..3], a notation
 borrowed from Pascal. In general, the range of an array declared by float
 a[M]; is al0..M — 1], and the same if float is replaced by any other data type.

 One problem is that many algorithms naturally like to go from 1 to M, not
 from 0 to M — 1. Sure, you can always convert them, but they then often acquire
 a baggage of additional arithmetic in array indices that is, at best, distracting. It is
 better to use the power of the C language, in a consistent way, to make the problem
 disappear. Consider

 float b[4] ,*bb;
 bb=b-1;

 The pointer bb now points one location before b. An immediate consequence is that
 the array elements bb[1], bb[2], bb[3], and bb[4] all exist. In other words the
 range of bb is bb[1..4]. We will refer to bb as a unit-offset vector. (See Appendix
 B for some additional discussion of technical details.)

 It is sometimes convenient to use zero-offset vectors, and sometimes convenient
 to use unit-offset vectors in algorithms. The choice should be whichever is most
 natural to the problem at hand. For example, the coefficients of a polynomial
 ao + a,x + aga? +... + an2” clearly cry out for the zero-offset a0. .n], while
 a vector of V data points x;, i = 1... N calls for a unit-offset x[1..N]. When a
 routine in this book has an array as an argument, its header comment always gives
 the expected index range. For example,

 void someroutine(float bb[], int nn)
 This routine does something with the vector bb[1..nn].

 Now, suppose you want someroutine() to do its thing on your own vector,
 of length 7, say. If your vector, call it aa, is already unit-offset (has the valid range
 aa[1..7]), then you can invoke someroutine(aa,7) ; in the obvious way. That is
 the recommended procedure, since someroutine() presumably has some logical,
 or at least aesthetic, reason for wanting a unit-offset vector.

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.2 Some C Conventions for Scientific Computing 19

 But suppose that your vector of length 7, now call it a, is perversely a native C,
 zero-offset array (has range a[0. .6]). Perhaps this is the case because you disagree
 with our aesthetic prejudices, Heaven help you! To use our recipe, do you have to
 copy a’s contents element by element into another, unit-offset vector? No! Do you
 have to declare a new pointer aaa and set it equal to a-1? No! You simply invoke
 someroutine(a-1,7);. Then a[1], as seen from within our recipe, is actually
 a[0] as seen from your program. In other words, you can change conventions “on
 the fly” with just a couple of keystrokes.

 Forgive us for belaboring these points. We want to free you from the zero-offset
 thinking that C encourages but (as we see) does not require. A final liberating point
 is that the utility file nrutil.c, listed in full in Appendix B, includes functions
 for allocating (using malloc()) arbitrary-offset vectors of arbitrary lengths. The
 synopses of these functions are as follows:

 float *vector(long nl, long nh)
 Allocates a float vector with range [nl..nh].

 int *ivector(long nl, long nh)
 Allocates an int vector with range [nl..nh].

 unsigned char *cvector(long nl, long nh)
 Allocates an unsigned char vector with range [nl..nh].

 unsigned long *lvector(long nl, long nh)
 Allocates an unsigned long vector with range [nl..nh].

 double *dvector(long nl, long nh)
 Allocates a double vector with range [nl..nh].

 A typical use of the above utilities is the declaration float *b; followed by
 b=vector (1,7) ;, which makes the range b[1..7] come into existence and allows
 b to be passed to any function calling for a unit-offset vector.

 The file nrutil.c also contains the corresponding deallocation routines,

 void free_vector(float *v, long nl, long nh)
 void free_ivector(int *v, long nl, long nh)
 void free_cvector(unsigned char *v, long nl, long nh)
 void free_lvector(unsigned long *v, long nl, long nh)
 void free_dvector(double *v, long nl, long nh)

 with the typical use being free_vector(b,1,7);.

 Our recipes use the above utilities extensively for the allocation and deallocation
 of vector workspace. We also commend them to you for use in your main programs or
 other procedures. Note that if you want to allocate vectors of length longer than 64k
 on an IBM PC-compatible computer, you should replace all occurrences of malloc

 in nrutil.c by your compiler’s special-purpose memory allocation function. This
 applies also to matrix allocation, to be discussed next.

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 doa,

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 20 Chapter 1. Preliminaries

 Matrices and Two-Dimensional Arrays

 The zero- versus unit-offset issue arises here, too. Let us, however, defer it for
 a moment in favor of an even more fundamental matter, that of variable dimension
 arrays (FORTRAN terminology) or conformant arrays (Pascal terminology). These
 are arrays that need to be passed to a function along with real-time information
 about their two-dimensional size. The systems programmer rarely deals with two-
 dimensional arrays, and almost never deals with two-dimensional arrays whose size
 is variable and known only at run time. Such arrays are, however, the bread and
 butter of scientific computing. Imagine trying to live with a matrix inversion routine
 that could work with only one size of matrix!

 There is no technical reason that a C compiler could not allow a syntax like

 void someroutine(a,m,n)
 float alm] [n]; /* ILLEGAL DECLARATION */

 and emit code to evaluate the variable dimensions m and n (or any variable-dimension
 expression) each time someroutine() is entered. Alas! the above fragment is
 forbidden by the C language definition. The implementation of variable dimensions
 in C instead requires some additional finesse; however, we will see that one is
 rewarded for the effort.

 There is a subtle near-ambiguity in the C syntax for two-dimensional array
 references. Let us elucidate it, and then turn it to our advantage. Consider the
 array reference to a (say) float value ali] [j], where i and j are expressions
 that evaluate to type int. A C compiler will emit quite different machine code for
 this reference, depending on how the identifier a has been declared. If a has been
 declared as a fixed-size array,e.g., float a[5] [9] ;, then the machine code is: “to
 the address a add 9 times i, then add j, return the value thus addressed.” Notice that
 the constant 9 needs to be known in order to effect the calculation, and an integer
 multiplication is required (see Figure 1.2.1).

 Suppose, on the other hand, that a has been declared by float **a;. Then
 the machine code for a[i] [j] is: “to the address of a add i, take the value thus
 addressed as a new address, add j to it, return the value addressed by this new
 address.” Notice that the underlying size of a[] [] does not enter this calculation
 at all, and that there is no multiplication; an additional indirection replaces it. We
 thus have, in general, a faster and more versatile scheme than the previous one. The
 price that we pay is the storage requirement for one array of pointers (to the rows
 of a[] []), and the slight inconvenience of remembering to initialize those pointers
 when we declare an array.

 Here is our bottom line: We avoid the fixed-size two-dimensional arrays of C as
 being unsuitable data structures for representing matrices in scientific computing. We
 adopt instead the convention “pointer to array of pointers,” with the array elements
 pointing to the first element in the rows of each matrix. Figure 1.2.1 contrasts the
 rejected and adopted schemes.

 The following fragment shows how a fixed-size array a of size 13 by 9 is
 converted to a “pointer to array of pointers” reference aa:

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.2 Some C Conventions for Scientific Computing 21

 (a)

 *em eo 77

 (b)
 Figure 1.2.1. Two storage schemes for a matrix m. Dotted lines denote address reference, while solid

 lines connect sequential memory locations. (a) Pointer to a fixed size two-dimensional array. (b) Pointer
 to an array of pointers to rows; this is the scheme adopted in this book.

 float a[13] [9] ,**aa;

 int i;
 aa=(float **) malloc((unsigned) 13*sizeof(float*)) ;
 for (i=0;i<=12;it++) aalil=alil; ali] is a pointer to a[i] [0]

 The identifier aa is now a matrix with index range aa[0..12] [0..8]. You can use
 or modify its elements ad lib, and more importantly you can pass it as an argument
 to any function by its name aa. That function, which declares the corresponding
 dummy argument as float **aa;, can address its elements as aa[i] [j] without
 knowing its physical size.

 You may rightly not wish to clutter your programs with code like the above
 fragment. Also, there is still the outstanding problem of how to treat unit-offset
 indices, so that (for example) the above matrix aa could be addressed with the range
 a[1..13][1..9]. Both of these problems are solved by additional utility routines
 in nrutil.c (Appendix B) which allocate and deallocate matrices of arbitrary
 range. The synopses are

 float **matrix(long nrl, long nrh, long ncl, long nch)
 Allocates a float matrix with range [nrl..nrh] [ncl..nch].

 double **dmatrix(long nrl, long nrh, long ncl, long nch)
 Allocates a double matrix with range [nrl..nrh] [ncl..nch].

 int **imatrix(long nrl, long nrh, long ncl, long nch)
 Allocates an int matrix with range [nrl..nrh] [ncl..nch].

 void free_matrix(float **m, long nrl, long nrh, long ncl, long nch)
 Frees a matrix allocated with matrix.

 “(eoueWY YON apis}no) Bio abpuquieo@ Masjsno}9auIp 0} jee PUaS JO ‘(AJUO BOVEWY YON) EZ7Z-Z28-008- I I/29 40 Woo" U'MMy/:d}Y

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 doa,

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 22 Chapter 1. Preliminaries

 void free_dmatrix(double **m, long nrl, long nrh, long ncl, long nch)
 Frees a matrix allocated with dmatrix.

 void free_imatrix(int **m, long nrl, long nrh, long ncl, long nch)
 Frees a matrix allocated with imatrix.

 A typical use is

 float **a;
 a=matrix(1,13,1,9);

 a(3](S]=...
 ...+a[2] [9]/3.0...
 someroutine(a,...);

 free_matrix(a,1,13,1,9);

 All matrices in Numerical Recipes are handled with the above paradigm, and we
 commend it to you.

 Some further utilities for handling matrices are also included in nrutil.c.
 The first is a function submatrix() that sets up a new pointer reference to an
 already-existing matrix (or sub-block thereof), along with new offsets if desired.
 Its synopsis is

 float **submatrix(float **a, long oldrl, long oldrh, long oldcl,

 long oldch, long newrl, long newcl)
 Point a submatrix [newrl..newrl+(oldrh-oldr1)] [newcl. .newcl+(oldch-oldcl)] to
 the existing matrix range a[oldrl..oldrh] [oldcl..oldch].

 Here oldrl and oldrh are respectively the lower and upper row indices of the
 original matrix that are to be represented by the new matrix, oldcl and oldch are
 the corresponding column indices, and newrl and newcl are the lower row and
 column indices for the new matrix. (We don’t need upper row and column indices,
 since they are implied by the quantities already given.)

 Two sample uses might be, first, to select as a 2 x 2 submatrix b[1. .2]
 [1..2] some interior range of an existing matrix, say a[4..5] [2..3],

 float **a,**b;
 a=matrix(1,13,1,9);

 b=submatrix(a,4,5,2,3,1,1);

 and second, to map an existing matrix a[1..13][1..9] into a new matrix
 plO..12] [0..8],

 float **a,**b;
 a=matrix(1,13,1,9);

 b=submatrix(a,1,13,1,9,0,0);

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 doa,

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.2 Some C Conventions for Scientific Computing 23

 Incidentally, you can use submatrix() for matrices of any type whose sizeof ()
 is the same as sizeof (float) (often true for int, e.g.); just cast the first argument
 to type float ** and cast the result to the desired type,e.g., int **.

 The function

 void free_submatrix(float **b, long nrl, long nrh, long ncl, long nch)

 frees the array of row-pointers allocated by submatrix (). Note that it does not free
 the memory allocated to the data in the submatrix, since that space still lies within
 the memory allocation of some original matrix.

 Finally, if you have a standard C matrix declared as a[nrow] [ncol], and you
 want to convert it into a matrix declared in our pointer-to-row-of-pointers manner,
 the following function does the trick:

 float **convert_matrix(float *a, long nrl, long nrh, long ncl, long nch)
 Allocate a float matrix m[nrl..nrh] [ncl..nch] that points to the matrix declared in the
 standard C manner as a[nrow] [ncol] , where nrow=nrh-nrl+i1 and ncol=nch-ncl+i. The
 routine should be called with the address &a[0] [0] as the first argument.

 (You can use this function when you want to make use of C’s initializer syntax
 to set values for a matrix, but then be able to pass the matrix to programs in this
 book.) The function

 void free_convert_matrix(float **b, long nrl, long nrh, long ncl, long nch)
 Free a matrix allocated by convert_matrix().

 frees the allocation, without affecting the original matrix a.

 The only examples of allocating a three-dimensional array as a pointer-to-
 pointer-to-pointer structure in this book are found in the routines r1£t3 in §12.5 and
 sfroid in §17.4. The necessary allocation and deallocation functions are

 float ***f3tensor(long nrl, long nrh, long ncl, long nch, long ndl, long ndh)
 Allocate a float 3-dimensional array with subscript range [nrl. .nrh] [ncl..nch] [ndl. .ndh] .

 void free_f3tensor(float ***t, long nrl, long nrh, long ncl, long nch,
 long ndl, long ndh)
 Free a float 3-dimensional array allocated by f3tensor().

 Complex Arithmetic

 C does not have complex data types, or predefined arithmetic operations on
 complex numbers. That omission is easily remedied with the set of functions in
 the file complex.c which is printed in full in Appendix C at the back of the book.
 A synopsis is as follows:

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 doa,

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 24 Chapter 1. Preliminaries

 typedef struct FCOMPLEX {float r,i;} fcomplex;

 fcomplex Cadd(fcomplex a, fcomplex b)
 Returns the complex sum of two complex numbers.

 fcomplex Csub(fcomplex a, fcomplex b)
 Returns the complex difference of two complex numbers.

 fcomplex Cmul(fcomplex a, fcomplex b)
 Returns the complex product of two complex numbers.

 fcomplex Cdiv(fcomplex a, fcomplex b)
 Returns the complex quotient of two complex numbers.

 fcomplex Csqrt(fcomplex z)
 Returns the complex square root of a complex number.

 fcomplex Conjg(fcomplex z)
 Returns the complex conjugate of a complex number.

 float Cabs(fcomplex z)
 Returns the absolute value (modulus) of a complex number.

 fcomplex Complex(float re, float im)
 Returns a complex number with specified real and imaginary parts.

 fcomplex RCmul(float x, fcomplex a)
 Returns the complex product of a real number and a complex number.

 The implementation of several of these complex operations in floating-point
 arithmetic is not entirely trivial; see §5.4.

 Only about half a dozen routines in this book make explicit use of these complex
 arithmetic functions. The resulting code is not as readable as one would like, because
 the familiar operations +-*/ are replaced by function calls. The C++ extension to
 the C language allows operators to be redefined. That would allow more readable
 code. However, in this book we are committed to standard C.

 We should mention that the above functions assume the ability to pass, return,
 and assign structures like FCOMPLEX (or types such as fcomplex that are defined
 to be structures) by value. All recent C compilers have this ability, but it is not in
 the original K&R C definition. If you are missing it, you will have to rewrite the
 functions in complex.c, making them pass and return pointers to variables of type
 fcomplex instead of the variables themselves. Likewise, you will need to modify
 the recipes that use the functions.

 Several other routines (e.g., the Fourier transforms four1 and fourn) do
 complex arithmetic “by hand,” that is, they carry around real and imaginary parts as
 float variables. This results in more efficient code than would be obtained by using
 the functions in complex .c. But the code is even less readable. There is simply no
 ideal solution to the complex arithmetic problem in C.

 Implicit Conversion of Float to Double

 In traditional (K&R) C, float variables are automatically converted to double
 before any operation is attempted, including both arithmetic operations and passing
 as arguments to functions. All arithmetic is then done in double precision. If a
 float variable receives the result of such an arithmetic operation, the high precision

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 Buipnjoul) say ajqepeos

 yew Jo BulAdoo Aue Jo ‘uononpoidas sayyin4 “asn yeuossed UMO 4194} 10} Adoo seded auo eyeW 0} SuasN yeUsE}U! 10} PayUeJG SI UOISSIWAg

 JOM USIA ‘SAIOHGD 40 Sy00g sadioay jeOOWNN Japs OJ “payiqiyoud Ajjoujs Ss! ‘’a}ndwod JaAsas Aue 0} (BU SII

 “aremyog sedivay jeouawinn Aq 2661-8861 (9) 1UBUIAdoD suIesBolg ‘ssalq Ayan eBpUquIeD kq Z661-86L (9) 1U

 doa,

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 1.2 Some C Conventions for Scientific Computing 25

 is immediately thrown away. A corollary of these rules is that all the real-number
 standard C library functions are of type double and compute to double precision.

 The justification for these conversion rules is, “well, there’s nothing wrong with
 a little extra precision,” and “this way the libraries need only one version of each
 function.” One does not need much experience in scientific computing to recognize
 that the implicit conversion rules are, in fact, sheer madness! In effect, they make it
 impossible to write efficient numerical programs. One of the cultural barriers that
 separates computer scientists from “regular” scientists and engineers is a differing
 point of view on whether a 30% or 50% loss of speed is worth worrying about. In
 many real-time or state-of-the-art scientific applications, such a loss is catastrophic.
 The practical scientist is trying to solve tomorrow’s problem with yesterday’s
 computer; the computer scientist, we think, often has it the other way around.

 The ANSI C standard happily does not allow implicit conversion for arithmetic
 operations, but it does require it for function arguments, unless the function is fully
 prototyped by an ANSI declaration as described earlier in this section. That is
 another reason for our being rigorous about using the ANSI prototype mechanism,
 and a good reason for you to use an ANSI-compatible compiler.

 Some older C compilers do provide an optional compilation mode in which
 the implicit conversion of float to double is suppressed. Use this if you can.
 In this book, when we write float, we mean float; when we write double,
 we mean double, i.e., there is a good algorithmic reason for having higher
 precision. Our routines all can tolerate the traditional implicit conversion rules,
 but they are more efficient without them. Of course, if your application actually
 requires double precision, you can change our declarations from float to double
 without difficulty. (The brute force approach is to add a preprocessor statement
 #define float double !)

 A Few Wrinkles

 We like to keep code compact, avoiding unnecessary spaces unless they add
 immediate clarity. We usually don’t put space around the assignment operator “=”.
 Through a quirk of history, however, some C compilers recognize the (nonexistent)
 operator “‘=-” as being equivalent to the subtractive assignment operator “-=”, and
 “=«” as being the same as the multiplicative assignment operator “*=”. That is why
 you will see us write y= -10.0; or y=(-10.0);, and y= *a; or y=(*a) ;.

 We have the same viewpoint regarding unnecessary parentheses. You can’t write
 (or read) C effectively unless you memorize its operator precedence and associativity
 tules. Please study the accompanying table while you brush your teeth every night.

 We never use the register storage class specifier. Good optimizing compilers
 are quite sophisticated in making their own decisions about what to keep in registers,
 and the best choices are sometimes rather counter-intuitive.

 Different compilers use different methods of distinguishing between defining
 and referencing declarations of the same external name in several files. We follow
 the most common scheme, which is also the ANSI standard. The storage class
 extern is explicitly included on all referencing top-level declarations. The storage
 class is omitted from the single defining declaration for each external variable. We
 have commented these declarations, so that if your compiler uses a different scheme
 you can change the code. The various schemes are discussed in §4.8 of [1].

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 ov
 So
 33
 gg
 ae
 =o
 32.
 8a
 3a
 aa
 so
 es
 az
 oe
 $3
 22
 osc
 OG
 as
 26
 <*
 oe
 Ae
 gx
 38
 oo
 35
 23
 eB
 go
 a0
 a
 28
 23
 a2
 <3
 Ue
 oz
 $3
 Pe
 fa
 as
 3
 ae
 28
 s
 SB
 25
 co
 §5
 an
 ga
 ok
 g8F
 3
 a5
 23
 3g
 3s
 oe
 gs
 o
 a2
 gg
 2
 ss
 2
 Do
 Oo
 ae
 2s
 <a
 Bo
 =3
 3B
 $8
 25
 eo
 °3

 le)
 o
 3
 ss
 é

 “alemyos Sedioay JeouewWNN Aq 2661-886 (O) 1UBUAdOD suresBOlg “ssald AysienluN eGpuquied Aq Z661-8861 (O

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

 26 Chapter 1. Preliminaries

 Operator Precedence and Associativity Rules in C

 oO function call left-to-right
 0 array element
 structure or union member
 > pointer reference to structure
 ! logical not right-to-left
 ~ bitwise complement
 - unary minus
 ++ increment
 -- decrement
 & address of
 * contents of
 (type) cast to type
 sizeof size in bytes
 * multiply left-to-right
 / divide
 h remainder
 + add left-to-right
 - subtract
 << bitwise left shift left-to-right
 >> bitwise right shift
 < arithmetic less than left-to-right
 > arithmetic greater than
 <= arithmetic less than or equal to
 >= arithmetic greater than or equal to
 == arithmetic equal left-to-right

 f= arithmetic not equal

 & bitwise and left-to-right

 - bitwise exclusive or left-to-right

 | bitwise or left-to-right

 && logical and left-to-right

 I logical or left-to-right

 Po: conditional expression right-to-left

 = ignment operator right-to-left
 also += -= *= /= Y=
 <<= >>= &= 7= |=

 , sequential expression left-to-right

 We have already alluded to the problem of computing small integer powers of
 numbers, most notably the square and cube. The omission of this operation from C
 is perhaps the language’s most galling insult to the scientific programmer. All good
 FORTRAN compilers recognize expressions like (A+B) **4 and produce in-line code,
 in this case with only one add and two multiplies. It is typical for constant integer
 powers up to 12 to be thus recognized.

 *(eoveWY YON episyno) Bio‘eBpuquied® Mesisnojoauip 0} |eWe Pues JO ‘(AJUO BOLEWY YUON) EzbPZ-ZZ8-008-| [129 JO WOo'U'MMy/:cY

 OUSGOM IISIA ‘SWWOHGD JO Sy00q sedioay jeoaWINN Japso OY “payiqiyoud Ajyouys si ‘“a;Nndwios JaAsas Aue 0} (aUO siy} Bulpnjoul) s
 -eulyoew jo BulAdoo Aue Jo ‘uononpoides seyin4 “asn yeuossed UMO 4194} 10} Adoo Jaded auo eyeW 0} suasn jeUsa}U! 40} payUeJB Ss}

 “aleMYyOs sedioay JeouewWNnN Aq 2661-8861 (O) 1UBUAdoD suresBOIg “Ssalg AysienluN eGpuquied Aq 2661-8861 (O) 1BUAdOD

 ($-80L€b-L2S-0 NASI) DNILAAWOD SISILNSIOS SO LYW SHL:O NI SAdIOSY TVOINSWNN Woy ebed ejdwes

-/

-- TODO: parse the OCR text into Lean definitions
