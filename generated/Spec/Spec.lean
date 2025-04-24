/-
 ```
 Numerical Recipes in C
 The Art of Scientific Computing
 Second Edition

 William H. Press
 Harvard-Smithsonian Center for Astrophysics

 Saul A. Teukolsky
 Department of Physics, Cornell University

 William T. Vetterling
 Polaroid Corporation

 Brian P. Flannery
 EXXON Research and Engineering Company

 CAMBRIDGE UNIVERSITY PRESS
 Cambridge New York Port Chester Melbourne Sydney
 ```
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

-/

-- TODO: parse the OCR text into Lean definitions
