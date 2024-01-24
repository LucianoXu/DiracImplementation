%***************************************************************************
%
% Chameleons problem
%
% Project:    Cime
% Author(s):  Claude Marché
% Created on: 08 mar 93
%
% Last modified by $Author: marche $ 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/others/chameleons-problem.nc,v $
% $Revision: 1.4 $ 
% Last modified on $Date: 1997/07/01 16:15:14 $
% 
%***************************************************************************

operators
  & : AC
  Red,Green,Blue : constant

axioms
  Red & Blue = Green & Green;
  Red & Green = Blue & Blue;
  Green & Blue = Red & Red;

order 
  rpo(Red>Blue>Green > & ; & mul)

problems
  Red & Red & Red & Red & Blue & Blue & Blue & Green & Green =
  Red & Red & Red & Red & Red & Red & Red & Red & Red;
  Red & Red & Red & Red & Blue & Blue & Blue & Green & Green =
  Blue & Blue & Blue & Blue & Blue & Blue & Blue & Blue & Blue;
  Red & Red & Red & Red & Blue & Blue & Blue & Green & Green =
  Green & Green & Green & Green & Green & Green & Green & Green & Green;

end

Result:
{ [1] Red & Blue -> Green & Green,
  [2] Red & Green -> Blue & Blue,
  [3] Red & Red -> Green & Blue,
  [4] Blue & Blue & Blue -> Green & Green & Green } (4 rules)

Number of calls to AC matching      : 414
Number of successful calls          : 11 (2%)
Number of calls to unification      : 36
Number of unifiers generated        : 20 (0.56 average)
Number of critical pairs considered : 16 (80%)
Number of rules produced            : 4
Number of rules retained            : 4

      times       |   user   |  system  |  total 
------------------+----------+----------+----------
Total times       |    0.380 |    0.420 |    0.800 
Unification times |    0.050 |    0.020 |    0.070 
Matching times    |    0.130 |    0.040 |    0.170 
Poly times        |    0.000 |    0.000 |    0.000 

