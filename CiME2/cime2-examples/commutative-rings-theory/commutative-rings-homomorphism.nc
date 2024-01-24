%***************************************************************************
%
%
% Comple'tion modulo CR de la th\'eorie d'un morphisme d'anneaux
% commutatifs
%
%
% $Id: commutative-rings-homomorphism.nc,v 1.4 1997/07/11 12:43:07 demons Exp $
%
%***************************************************************************

operators
  +,.,&,*      : AC
  0,1,zero,one : constant
  -,I,H        : unary
  x,y,z,t,u    : variable

theory  CR(+,0,-,.,1)  CR(&,zero,I,*,one)

axioms 

  H(x+y) = H(x) & H(y); 
  H(x.y) = H(x) * H(y);  

order  rpo( H>1>.>- >+>0, H>one>*>I>&>zero  )

% conjectures
%   H(0) = zero ;

end

New rule produced :  [1] H(0) -> zero
All conjectures have been proved !

Number of calls to AC matching      : 501
Number of successful calls          : 35 (6%)
Number of calls to unification      : 2
Number of unifiers generated        : 20 (10.00 average)
Number of critical pairs considered : 0 (0%)
Number of rules produced            : 1
Number of rules retained            : 1

      times       |   user   |  system  |  total 
------------------+----------+----------+----------
Total times       |    0.820 |    0.680 |    1.500 
Unification times |    0.030 |    0.010 |    0.040 
Matching times    |    0.400 |    0.130 |    0.530 
Poly times        |    0.000 |    0.000 |    0.000 

Should I (s)top or (c)ontinue ? c
New rule produced :  [2] H(-(x)) -> I(H(x))
New rule produced :  [3] H(x+y) -> H(x) & H(y)
New rule produced :  [4] H(x.y) -> H(x)*H(y)
New rule produced :  [5] H(x)*H(1) -> H(x)

Result:
{ [1] H(0) -> zero,
  [2] H(-(x)) -> I(H(x)),
  [3] H(x+y) -> H(x) & H(y),
  [4] H(x.y) -> H(x)*H(y),
  [5] H(x)*H(1) -> H(x) } (5 rules)

Number of calls to AC matching      : 2071
Number of successful calls          : 107 (5%)
Number of calls to unification      : 23
Number of unifiers generated        : 44 (1.91 average)
Number of critical pairs considered : 24 (54%)
Number of rules produced            : 5
Number of rules retained            : 5

      times       |   user   |  system  |  total 
------------------+----------+----------+----------
Total times       |    2.240 |    1.650 |    3.890 
Unification times |    0.060 |    0.010 |    0.070 
Matching times    |    1.110 |    0.640 |    1.750 
Poly times        |    0.000 |    0.000 |    0.000 

