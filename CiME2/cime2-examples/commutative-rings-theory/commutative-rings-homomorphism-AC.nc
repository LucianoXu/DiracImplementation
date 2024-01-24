%***************************************************************************
%
% Comple'tion modulo CR de la th\'eorie d'un morphisme d'anneaux
% commutatifs
%
% $Id: commutative-rings-homomorphism-AC.nc,v 1.5 1997/07/11 12:43:06 demons Exp $
%
%***************************************************************************

operators
  +,.,&,*      : AC
  0,1,zero,one : constant
  -,I,H        : unary
  x,y,z,t,u    : variable

axioms 
  x+0 = x;
  x+-(x) = 0;
  x.1 = x;
  x.(y+z) = (x.y)+(x.z);

  x&zero = x;
  x&I(x) = zero;
  x*one = x;
  x*(y&z) = (x*y)&(x*z);

  H(x+y) = H(x) & H(y); 
  H(x.y) = H(x) * H(y);  
  
order  rpo( H>1>.>- >+>0, H>one>*>I>&>zero  )

% conjectures

%   H(0) = zero ;

end

New rule produced :  [1] x+0 -> x
New rule produced :  [2] x.1 -> x
New rule produced :  [3] x & zero -> x
New rule produced :  [4] x*one -> x
New rule produced :  [5] x+-(x) -> 0
New rule produced :  [6] x & I(x) -> zero
New rule produced :  [7] -(0) -> 0
New rule produced :  [8] -(-(x)) -> x
New rule produced :  [9] I(zero) -> zero
New rule produced :  [10] I(I(x)) -> x
New rule produced :  [11] x+-(x+y) -> -(y)
New rule produced :  [12] x & I(x & y) -> I(y)
New rule produced :  [13] H(x+y) -> H(x) & H(y)
New rule produced :  [14] H(x.y) -> H(x)*H(y)
New rule produced :  [15] -(x+y) -> -(x)+-(y)
Rule [11] x+-(x+y) -> -(y) collapsed.
New rule produced :  [16] I(x & y) -> I(x) & I(y)
Rule [12] x & I(x & y) -> I(y) collapsed.
New rule produced :  [17] H(x) & H(0) -> H(x)
New rule produced :  [18] H(x)*H(1) -> H(x)
New rule produced :  [19] H(0) -> zero
Rule [17] H(x) & H(0) -> H(x) collapsed.
All conjectures have been proved !

Number of calls to AC matching      : 11111
Number of successful calls          : 1073 (9%)
Number of calls to unification      : 89
Number of unifiers generated        : 514 (5.78 average)
Number of critical pairs considered : 308 (59%)
Number of rules produced            : 19
Number of rules retained            : 16

      times       |   user   |  system  |  total 
------------------+----------+----------+----------
Total times       |   11.380 |    4.280 |   15.660 
Unification times |    1.400 |    0.010 |    1.410 
Matching times    |    6.890 |    2.100 |    8.990 
Poly times        |    0.000 |    0.000 |    0.000 

Should I (s)top or (c)ontinue ? c
New rule produced :  [20] zero*H(1) -> zero
New rule produced :  [21] H(x) & H(-(x)) -> zero
New rule produced :  [22] H(-(x)) -> I(H(x))
Rule [21] H(x) & H(-(x)) -> zero collapsed.
New rule produced :  [23] I(H(x))*H(1) -> I(H(x))
New rule produced :  [24] x.(y+z) -> (x.y)+(x.z)
New rule produced :  [25] x*(y & z) -> (x*y) & (x*z)
New rule produced :  [26] (x.y)+(x.0) -> x.y
New rule produced :  [27] (x*y) & (x*zero) -> x*y
New rule produced :  [28] x+(x.0) -> x
New rule produced :  [29] x.0 -> 0
Rule [28] x+(x.0) -> x collapsed.
Rule [26] (x.y)+(x.0) -> x.y collapsed.
New rule produced :  [30] x & (x*zero) -> x
New rule produced :  [31] x*zero -> zero
Rule [30] x & (x*zero) -> x collapsed.
Rule [27] (x*y) & (x*zero) -> x*y collapsed.
Rule [20] zero*H(1) -> zero collapsed.
New rule produced :  [32] (x.y)+(x.-(y)) -> 0
New rule produced :  [33] (x*y) & (x*I(y)) -> zero
New rule produced :  [34] x+(x.-(1)) -> 0
New rule produced :  [35] x.-(y) -> -(x.y)
Rule [34] x+(x.-(1)) -> 0 collapsed.
Rule [32] (x.y)+(x.-(y)) -> 0 collapsed.
New rule produced :  [36] x & (x*I(one)) -> zero
New rule produced :  [37] x*I(y) -> I(x*y)
Rule [36] x & (x*I(one)) -> zero collapsed.
Rule [33] (x*y) & (x*I(y)) -> zero collapsed.
Rule [23] I(H(x))*H(1) -> I(H(x)) collapsed.

Result:
{ [1] x+0 -> x,
  [2] x.1 -> x,
  [3] x & zero -> x,
  [4] x*one -> x,
  [5] x+-(x) -> 0,
  [6] x & I(x) -> zero,
  [7] -(0) -> 0,
  [8] -(-(x)) -> x,
  [9] I(zero) -> zero,
  [10] I(I(x)) -> x,
  [13] H(x+y) -> H(x) & H(y),
  [14] H(x.y) -> H(x)*H(y),
  [15] -(x+y) -> -(x)+-(y),
  [16] I(x & y) -> I(x) & I(y),
  [18] H(x)*H(1) -> H(x),
  [19] H(0) -> zero,
  [22] H(-(x)) -> I(H(x)),
  [24] x.(y+z) -> (x.y)+(x.z),
  [25] x*(y & z) -> (x*y) & (x*z),
  [29] x.0 -> 0,
  [31] x*zero -> zero,
  [35] x.-(y) -> -(x.y),
  [37] x*I(y) -> I(x*y) } (23 rules)

Number of calls to AC matching      : 22370
Number of successful calls          : 1749 (7%)
Number of calls to unification      : 232
Number of unifiers generated        : 781 (3.37 average)
Number of critical pairs considered : 471 (60%)
Number of rules produced            : 37
Number of rules retained            : 23

      times       |   user   |  system  |  total 
------------------+----------+----------+----------
Total times       |   23.990 |   10.670 |   34.660 
Unification times |    1.960 |    0.010 |    1.970 
Matching times    |   14.080 |    5.350 |   19.430 
Poly times        |    0.000 |    0.000 |    0.000 

