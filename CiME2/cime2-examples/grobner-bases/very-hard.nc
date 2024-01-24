%***************************************************************************
%
%
% Comple'tion modulo CR de l'exemple de Siva
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        grobnerd.nc
% Created on:              05 mai 93
% Last modified on: 05 mai 93
%
%***************************************************************************

operators
  +,* : AC
  0,1,2,3,4 : constant
  -   : unary
  try12,try11,try10,try9,try8,try7,try6,try5,try4,try3,try2,try1 : constant
  c8,c7,c6,c0 : constant
  g8,g7,g6,g5,g4,g3,g2,g1,g0 : constant
  T,X,S,U,W,F,G,K,L,M,P,A,B,C : constant
  x,y,z : variable
  ^ : infix binary
  
theory  CR(+,0,-,*,1)

axioms
  x^2 = x*x;
  x^3 = x*x*x;
  x^4 = x*x*x*x;
  2*x = x+x;

A*C+B+-(B^2) = 0;

g0 =   ((L*A)*(L*B)*((L*C) + M +(L*B*M))) +
       ((L*A)*((L*C)+M)*((L*B) + (A*L*M))) +
       (L*((2*L*(B^2)) + (A*L*B*M))) + 
       -(1) ;

g1 =    (L^4) * (A^3);

g2 =    (L^3)*A*B*(B + (A*M)) ;

g3 =    (L^4)*A*(B^2) ;

g4 =    2*(L^4)*(A^2)*B ;

g5 =    ((L^3)*(A^3)*M) + 
        ((L^3)*(A^2)*B) + 
        ((L^4)*(A^2)*B) ;

g6 =    M + 
        (L*( (B*((L*C)+M)) + 
             (B*((L*C)+M+(L*B*M))) + 
             C + 
             (A*((L*C)+M)*((L*C)+M+(L*B*M))))) ;

g7 =    ((L^2)*(A^2))*((L*C)+M+(L*B*M)) + 
        ((L^3)*A*B*(B+(A*M))) +
        ((L^2)*A*(L*A)*((L*C)+M)) + 
        ((L^2)*A*B) + 
        ((L^3)*A*B) + 
        ((L^4)*A*(B^2)) ;

g8 =    ((L*A)*(L*B)*((L*B*M)+(L*C)+M)) + 
        ((L*A)*((L*C)+M)*(B*(L^2))) +
        ((B^2)*(L^2)) + 
        ((B^2)*(L^3)) ;

c0 = g0+(g2*S)+(g4*T)+(g1*S*T) ;
c6 = g6+(g1*(T^2))+((g2+g3)*T) ;
c7 = g7+((g4+g5)*S)+(g1*(S^2)) ;
c8 = g8+(g3*S)+(g5*T)+(g1*S*T) ;

try1 = (((L^2)+-(L))*S) + (2*L*M) ;
try2 = ((L^2)+-(1))*T + ((M^2)+-(S*M)) ;
try3 = ((A^2)*(S^2)+-(A*S)) + 4*A*B*S + 2*(B^2) + 2*A*C ;
try4 = ((B^2)+-(B))*S + (A^2)*S*T + 2*B*C + 2*A*B*T ;
try5 = ((C^2)+-(C*S)) + (A^2)*(T^2) + (2*(B^2)+-(1))*T ;
try6 = (X^2) + -(S*X) + -(T) ;

try7 = c6+-(W*F) ;
try8 = c0+-(W*G) ;
try9 = c8+-(K*F) ;
try10 = c7+-(K*G) ;

try11 = (F*W) + (T*(K^2)) + -(P*F) ;
try12 = (S*(K^2)) + (K*(F+W)) + -(P*G) ;

%polset

try1 = 0; try2 = 0; try3 = 0; try4 = 0; try5 = 0; try6 = 0;
try7 = 0; try8 = 0; try9 = 0; try10 = 0; try11 = 0; try12 = 0;
F + (G*X) + -(U) = 0; P*U = 0;
(F*(1+-(L))) + (G*M) + -(U*(1+-(L))) = 0;
((F*(1+-(2*B)+-(A*S)))+(G*C)+(G*A*T)) + U*((A*S)+(2*B)+-(1)) = 0;

order  rpo(

try12>try11>try10>try9>try8>try7>try6>try5>try4>try3>try2>try1>
c8>c7>c6>c0>
g8>g7>g6>g5>g4>g3>g2>g1>g0>
T>X>S>U>W>F>G>K>L>M>P>A>B>C>^>2>1>*>- >+>0 

)

end

