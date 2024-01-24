%***************************************************************************
%
%
% Calcul de la base standard de l'ideal
%
%
% Project:                Cime
% Author(s):             Claude March\'e, Evelyne contejean
%
% File name:        base-standard-1.nc
% Created on:              10 mar 93
% Last modified on: 10 mar 93
%
%***************************************************************************

operators
  +,* : AC
  0,1 : constant
  -   : unary
  X1,X2,Y1,Y2,Y3 : constant
  x,y,z : variable

theory  CR(+,0,-,*,1)
unification theory AG(+,0,-) ACU(*,1)

axioms
 (X2*X2) + -(Y1*X1) = 0;
 (X1*X1*X1*X2) + - (Y2) = 0;
 1 + -(Y3*X1*X2) = 0;

order  interactive

end

