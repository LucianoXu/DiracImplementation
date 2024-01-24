%***************************************************************************
%
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        bsf5.nc
% Created on:              15 jul 93
% Last modified on: 15 jul 93
%
%***************************************************************************

operators
  +,* : AC
  0,1 : constant
  -   : unary
  a,b : constant
  x,y,z : variable

theory  CR(+,0,-,*,1)

axioms
%  x+0 = x ;
%  x*1 = x ;
%  x*(y+z) = (x*y)+(x*z) ;
%  x*0 = 0 ;
%  -(x) = x+x+x+x ;
  x+x+x+x+x = 0 ;

  a+a+a = b;
  
order rpo( a>b>1>*>->+>0 ; + mul, * mul)

problems 
  a = b+b;
end

