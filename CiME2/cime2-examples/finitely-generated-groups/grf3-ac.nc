%***************************************************************************
%
%
% Comple'tion modulo AC du groupe finiment engendre' par
%
%    2a-3b+c   = 0
%    -3a+2b+3c = 0 
%    2a+2b-2c  = 0
%
% File name:        $Source: /users/demons/demons/master-sources-repository/cime/examples/finitely-generated-groups/grf3-ac.nc,v $
% Revision:         $Revision: 1.3 $ 
% Last modified by: $Author: contejea $
% Last modified on: $Date: 1997/05/16 07:57:04 $
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable
  a,b,c : constant

axioms
  x+0 = x;
  x+-(x) = 0;
  a+a+-(b+b+b)+c = 0;
  -(a+a+a)+b+b+c+c+c = 0;
  a+a+b+b+-(c+c) = 0;

order  rpo( c>b>a>- >0>+ ; + mul )

end

