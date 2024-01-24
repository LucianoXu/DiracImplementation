%***************************************************************************
%
%
% Comple'tion modulo AC1 des anneaux commutatifs
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        ann-ac1.nc
% Created on:              08 mar 93
% Last modified on: 06 dec 93
%
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z : variable

theory  ACU(+,0) ACU(.,1)

axioms
  x+-(x)  = 0;
  x.(y+z) = (x.y)+(x.z);

order  rpo( .>->0>+ ; + mul, . mul )


end

