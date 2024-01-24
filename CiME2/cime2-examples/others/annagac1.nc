%***************************************************************************
%
%
% Comple'tion modulo AG et AC1 des anneaux commutatifs
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        annagac1.nc
% Created on:              04 mai 93
% Last modified on: 04 mai 93
%
%***************************************************************************

operators
  +,. : AC
  0,1 : constant
  -   : 1
  x,y,z,t,u : variable

theory  AG(+,0,-) ACU(.,1)

axioms
  x.(y+z) = (x.y)+(x.z);

order  
  rpo( 1>.>->+>0 ; + mul, . mul )
  % interactive

end

