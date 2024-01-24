%***************************************************************************
%
%
% Pb d'Helene Kirchner et de Trouve
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        helene.nc
% Created on:              12 jul 93
% Last modified on: 12 jul 93
%
%***************************************************************************

operators
  . : infix binary
  1,a,b : constant
  x,y,z : variable
  + : AC

theory
  AU(.,1)

axioms

% c'est trivialement complet si l'on ajoute les distributivites
%  x.(y+z) = (x.y)+(x.z);
%  (x+y).z = (x.z)+(y.z);
  x.(a.(b.y)) = (x.(a.y)) + (x.(b.y));

order
  rpo( .>+ ; . lrlex )
% interactive

end

