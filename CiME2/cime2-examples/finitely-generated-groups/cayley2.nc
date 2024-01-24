%***************************************************************************
%
%
% Problemes sur les graphes de Cayley
% numero 2
%  (le groupe de tetraedre : ordre 12, la base de
%  decomposition consideree est de longueur 2)
%
% Project:                Cime
% Author(s):             Pauline Strogova, Claude March\'e
%
% File name:        cayley2.nc
% Created on:              25 nov 93
% Last modified on: 25 nov 93
%
%***************************************************************************

operators
   . : infix binary
   e : constant
   i : unary
   g1, g2 : constant
   c1_1, c1_2, c1_3, c1_4 : constant
   g2_1 : constant
   c2_2, c2_3, c2_4 : constant

theory G(.,e,i)

axioms
c1_1 = e;
c1_2 = c1_1 . i(g1);
c1_3 = c1_1 . i(g2);
c1_4 = c1_1 . g1;
g2_1 = c1_3 . (g1 . i(c1_3));
c2_2 = e;
c2_3 = c2_2 . i(g2_1);
c2_4 = c2_2 . g2_1;
i(c2_3) = c1_1 . (g2 . i(c1_4));
i(c2_4) = c1_2 . (g2 . i(c1_2));
i(c2_3) = c1_3 . (g1 . i(c1_3));
i(c2_4) = c1_4 . (g2 . i(c1_3));


order
  lexico (rpo (
  i > . > g1 > e,
  i > . > g2 > e,
  c1_1 > i > e,
  c1_2 > c1_1 > i, 
  c1_3 > c1_1 > i, 
  c1_4 > c1_1 > i, 
  g2_1 > c1_1,
  g2_1 > c1_2,
  g2_1 > c1_3,
  g2_1 > c1_4,
  c2_2 > g1 > e,
  c2_3 > c2_2 > g2_1,
  c2_4 > c2_2 > g2_1,
  g1 = g2;
  . lrlex );
  rpo ( . > g2 > g1 > e; . lrlex))

end

