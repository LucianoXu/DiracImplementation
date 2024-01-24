%***************************************************************************
%
%
% Problemes sur les graphes de Cayley
% numero 1 version avec comparaison des longueurs
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        cayley1.nc
% Created on:              10 nov 93
% Last modified on: 10 nov 93
%
%***************************************************************************

operators
   . : infix binary
   e : constant
   i : unary
   g1, g2 : constant
   c1_16, c1_15, c1_14, c1_13,
   c1_12, c1_11, c1_10, c1_9,
   c1_8, c1_7, c1_6, c1_5,
   c1_4, c1_3, c1_2, c1_1 : constant

theory G(.,e,i) 

axioms
c1_1 = e;
c1_2 = c1_1 . g2;
c1_3 = c1_2 . g2;
c1_4 = c1_1 . i(g2);
c1_5 = c1_1 . g1;
c1_6 = c1_5 . g2;
c1_7 = c1_6 . g2;
c1_8 = c1_5 . i(g2);
c1_9 = c1_5 . g1;
c1_10 = c1_9 . g2;
c1_11 = c1_10 . g2;
c1_12 = c1_9 . i(g2);
c1_13 = c1_1 . i(g1);
c1_14 = c1_2 . i(g1);
c1_15 = c1_3 . i(g1);
c1_16 = c1_13 . i(g2);
c1_1 = c1_8 . g1 . i(c1_12);
c1_1 = c1_4 . g1 . i(c1_8);
c1_1 = c1_16 . g1 . i(c1_4);
c1_1 = c1_12 . g1 . i(c1_16);
c1_1 = c1_9 . g1 . i(c1_13);
c1_1 = c1_6 . g1 . i(c1_10);
c1_1 = c1_2 . g1 . i(c1_6);
c1_1 = c1_10 . g1 . i(c1_14);
c1_1 = c1_7 . g1 . i(c1_11);
c1_1 = c1_3 . g1 . i(c1_7);
c1_1 = c1_11 . g1 . i(c1_15);
c1_1 = c1_11 . g2 . i(c1_12);
c1_1 = c1_7 . g2 . i(c1_8);
c1_1 = c1_3 . g2 . i(c1_4);
c1_1 = c1_13 . g2 . i(c1_14);
c1_1 = c1_14 . g2 . i(c1_15);
c1_1 = c1_15 . g2 . i(c1_16);


order  
  lexico(
  rpo(
  i > . > g1 > e,
  i > . > g2 > e,
  c1_1 > i > e,
  c1_2 > c1_1 > i,
  c1_3 > c1_2 > i,
  c1_4 > c1_1 > i,
  c1_5 > c1_1 > i,
  c1_6 > c1_5 > i,
  c1_7 > c1_6 > i,
  c1_8 > c1_5 > i,
  c1_9 > c1_5 > i,
  c1_10 > c1_9 > i,
  c1_11 > c1_10 > i,
  c1_12 > c1_9 > i,
  c1_13 > c1_1 > i,
  c1_14 > c1_2 > i,
  c1_15 > c1_3 > i,
  c1_16 > c1_13 > i,
% ajoute par moi pour preciser l'ordre
  g2 = g1
  ;
  . lrlex
  ) ;
  rpo ( .>g2 > g1>e ; . lrlex )
%  interactive
)

end

