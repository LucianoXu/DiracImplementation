%***************************************************************************
%
%
% Problemes sur les graphes de Cayley
% numero 3
%  (groupe PSL3 d'ordre 5616 ; nous considerons une chaine stabilisatrice
%  de longueur 5)
%
% Project:                Cime
% Author(s):             Pauline Strogova, Claude March\'e
%
% File name:        cayley3.nc
% Created on:              25 nov 93
% Last modified on: 26 nov 93
%
%***************************************************************************


operators
   . : infix binary
   e : constant
   i : unary
   g1, g2 : constant
   g1_1, g1_2, g1_3, g1_4 : constant
   c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, c1_10, c1_11, c1_12, c1_13 : constant
   g2_1, g2_2, g2_3, g2_4 : constant
   c2_1, c2_2, c2_3, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, c2_11, c2_12, c2_13 : constant
   g3_1, g3_2, g3_3 : constant
   c3_6, c3_13 : constant
   g4_1, g4_2, g4_3 : constant
   c4_2, c4_3, c4_5, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12 : constant
   g5_1 : constant
   c5_3, c5_8 : constant

theory G(.,e,i)

axioms

g1_1 = g1;
g1_2 = g2;
c1_1 = c1_2 . i(g1_2);
c1_2 = c1_3 . g1_1;
c1_3 = c1_4 . i(g1_2);
c1_4 = e;
c1_5 = c1_4 . g1_2;
c1_6 = c1_5 . g1_2;
c1_7 = c1_6 . g1_2;
c1_8 = c1_9 . i(g1_2);
c1_9 = c1_10 . i(g1_2);
c1_10 = c1_5 . g1_1;
c1_11 = c1_10 . g1_2;
c1_12 = c1_11 . g1_2;
c1_13 = c1_1 . i(g1_2);

g2_1 = c1_1 . g1_1 . i(c1_1);
g2_2 = c1_4 . g1_1 . i(c1_4);
g2_3 = c1_6 . g1_1 . i(c1_6);
g2_4 = c1_2 . g1_2 . i(c1_3);
c2_1 = e;
c2_2 = c2_1 . g2_4;
c2_3 = c2_2 . g2_2;
c2_5 = c2_6 . i(g2_4);
c2_6 = c2_1 . g2_1;
c2_7 = c2_10 . g2_3;
c2_8 = c2_13 . i(g2_4);
c2_9 = c2_10 . g2_1;
c2_10 = c2_1 . i(g2_4);
c2_11 = c2_13 . g2_4;
c2_12 = c2_6 . g2_4;
c2_13 = c2_1 . g2_3;
g3_1 = c2_2 . g2_1 . i(c2_2);
g3_2 = c2_3 . g2_1 . i(c2_5);
g3_3 = c2_7 . g2_1 . i(c2_8);
c3_6 = e;
c3_13 = c3_6 . g3_3;
g4_1 = c3_6 . g3_1 . i(c3_6);
g4_2 = c3_13 . g3_1 . i(c3_13);
g4_3 = c3_6 . g3_2 . i(c3_6);
c4_2 = e;
c4_3 = c4_2 . g4_1;
c4_5 = c4_2 . g4_3;
c4_7 = c4_9 . g4_2;
c4_8 = c4_2 . g4_2;
c4_9 = c4_3 . g4_3;
c4_10 = c4_5 . g4_1;
c4_11 = c4_8 . g4_3;
c4_12 = c4_5 . g4_2;
g5_1 = c4_8 . g4_1 . i(c4_8);
c5_3 = e;
c5_8 = c5_3 . g5_1;


c2_6 = c1_1 . i(g1_1) . i(c1_1);
c1_1 . g1_2 . i(c1_2) = e;
c1_2 . g1_1 . i(c1_3) = e;
c2_10 = c1_3 . i(g1_2) . i(c1_2);
c4_3 . c3_6 . c2_1 = c1_4 . i(g1_1) . i(c1_4);
c2_13 = c1_6 . i(g1_1) . i(c1_6);
c4_12 . c3_6 . c2_1 = c1_11 . i(g1_1) . i(c1_7);
c5_8 . c4_10 . c3_6 . c2_10 = c1_8 . i(g1_2) . i(c1_7);
c5_8 . c4_12 . c3_13 . c2_1 = c1_8 . i(g1_1) . i(c1_8);
c1_8 . g1_2 . i(c1_9) = e;
c5_8 . c4_7 . c3_13 . c2_6 = c1_12 . i(g1_1) . i(c1_9);
c1_9 . g1_2 . i(c1_10) = e;
c1_10 . g1_1 . i(c1_5) = e;
c4_11 . c3_6 . c2_1 = c1_7 . i(g1_1) . i(c1_11);
c5_8 . c4_5 . c3_13 . c2_13 = c1_9 . i(g1_1) . i(c1_12);
c4_7 . c3_6 . c2_7 = c1_13 . i(g1_2) . i(c1_12);
c5_8 . c4_3 . c3_6 . c2_13 = c1_13 . i(g1_1) . i(c1_13);
c1_13 . g1_2 . i(c1_1) = e;

c4_3 . c3_6 = c2_1 . i(g2_2) . i(c2_1);
c4_3 . c3_6 = c2_2 . i(g2_1) . i(c2_2);
c4_7 . c3_6 = c2_2 . i(g2_3) . i(c2_2);
c4_10 . c3_6 = c2_3 . i(g2_4) . i(c2_2);
c4_5 . c3_6 = c2_5 . i(g2_1) . i(c2_3);
c2_3 . g2_2 . i(c2_2) = e;
c4_8 . c3_6 = c2_8 . i(g2_3) . i(c2_3);
c4_3 . c3_6 = c2_5 . i(g2_4) . i(c2_3);
c4_5 . c3_6 = c2_3 . i(g2_1) . i(c2_5);
c2_5 . g2_2 . i(c2_10) = e;
c4_11 . c3_13 = c2_9 . i(g2_3) . i(c2_5);
c2_5 . g2_4 . i(c2_6) = e;
c4_5 . c3_6 = c2_6 . i(g2_2) . i(c2_6);
c4_12 . c3_13 = c2_6 . i(g2_3) . i(c2_6);
c4_11 . c3_13 = c2_8 . i(g2_1) . i(c2_7);
c4_3 . c3_6 = c2_11 . i(g2_2) . i(c2_7);
c2_7 . g2_3 . i(c2_10) = e;
c5_8 . c4_3 . c3_13 = c2_8 . i(g2_4) . i(c2_7);
c3_13 = c2_7 . i(g2_1) . i(c2_8);
c4_12 . c3_13 = c2_8 . i(g2_2) . i(c2_8);
c4_8 . c3_6 = c2_3 . i(g2_3) . i(c2_8);
c2_8 . g2_4 . i(c2_13) = e;
c2_9 . g2_1 . i(c2_10) = e;
c4_3 . c3_6 = c2_12 . i(g2_2) . i(c2_9);
c3_13 = c2_5 . i(g2_3) . i(c2_9);
c4_10 . c3_6 = c2_10 . i(g2_4) . i(c2_9);
c2_10 . g2_2 . i(c2_5) = e;
c4_8 . c3_6 = c2_11 . i(g2_1) . i(c2_11);
c4_3 . c3_6 = c2_7 . i(g2_2) . i(c2_11);
c5_8 . c4_10 . c3_6 = c2_11 . i(g2_3) . i(c2_11);
c5_8 . c4_10 . c3_6 = c2_7 . i(g2_4) . i(c2_11);
c4_5 . c3_6 = c2_12 . i(g2_1) . i(c2_12);
c4_3 . c3_6 = c2_9 . i(g2_2) . i(c2_12);
c4_8 . c3_6 = c2_12 . i(g2_3) . i(c2_12);
c4_5 . c3_6 = c2_9 . i(g2_4) . i(c2_12);
c4_12 . c3_13 = c2_13 . i(g2_1) . i(c2_13);
c4_8 . c3_6 = c2_13 . i(g2_2) . i(c2_13);
c4_3 = c3_6 . i(g3_1) . i(c3_6);
c4_5 = c3_6 . i(g3_2) . i(c3_6);
c4_8 = c3_13 . i(g3_1) . i(c3_13);
c4_3 = c3_13 . i(g3_2) . i(c3_13);
c4_11 = c3_6 . i(g3_3) . i(c3_13);
c5_8 = c4_3 . i(g4_2) . i(c4_3);
c4_7 . g4_1 . i(c4_11) = e;
c4_7 . g4_2 . i(c4_9) = e;
c5_8 = c4_7 . i(g4_3) . i(c4_7);
c5_8 = c4_8 . i(g4_1) . i(c4_8);
c5_8 = c4_12 . i(g4_1) . i(c4_9);
c4_9 . g4_3 . i(c4_3) = e;
c4_10 . g4_1 . i(c4_5) = e;
c5_8 = c4_11 . i(g4_2) . i(c4_10);
c5_8 = c4_12 . i(g4_3) . i(c4_10);
c4_11 . g4_1 . i(c4_7) = e;
c5_8 = c4_10 . i(g4_2) . i(c4_11);
c4_11 . g4_3 . i(c4_8) = e;
c5_8 = c4_9 . i(g4_1) . i(c4_12);
c4_12 . g4_2 . i(c4_5) = e;
c5_8 = c4_10 . i(g4_3) . i(c4_12);

order
  rpo
% rajoute par moi
   g2 > g1,

   i > . > g1_1 > g1 > e,
   i > . > g1_2 > g2 > e,
   c1_1 > c1_2 > i,
   c1_2 > c1_3 > i,
   c1_3 > c1_4 > i,
   c1_4 > i > e,
   c1_5 > c1_4 > i,
   c1_6 > c1_5 > i,
   c1_7 > c1_6 > i,
   c1_8 > c1_9 > i,
   c1_9 > c1_10 > i,
   c1_10 > c1_5 > i,
   c1_11 > c1_10 > i,
   c1_12 > c1_11 > i,
   c1_13 > c1_1 > i,
   g2_1 > c1_1,
   g2_1 > c1_2,
   g2_1 > c1_3,
   g2_1 > c1_4,
   g2_1 > c1_5,
   g2_1 > c1_6,
   g2_1 > c1_7,
   g2_1 > c1_8,
   g2_1 > c1_9,
   g2_1 > c1_10,
   g2_1 > c1_11,
   g2_1 > c1_12,
   g2_1 > c1_13,
   g2_2 > c1_1,
   g2_2 > c1_2,
   g2_2 > c1_3,
   g2_2 > c1_4,
   g2_2 > c1_5,
   g2_2 > c1_6,
   g2_2 > c1_7,
   g2_2 > c1_8,
   g2_2 > c1_9,
   g2_2 > c1_10,
   g2_2 > c1_11,
   g2_2 > c1_12,
   g2_2 > c1_13,
   g2_3 > c1_1,
   g2_3 > c1_2,
   g2_3 > c1_3,
   g2_3 > c1_4,
   g2_3 > c1_5,
   g2_3 > c1_6,
   g2_3 > c1_7,
   g2_3 > c1_8,
   g2_3 > c1_9,
   g2_3 > c1_10,
   g2_3 > c1_11,
   g2_3 > c1_12,
   g2_3 > c1_13,
   g2_4 > c1_1,
   g2_4 > c1_2,
   g2_4 > c1_3,
   g2_4 > c1_4,
   g2_4 > c1_5,
   g2_4 > c1_6,
   g2_4 > c1_7,
   g2_4 > c1_8,
   g2_4 > c1_9,
   g2_4 > c1_10,
   g2_4 > c1_11,
   g2_4 > c1_12,
   g2_4 > c1_13,
   c2_1 > g1_1 > e,
   c2_1 > g1_2 > e,
   c2_1 > g1_3 > e,
   c2_1 > g1_4 > e,
   c2_2 > c2_1 > g2_1,
   c2_2 > c2_1 > g2_2,
   c2_2 > c2_1 > g2_3,
   c2_2 > c2_1 > g2_4,
   c2_3 > c2_2 > g2_1,
   c2_3 > c2_2 > g2_2,
   c2_3 > c2_2 > g2_3,
   c2_3 > c2_2 > g2_4,
   c2_5 > c2_6 > g2_1,
   c2_5 > c2_6 > g2_2,
   c2_5 > c2_6 > g2_3,
   c2_5 > c2_6 > g2_4,
   c2_6 > c2_1 > g2_1,
   c2_6 > c2_1 > g2_2,
   c2_6 > c2_1 > g2_3,
   c2_6 > c2_1 > g2_4,
   c2_7 > c2_10 > g2_1,
   c2_7 > c2_10 > g2_2,
   c2_7 > c2_10 > g2_3,
   c2_7 > c2_10 > g2_4,
   c2_8 > c2_13 > g2_1,
   c2_8 > c2_13 > g2_2,
   c2_8 > c2_13 > g2_3,
   c2_8 > c2_13 > g2_4,
   c2_9 > c2_10 > g2_1,
   c2_9 > c2_10 > g2_2,
   c2_9 > c2_10 > g2_3,
   c2_9 > c2_10 > g2_4,
   c2_10 > c2_1 > g2_1,
   c2_10 > c2_1 > g2_2,
   c2_10 > c2_1 > g2_3,
   c2_10 > c2_1 > g2_4,
   c2_11 > c2_13 > g2_1,
   c2_11 > c2_13 > g2_2,
   c2_11 > c2_13 > g2_3,
   c2_11 > c2_13 > g2_4,
   c2_12 > c2_6 > g2_1,
   c2_12 > c2_6 > g2_2,
   c2_12 > c2_6 > g2_3,
   c2_12 > c2_6 > g2_4,
   c2_13 > c2_1 > g2_1,
   c2_13 > c2_1 > g2_2,
   c2_13 > c2_1 > g2_3,
   c2_13 > c2_1 > g2_4,
   g3_1 > c2_1,
   g3_1 > c2_2,
   g3_1 > c2_3,
   g3_1 > c2_5,
   g3_1 > c2_6,
   g3_1 > c2_7,
   g3_1 > c2_8,
   g3_1 > c2_9,
   g3_1 > c2_10,
   g3_1 > c2_11,
   g3_1 > c2_12,
   g3_1 > c2_13,
   g3_2 > c2_1,
   g3_2 > c2_2,
   g3_2 > c2_3,
   g3_2 > c2_5,
   g3_2 > c2_6,
   g3_2 > c2_7,
   g3_2 > c2_8,
   g3_2 > c2_9,
   g3_2 > c2_10,
   g3_2 > c2_11,
   g3_2 > c2_12,
   g3_2 > c2_13,
   g3_3 > c2_1,
   g3_3 > c2_2,
   g3_3 > c2_3,
   g3_3 > c2_5,
   g3_3 > c2_6,
   g3_3 > c2_7,
   g3_3 > c2_8,
   g3_3 > c2_9,
   g3_3 > c2_10,
   g3_3 > c2_11,
   g3_3 > c2_12,
   g3_3 > c2_13,
   c3_6 > g2_1 > e,
   c3_6 > g2_2 > e,
   c3_6 > g2_3 > e,
   c3_13 > c3_6 > g3_1,
   c3_13 > c3_6 > g3_2,
   c3_13 > c3_6 > g3_3,
   g4_1 > c3_6,
   g4_1 > c3_13,
   g4_2 > c3_6,
   g4_2 > c3_13,
   g4_3 > c3_6,
   g4_3 > c3_13,
   c4_2 > g3_1 > e,
   c4_2 > g3_2 > e,
   c4_2 > g3_3 > e,
   c4_3 > c4_2 > g4_1,
   c4_3 > c4_2 > g4_2,
   c4_3 > c4_2 > g4_3,
   c4_5 > c4_2 > g4_1,
   c4_5 > c4_2 > g4_2,
   c4_5 > c4_2 > g4_3,
   c4_7 > c4_9 > g4_1,
   c4_7 > c4_9 > g4_2,
   c4_7 > c4_9 > g4_3,
   c4_8 > c4_2 > g4_1,
   c4_8 > c4_2 > g4_2,
   c4_8 > c4_2 > g4_3,
   c4_9 > c4_3 > g4_1,
   c4_9 > c4_3 > g4_2,
   c4_9 > c4_3 > g4_3,
   c4_10 > c4_5 > g4_1,
   c4_10 > c4_5 > g4_2,
   c4_10 > c4_5 > g4_3,
   c4_11 > c4_8 > g4_1,
   c4_11 > c4_8 > g4_2,
   c4_11 > c4_8 > g4_3,
   c4_12 > c4_5 > g4_1,
   c4_12 > c4_5 > g4_2,
   c4_12 > c4_5 > g4_3,
   g5_1 > c4_2,
   g5_1 > c4_3,
   g5_1 > c4_5,
   g5_1 > c4_7,
   g5_1 > c4_8,
   g5_1 > c4_9,
   g5_1 > c4_10,
   g5_1 > c4_11,
   g5_1 > c4_12,
   c5_3 > g4_1 > e,
   c5_8 > c5_3 > g5_1;
  . lrlex


end


