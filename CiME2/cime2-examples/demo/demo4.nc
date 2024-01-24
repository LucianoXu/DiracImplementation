%***************************************************************************
%
%
% Comple'tion modulo CR de l'anneau quotient d\'efini par
%
%   2X^2Y - Y et 3XY^2 -X
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo4.nc
% Created on:              10 mar 93
% Last modified on: 10 mar 93
%
%***************************************************************************

operators
  +,* : AC
  0,1 : constant
  -   : unary
  X,Y,Z : constant
  x,y,z : variable

theory  CR(+,0,-,*,1)

axioms
  (X*X*Y) + (X*X*Y) + -(Y) = 0;
  (X*Y*Y) + (X*Y*Y) + (X*Y*Y) + -(X) = 0;
  
order rpo( Y>X>1>*>- >0>+ ; + mul, * mul)
% interactive

end

% Resultat :
% {(z*Y*Y)+(z*Y*Y)+(z*Y*Y) -> (z*X*X)+(z*X*X),
% (Y*Y)+(Y*Y)+(Y*Y) -> (X*X)+(X*X),
% (X*X*Y)+(X*X*Y) -> Y,
% -(X*X*X) -> -(X)+(X*X*X),
% -(X*X*Y) -> -(Y)+(X*X*Y),
% (z*X*X*Y)+(z*X*X*Y) -> z*Y,
% -(z*X*X*X) -> -(z*X)+(z*X*X*X),
% X*X*Y*Y -> (Y*Y)+(Y*Y)+-(X*X),
% -(z*X*X*Y) -> -(z*Y)+(z*X*X*Y),
% (z*X*X*X)+(z*X*X*X) -> z*X,
% (X*X*X)+(X*X*X) -> X,
% -(Y*Y) -> -(X*X)+-(X*X)+(Y*Y)+(Y*Y),
% -(z*Y*Y) -> -(z*X*X)+-(z*X*X)+(z*Y*Y)+(z*Y*Y)} (13 regles)
% 
% Nombre d'appels au filtrage AC     : 27628
% Nombre d'appels reussis            : 585 (2%)
% Nombre d'appels a l'unification AC : 172
% Nombre de solutions trouvees       : 117 (0 en moyenne)
% 
% Temps utilisateur : 78.940 s  (1 mn 18 s)
% Temps syste`me : 0.810 s
% 
% Comparaison avec RRL:
% 
% Number of rules generated            =  53
% Number of rules retained             =  22
% Number of critical pairs             =  661
% Number of unblocked critical pairs   =  252
% Time used                            =  36.05 sec
%  Time spent in normalization         =  24.08 sec  (66.0 percent of time)
%  Time spent in unification           =   5.18 sec   (14.0 percent of time)
%  Time spent in ordering              =   0.08 sec   (0.0 percent of time)
%  Time spent in simplifying the rules =   1.20 sec   (3.0 percent of time)
%  Time spent in blocking              =   1.37 sec   (3.0 percent of time)
% Total time (including 'undo' action) = 36.13333333333333 sec
% 
% Time for this command = 36.133 sec      Total time = 75.017 sec

