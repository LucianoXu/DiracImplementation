%***************************************************************************
%
%
% Comple'tion modulo AG du groupe finiment engendre' par
%
%    2a-3b+c   = 0
%    -3a+2b+3c = 0 
%    2a+2b-2c  = 0
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo3.nc
% Created on:              24 mar 93
% Last modified on: 24 mar 93
%
%***************************************************************************

operators
  + : AC
  0 : constant
  - : unary
  x,y : variable
  a,b,c : constant

theory  AG(+,0,-)

axioms
  a+a+-(b+b+b)+c = 0;
  -(a+a+a)+b+b+c+c+c = 0;
  a+a+b+b+-(c+c) = 0;

order  rpo( c>b>a>- >0>+ ; + mul)
  % interactive

end

% Resultat :
% {a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a -> 0,
% -(a) -> a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a,
% b -> a+a+a+a+a+a+a+a+a,
% c -> a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a} (4 regles)
% 
% Nombre d'appels au filtrage AC     : 4014
% Nombre d'appels reussis            : 251 (6% )
% Nombre d'appels a l'unification AC : 19
% Nombre de solutions trouvees       : 14 (0 en moyenne)
% 
% Resolution des problemes :
% Temps utilisateur : 85.890 s  (1 mn 25 s)
% Temps syste`me : 0.530 s
% 
% Comparaison avec RRL:
% 
% Number of rules generated            =  59
% Number of rules retained             =  9
% Number of critical pairs             =  837
% Number of unblocked critical pairs   =  100
% Time used                            = 202.10 sec
%  Time spent in normalization         = 179.28 sec  (88.0 percent of time)
%  Time spent in unification           =   6.67 sec   (3.0 percent of time)
%  Time spent in ordering              =   0.33 sec   (0.0 percent of time)
%  Time spent in simplifying the rules =   7.28 sec   (3.0 percent of time)
%  Time spent in blocking              =   1.73 sec   (0.0 percent of time)
% Total time (including 'undo' action) = 202.15 sec
% 
% Time for this command = 202.183 sec      Total time = 202.267 sec

