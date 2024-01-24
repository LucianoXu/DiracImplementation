%***************************************************************************
%
% Groupes quantiques
% (Probleme de Guichardet)
% cas de N=2
% 
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        grp-quant-2.nc
% Created on:              10 nov 93
% Last modified on: 10 nov 93
%
%***************************************************************************

operators
  . : infix binary
  + : AC
  0,1,t : constant
  - : unary
  X11,X12,X22 : constant
  pm2mp2,p2,pm2 : unary
  x,y,z : variable

theory 
  AU(.,1)
  AG(+,0,-)

unification theory 
  AG(+,0,-)

axioms
  x.(y+z) = (x.y) + (x.z);
  (x+y).z = (x.z) + (y.z);
  x.0 = 0;
  0.x = 0;
  x.-(y) = -(x.y);
  -(x).y = -(x.y);

  X11.t = t.X11;
  X12.t = t.X12;
  X22.t = t.X22;

  X11.p2(t) = p2(t).X11;
  X12.p2(t) = p2(t).X12;
  X22.p2(t) = p2(t).X22;

  X11.pm2(t) = pm2(t).X11;
  X12.pm2(t) = pm2(t).X12;
  X22.pm2(t) = pm2(t).X22;

  p2(t).t = t.p2(t);
  pm2(t).t = t.pm2(t);
  pm2(t).p2(t) = 1; 
  p2(t).pm2(t) = 1;
 
  X11.X12 = pm2(t).X12.X11;
  X11.X22 = (p2(t).X22.X11) + (t.X12);

  X12.X22 = pm2(t).X22.X12;

order 
 rpo( X11>X12>X22 > pm2mp2 > pm2 > p2 > t > 1 > . > - > + > 0; 
      . lrlex , + mul )

end

