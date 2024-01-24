%***************************************************************************
%
% Groupes quantiques
% (Probleme de Guichardet)
% cas de N=3
% 
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        grp-quant-3.nc
% Created on:              22 nov 93
% Last modified on: 25 nov 93
%
%***************************************************************************

operators
  . : infix binary
  + : AC
  0,1,t : constant
  - : unary
  pm2mp2,p2,pm2 : unary
  x,y,z : variable

  X11,X12,X13,X22,X23,X33 : constant

theory 
  AU(.,1)
  AG(+,0,-)

axioms
  X11.t = t.X11;
  X12.t = t.X12;
  X13.t = t.X13;
  X22.t = t.X22;
  X23.t = t.X23;
  X33.t = t.X33;

  X11.p2(t) = p2(t).X11;
  X12.p2(t) = p2(t).X12;
  X13.p2(t) = p2(t).X13;
  X22.p2(t) = p2(t).X22;
  X23.p2(t) = p2(t).X23;
  X33.p2(t) = p2(t).X33;

  X11.pm2(t) = pm2(t).X11;
  X12.pm2(t) = pm2(t).X12;
  X13.pm2(t) = pm2(t).X13;
  X22.pm2(t) = pm2(t).X22;
  X23.pm2(t) = pm2(t).X23;
  X33.pm2(t) = pm2(t).X33;

  pm2mp2(t) = pm2(t) + -(p2(t));


  p2(t).t = t.p2(t);
  pm2(t).t = t.pm2(t);
  pm2(t).p2(t) = 1; 
  p2(t).pm2(t) = 1;
 
  x.(y+z) = (x.y) + (x.z);
  (x+y).z = (x.z) + (y.z);
  x.0 = 0;
  0.x = 0;
  x.-(y) = -(x.y);
  -(x).y = -(x.y);


  X11.X12 = pm2(t).X12.X11;
  X11.X13 = pm2(t).X13.X11;
  X11.X22 = (p2(t).X22.X11) + (t.X12);
  X11.X23 = (p2(t).X23.X11) + (t.X13);
  X11.X33 = X33.X11;

  X12.X13 = pm2(t).X13.X12;
  X12.X22 = pm2(t).X22.X12;
  X12.X23 = (X23.X12) + (pm2mp2(t).X22.X13);
  X12.X33 = (p2(t).X33.X12) + (t.X13);

  X13.X22 = X22.X13;
  X13.X23 = pm2(t).X23.X13;
  X13.X33 = pm2(t).X33.X13;

  X22.X23 = pm2(t).X23.X22;
  X22.X33 = (p2(t).X33.X22) + (t.X23);

  X23.X33 = pm2(t).X33.X23;

order 
 rpo( X11>X12>X13>X22>X23>X33 >  
      pm2mp2 > pm2 > p2 > t > 1 > . > - > + > 0; 
      . lrlex, + mul
    )

end

