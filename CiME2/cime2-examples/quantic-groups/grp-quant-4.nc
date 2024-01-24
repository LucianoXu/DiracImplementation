%***************************************************************************
%
% Groupes Quantiques
% (Probleme de Guichardet)
% cas de N=4
% 
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        grp-quant-4.nc
% Created on:              10 nov 93
% Last modified on: 22 nov 93
%
%***************************************************************************

operators
  . : infix binary
  + : AC
  0,1,t : constant
  - : unary
  pm2mp2,p2,pm2 : unary
  x,y,z : variable

  X11,X12,X13,X14,X22,X23,X24,X33,X34,X44 : constant

theory 
  AU(.,1)
  AG(+,0,-)

axioms
  X11.t = t.X11;
  X12.t = t.X12;
  X13.t = t.X13;
  X14.t = t.X14;
  X22.t = t.X22;
  X23.t = t.X23;
  X24.t = t.X24;
  X33.t = t.X33;
  X34.t = t.X34;
  X44.t = t.X44;

  X11.p2(t) = p2(t).X11;
  X12.p2(t) = p2(t).X12;
  X13.p2(t) = p2(t).X13;
  X14.p2(t) = p2(t).X14;
  X22.p2(t) = p2(t).X22;
  X23.p2(t) = p2(t).X23;
  X24.p2(t) = p2(t).X24;
  X33.p2(t) = p2(t).X33;
  X34.p2(t) = p2(t).X34;
  X44.p2(t) = p2(t).X44;

  X11.pm2(t) = pm2(t).X11;
  X12.pm2(t) = pm2(t).X12;
  X13.pm2(t) = pm2(t).X13;
  X14.pm2(t) = pm2(t).X14;
  X22.pm2(t) = pm2(t).X22;
  X23.pm2(t) = pm2(t).X23;
  X24.pm2(t) = pm2(t).X24;
  X33.pm2(t) = pm2(t).X33;
  X34.pm2(t) = pm2(t).X34;
  X44.pm2(t) = pm2(t).X44;

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
  X11.X14 = pm2(t).X14.X11;
  X11.X22 = (p2(t).X22.X11) + (t.X12);
  X11.X23 = (p2(t).X23.X11) + (t.X13);
  X11.X24 = (p2(t).X24.X11) + (t.X14);
  X11.X33 = X33.X11;
  X11.X34 = X34.X11;
  X11.X44 = X44.X11;

  X12.X13 = pm2(t).X13.X12;
  X12.X14 = pm2(t).X14.X12;
  X12.X22 = pm2(t).X22.X12;
  X12.X23 = (X23.X12) + (pm2mp2(t).X22.X13);
  X12.X24 = (X24.X12) + (pm2mp2(t).X22.X14);
  X12.X33 = (p2(t).X33.X12) + (t.X13);
  X12.X34 = (p2(t).X34.X12) + (t.X14);
  X12.X44 = X44.X12;

  X13.X14 = pm2(t).X14.X13;
  X13.X22 = X22.X13;
  X13.X23 = pm2(t).X23.X13;
  X13.X24 = (X24.X13) + (pm2mp2(t).X23.X14);
  X13.X33 = pm2(t).X33.X13;
  X13.X34 = (X34.X13) + (pm2mp2(t).X33.X14);
  X13.X44 = (p2(t).X44.X13) + (t.X14);

  X14.X22 = X22.X14;
  X14.X23 = X23.X14;
  X14.X24 = pm2(t).X24.X14;
  X14.X33 = X33.X14;
  X14.X34 = pm2(t).X34.X14;
  X14.X44 = pm2(t).X44.X14;

  X22.X23 = pm2(t).X23.X22;
  X22.X24 = pm2(t).X24.X22;
  X22.X33 = (p2(t).X33.X22) + (t.X23);
  X22.X34 = (p2(t).X34.X22) + (t.X24);
  X22.X44 = X44.X22;

  X23.X24 = pm2(t).X24.X23;
  X23.X33 = pm2(t).X33.X23;
  X23.X34 = (X34.X23) + (pm2mp2(t).X33.X24);
  X23.X44 = (p2(t).X44.X23) + (t.X24);

  X24.X33 = X33.X24;
  X24.X34 = pm2(t).X34.X24;
  X24.X44 = pm2(t).X44.X24;

  X33.X34 = pm2(t).X34.X33;
  X33.X44 = (p2(t).X44.X33) + (t.X34);

  X34.X44 = pm2(t).X44.X34;

order 
  rpo( X11>X12>X13>X14>X22>X23>X24>X33>X34>X44 >  
       pm2mp2 > pm2 > p2 > t > 1 > . > - > + > 0 ; 
       . lrlex, + mul )

end

