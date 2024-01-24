%***************************************************************************
%
%
% algebre lambda star de laurent regnier
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        lstar.nc
% Created on:              08 jul 93
% Last modified on: 08 jul 93
%
%***************************************************************************

operators
  . : infix binary
  0,1 : constant
  *,! : 1
  p,q : constant
  t : constant
  d0,d1,d2 : constant
  x,y,z,u,v : variable

theory
  AU(.,1)

axioms
  !(x.y) = !(x).!(y);
  *(*(x)) = x; 
  *(x.y) = *(y).*(x);

  *(p).p = 1; *(q).q = 1;
  *(t).t = 1;
  *(d0).d0 = 1;
  *(d1).d1 = 1;
  *(d2).d2 = 1;
  *(1) = 1;

  *(p).q = 0;
  *(d0).d1 = 0;
  *(d0).d2 = 0;
  *(d1).d2 = 0;

  !(x).d0 = d0.x;
  !(x).d1 = d1.x;
  !(x).d2 = d2.x;
  !(x).t = t.!(!(x));

order
%  lexico( rpo( t=p=q=d0=d1=d2=*=!=0 , !>.>1 ; . lrlex ) ;
          interactive
%        )

end

