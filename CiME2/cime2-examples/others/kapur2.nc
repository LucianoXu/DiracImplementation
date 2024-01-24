%***************************************************************************
%
% Finding a canonical rewrite system for the theory described in file
% kapur1.n by adding a new constant
%
% $Id: kapur2.nc,v 1.2 1996/05/31 15:08:17 marche Exp $
%
%***************************************************************************

operators
  . : infix binary
  a,b,c : constant
  x,y,z : variable

theory 
  A(.)

axioms
  a.(b.a) = b.(a.b);
  a.b = c;

order 
  lexico( rpo(c=b=a, a>. ; . lrlex) ;
          rpo(c>b>a>. ; . lrlex)
        )
end

