%***************************************************************************
%
% A decidable theory without any canonical rewrite system
%
% @Article{kapur85tcs,
%   author        = "Deepak Kapur and Paliath Narendran",
%   title         = "A Finite {T}hue system with decidable word problem
%                   and without equivalent finite canonical system",
%   journal       = tcs,
%   year          = 1985,
%   volume        = 35,
%   pages         = "337--344"
% }
%
% see also file kapur2.nc
%
% $Id: kapur1.nc,v 1.2 1996/05/31 15:08:16 marche Exp $
%
%***************************************************************************

operators
  . : infix binary
  a,b : constant
  x,y,z : variable

theory 
  A(.)

axioms
  a.(b.a) = b.(a.b);

order 
  lexico(rpo(b=a, a>. ; . lrlex) ;
	 rpo(b>a>. ; . lrlex)
	 )
  
end

