% This example demonstrates that several chains of can be ontained in the
% precedence. However, every chain must contain at most two AC symbols,
% only unary symbols are allowed between AC symbols, and constants must
% be minimal in these chains.

operators
  +,*		: AC
  i,j,k,l,m	: 1
  0		: constant

  @,&		: AC
  I,J,K,L,M	: 1
  1		: constant

  a		: constant

  x,y,z	: variable

order
  mapo(*>i>j>k>l>m>+>0,@>I>J>K>L>M>&>1)


problems
  compare  x * y	with  x + y;
  compare  x @ y	with  x & y;
  compare  x @ y	with  x * y;

  compare  m(l(k(j(i(a)))))	with i(j(k(l(m(a)))));

  compare  ( x * ( x + ( y @ ( y & a ) ) ) )
  with     ( x + ( x * ( y @ ( y & a ) ) ) ) ;

  compare  ( x * ( x + ( y @ ( y & a ) ) ) )
  with     ( x*x ) + ( x * ( ( y@y ) & ( y@a ) ) ) ;

end

