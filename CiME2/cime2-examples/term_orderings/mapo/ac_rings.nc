% Associative commutative rings.
% This example is from the article of Delor and Puel.

operators
  +,*	: AC
  I	: 1
  0	: constant

  x,y,z	: variable

order
  mapo(*>I>+>0)


problems
  compare  x + 0	with  x;
  compare  x + I(x)	with  0;
  compare  I(0)		with  0;
  compare  I(I(x))	with  x;
  compare  I(x + y)	with  I(x) + I(y);
  compare  x * (y + z)	with  (x * y) + (x * z);
  compare  x * 0	with  0;
  compare  x * I(y)	with  I(x * y);

end

