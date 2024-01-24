operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable

axioms
  x.(y.z) = (x.y).z;
  x.e = x;
  x.I(x) = e;
  e.x = x;
  I(x).x = e;

order
  rpo(I>.>e;. rllex)

conjectures
  I(x.y) = I(y).I(x);

problems
  I(x.y) = I(x).I(y);

end

