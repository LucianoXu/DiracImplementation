operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable

axioms
  x.(y.z) = (x.y).z;
  x.e = x;
  x.I(x) = e;

conjectures
  e.x = x;
  I(x).x = e;

end

