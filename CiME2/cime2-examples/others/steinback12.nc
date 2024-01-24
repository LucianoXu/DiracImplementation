
operators
  0 : constant
  s,h : unary
  f,g : binary
  x,y,z : variable

axioms
  s(s(x)) = x;
  f(0,y) = y;
  f(s(x),y) = s(f(x,y));
  f(f(g(x,y),0),0) = g(x,y);
  g(0,y) = y;
  g(s(x),y) = f(g(x,y),0);
  h(0) = s(0);

order
  rpo (g>f>h>s>0)

end