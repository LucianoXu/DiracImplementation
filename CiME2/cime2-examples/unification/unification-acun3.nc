
operators
  + : AC
  . : binary
  f,g : 2
  x,y,z,t,u,v,w : variable
  a,b : constant
  0 : constant
  h5 : 5
  h3 : 3
  h2 : 2
  h1 : 1
  - : unary

unification theory ACUN(+,0,3)

problems

plain unify 0 = a+a+a;
%plain unify a+a+a = 0;
%plain unify a+a+a+a+a = a+a;
%plain unify x+x+x = 0;
%plain unify x+x+x+x+x = x+x;
%AC complete unify a+b = u+v;
%AC only unify a+b = u+v;

end

