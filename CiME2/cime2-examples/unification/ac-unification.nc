
operators
  + : AC
  . : infix binary
  f,g : 2
  x,y,z,t,u,v,w : variable
  a,b : constant
  0 : constant
  h5 : 5
  h3 : 3
  h2 : 2
  h1 : 1
  - : unary

problems

  unify a = b;
 
  unify x+y = y+x;

  unify x+a = y+b;

  unify x+f(y,y) = z+f(u,u);

  unify x+x+y+g(x,u) = z+g(a,b)+g(a,b);

  unify x+x+y+u = z+v+v;

  unify x+y = z+t;

  unify x+x = y+z+t;

  unify f(x+y,y+x) = f(z,z);

  unify 0 = x+y ;
 
  unify h5(y,z,t,v,x) = h5(v+u+y,v+u,u+w,-(x),-(y));

  unify h5(y,z,t,v,x) = h5(h3(v,u,y),h2(v,u),h2(u,w),h1(x),h1(y));

  unify u+x+-(x) = v+z+(0.z);
 
  unify x.(y+z) = t.0;

%  unify  x+-(x)+y = a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a+a;

end
