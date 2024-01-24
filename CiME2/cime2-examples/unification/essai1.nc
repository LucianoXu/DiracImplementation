
operators
  + : AC
  . : 2
  I : 1
  - : 1
  e : constant
  f,g : 2
  x,y,z,t,u,v,w : variable
  a,b : constant
  0 : constant

%  unification theory ACU(+,0)

problems

%  unify  I(u).u  = x.y ;
%  unify  x + -(x) + y = u + .(0,u) + v;
%  unify  x + -(x) + y = u + .(0,u) ;
%  unify  x + -(x)     = u + .(0,u) + v;
%  unify  x + -(x)     = u + .(0,u);
%  unify  x + -(x) + y = .(w,u) + .(0,u) + v;
%  unify  x + -(x)     = .(w,u) + .(0,u) + v;
%  unify  x + -(x) + y = .(w,u) + .(0,u);
%  unify  x + -(x)     = .(w,u) + .(0,u);
%  unify x+y = t+u;
%  unify x+a = y+b;
%  unify -(-(x)) = -(0);
  unify x+y+-(y+z) = u+v+-(v+w);

end

