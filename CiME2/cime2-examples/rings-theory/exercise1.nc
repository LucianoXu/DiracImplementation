operators
  +   : AC
  *   : infix binary
  0,1 : constant
  -   : 1
  x,y,z : variable

axioms
  x+0 = x;
  x+-(x) = 0;
  x*(y*z) = (x*y)*z;
  x*1 = x;
  1*x = x;
  x*(y+z) = (x*y)+(x*z);
  (x+y)*z = (x*z)+(y*z);

order  
  rpo( * > - > + > 0 , *>1 ; * lrlex )

problems
  (x+-(y))*(-(x)+y) = ((x+y)*(x+y))+-((x+x)*x)+-((y+y)*y) ;
  (x+y)*(x+-(y)) = (x*x)+(-(y*y)) ;
  reduce (x+y+z)*(x+y+(-(z))) ;
  reduce (((x*(y+z+(-(y))))+y+((x+1)*(-(z)))+1)*y)+(y*z) ;
 
end

