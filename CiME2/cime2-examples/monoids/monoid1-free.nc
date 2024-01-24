

operators
  . : infix binary
  1 : constant
  a,b,c,d : constant
  x,y,z : variable

axioms

   (x.y).z = x.(y.z) ;
   x.1 = x ;
   1.x =x ;
   a.b.b = c ;
   b.c = d ;

order
  lexico(rpo(a=b=c=d>.;. lrlex); 
	 rpo(a>b>c>d>.; . lrlex))

end
