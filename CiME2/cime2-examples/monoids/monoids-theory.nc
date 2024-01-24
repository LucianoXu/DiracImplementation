

operators
  . : infix binary
  1 : constant
  x,y,z : variable

axioms

   (x.y).z = x.(y.z) ;
   x.1 = x ;
   1.x =x ;

order
  rpo(.>1 ;. lrlex)

end
