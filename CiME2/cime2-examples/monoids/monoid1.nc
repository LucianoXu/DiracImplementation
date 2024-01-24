

operators
  . : infix binary
  1 : constant
  a,b,c,d : constant

theory AU(.,1)

axioms

%  a.a.b.b.b = c ;
%  a = b.c.c.c ;

   a.b.b = c ;
   b.c = d ;

order
  lexico(rpo(a=b=c=d>.;. lrlex); 
	 rpo(a>b>c>d>.; . lrlex))

end
