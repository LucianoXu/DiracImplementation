%
%
%         Entiers en base 2. Seul probleme, on ne sait pas prouver -0 = 0.
%
%

operators

% constructors
  o,i : constant
  0,1 : postfix unary
  P,M : constant
  int : binary

% operators
  #,* : infix binary
  +,. : AC
  - : infix binary
  divise : infix 2
  if_then_else : 3
  and, xor : AC
  true, false : constant
  est_nul, est_non_nul : 1
  est_sup : 2
  est_sup_strict : 2
 
% variables

  x,y,z,u,v : variable

theory BR(xor,false,and,true) 
unification theory BR(xor,false,and,true) 

axioms

  est_nul(o) = true;
  est_nul(i) = false;
  (o)0 = o;
  (o)1 = i;
  x+o = x;
  x - o = x;
  x.i = x;
  est_nul((x)1) = false;
  est_sup(x,o) = true;
  o - x = o;
  x.o = o;
  if_then_else(true,x,y) = x;
  if_then_else(false,x,y) = y;
  est_nul((x)0) = est_nul(x);
  est_sup(o,x) = est_nul(x);
  est_sup(i,i) = true;
  i - i = o;
  est_nul(x+x) = est_nul(x);
  est_nul(x+i) = false;
  est_sup((x)1,i) = true;
  i - (x)0 = i;
  i - (x)1 = o;
  i+i = (i)0;
  est_sup(i,(x)1) = est_nul(x);
  est_sup(i,(x)0) = est_nul(x);
  i+(x)0 = (x)1;
  (x)1 - i = (x)0;
  est_nul(x+(y)1) = false;
  est_sup((x)1,(y)1) = est_sup(x,y);
  x.(y)0 = (x.y)0;
  est_sup((x)0,i) = est_sup(x,i);
  est_sup((x)0,(y)0) = est_sup(x,y);
  est_sup((x)1,(y)0) = est_sup(x,y);
  i+(x)1 = (x+i)0;
  x.(y)1 = x+(x.y)0;
  est_nul(x+(y)0) = est_nul(x+y);
  est_nul(x) and est_nul(y) = est_nul(x+y);
  (x)0+(y)0 = (x+y)0;
  (x)1+(y)0 = (x+y)1;
  (x)0 - (y)0 = (x - y)0;
  (x)1 - (y)0 = (x - y)1;
  est_sup((x)0,(y)1) = est_sup(x,y+i);
  est_nul(x+y+y) = est_nul(x+y);
  (x)1+(y)1 = (x+y+i)0;
  (x)0 - i = if_then_else(est_nul(x),o,(x - i)1);
  (x)0 - (y)1 = if_then_else(est_nul(x),o,(x - (y+i))1);

% entiers signes

  int(P,x) # int(P,y) = int(P,x+y);
  int(M,x) # int(M,y) = int(M,x+y);
  int(P,x) # int(M,y) = if_then_else(est_sup(x,y),int(P,x-y),int(M,y-x));
  int(M,y) # int(P,x) = if_then_else(est_sup(x,y),int(P,x-y),int(M,y-x));

  int(P,x) * int(P,y) = int(P,x.y);
  int(P,x) * int(M,y) = int(M,x.y);
  int(M,x) * int(P,y) = int(M,x.y);
  int(M,x) * int(M,y) = int(P,x.y);

order

lexico(
 rpo ( P=M,
                                          + < .                      < *,
                              o=i < 0=1 < + < -                      < #,
                               if_then_else < -,
        false = true < est_nul= est_non_nul < -,
                             + < est_sup,
                      est_nul < est_sup = est_sup_strict < xor = and < #,
                                                                 int < #,
                                                                 int < *;
      # mul, + mul, est_sup lrlex, - lrlex);
        rpo (est_sup < est_sup_strict, P=M,0= 1,o=i);
        rpo (P<M,0< 1,o<i);
        interactive )
problems

% 89 * 77, ca doit donner 1(0(1(0(0(0(1(1(0(1(0(1(1(d)))))=6853
%  reduce (1(0(0(1(1(0(1(d)))))))) * (1(0(1(1(0(0(1(d)))))))) ;
unify if_then_else(est_nul(x) and est_nul(z),int(P,o),int(M,x+z))=
      if_then_else(true,y,u);

end
 
