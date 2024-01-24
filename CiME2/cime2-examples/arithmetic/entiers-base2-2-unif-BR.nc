%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                      %
%                          Entiers en base 2                           %
%                                                                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

operators

% constructors
  o,i : constant
  0,1 : postfix 1
  P,M : constant
  int,couple1,couple2 : 2

% operators
  #,* : infix 2
  +,. : AC
  -,_ : infix 2
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
  est_nul((x)1) = false;
  est_nul((x)0) = est_nul(x);
  est_nul(x+x) = est_nul(x);
  est_nul(x+i) = false;
  est_nul(x+(y)1) = false;
  est_nul(x+(y)0) = est_nul(x+y);
  est_nul(x) and est_nul(y) = est_nul(x+y);
  est_nul(x+x+y) = est_nul(x+y);

  est_sup(x,o) = true;
  est_sup(o,x) = est_nul(x);
  est_sup(i,i) = true;
  est_sup((x)1,i) = true;
  est_sup(i,(x)1) = est_nul(x);
  est_sup(i,(x)0) = est_nul(x);
  est_sup((x)0,i) = est_sup(x,i);
  est_sup((x)1,(y)1) = est_sup(x,y);
  est_sup((x)0,(y)0) = est_sup(x,y);
  est_sup((x)1,(y)0) = est_sup(x,y);
  est_sup((x)0,(y)1) = est_sup(x,y+i);

  if_then_else(true,x,y) = x;
  if_then_else(false,x,y) = y;

  (o)0 = o;
  (o)1 = i;

  x+o = x;
  i+i = (i)0;
  i+(x)0 = (x)1;
  i+(x)1 = (x+i)0;
  (x)0+(y)0 = (x+y)0;
  (x)1+(y)0 = (x+y)1;
  (x)1+(y)1 = (x+y+i)0;

  x - o = x;
  o - x = o;
  i - i = o;
  i - (x)0 = i;
  i - (x)1 = o;
  (x)1 - i = (x)0;
  (x)0 - (y)0 = (x - y)0;
  (x)1 - (y)0 = (x - y)1;
  (x)0 - i = if_then_else(est_nul(x),o,(x - i)1);
  (x)0 - (y)1 = if_then_else(est_nul(x),o,(x - (y+i))1);

  x.i = x;
  x.o = o;
  x.(y)0 = (x.y)0;
  x.(y)1 = x+(x.y)0;

  int(M,o) = int(P,o);

  int(P,x) # int(M,y) = couple1(x,y);
  int(M,x) # int(P,y) = couple2(x,y);
  int(P,x) # int(P,y) = int(P,x+y);
  int(M,x) # int(M,y) = int(M,x+y);

  int(P,x) _ int(M,y) = int(P,x+y);
  int(M,x) _ int(P,y) = int(M,x+y);
  int(P,x) _ int(P,y) = couple1(x,y);
  int(M,x) _ int(M,y) = couple2(x,y);

  int(P,x)*int(P,y) = int(P,x.y);
  int(P,x)*int(M,y) = int(M,x.y);
  int(M,x)*int(P,y) = int(M,x.y);
  int(M,x)*int(M,y) = int(P,x.y);

  couple1(x,o) = int(P,x);
  couple1(o,x) = int(M,x);
  couple1((x)0,(y)0) = couple1(x,y)*int(P,(i)0);
  couple1((x)1,(y)1) = couple1(x,y)*int(P,(i)0);
  couple1(x,i) = if_then_else(est_nul(x),int(M,i),int(P,x - i));
  couple1(i,x) = if_then_else(est_nul(x),int(P,i),int(M,x - i));
  couple1((x)1,(y)0) = (couple1(x,y)*int(P,(i)0)) # int(P,i);
  couple1((x)0,(y)1) = (couple1(x,y)*int(P,(i)0)) # int(M,i);

  couple2(x,o) = int(M,x);
  couple2(o,x) = int(P,x);
  couple2((x)0,(y)0) = couple2(x,y)*int(P,(i)0);
  couple2((x)1,(y)1) = couple2(x,y)*int(P,(i)0);
  couple2(x,i) = if_then_else(est_nul(x),int(P,i),int(M,x - i));
  couple2(i,x) = if_then_else(est_nul(x),int(M,i),int(P,x - i));
  couple2((x)1,(y)0) = (couple2(x,y)*int(P,(i)0)) # int(M,i);
  couple2((x)0,(y)1) = (couple2(x,y)*int(P,(i)0)) # int(P,i);
 
order

lexico( rpo ( P=M,
                                          + < .                      < *,
                              o=i < 0=1 < + < -                      < #,
                               if_then_else < -,
        false = true < est_nul= est_non_nul < -,
                             + < est_sup,
                      est_nul < est_sup = est_sup_strict < xor = and < #,
                                                                 int < #,
                                                                int < *,
        * < couple1 = couple2 = # = _, int < 0, P < 0;
        # rllex, couple1 rllex, couple2 rllex, _ rllex,
        + mul, est_sup lrlex, - lrlex);
        rpo (est_sup < est_sup_strict, P=M,0= 1,o=i);
        rpo (P<M,0< 1,o<i);
        interactive )


%problems

% 89 * 77, ca doit donner (((((((((((((i)1)0)1)0)1)1)0)0)0)1)0)1) =6853
%  reduce (((((((i)0)1)1)0)0)1) . (((((((i)0)0)1)1)0)1);
%  reduce int(P,((i)0)1) # int(M,(i)1);

end
 
