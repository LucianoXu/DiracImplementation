%***************************************************************************
%
% lists
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo5.nc
% Created on:              1 avr 93
% Last modified on: 1 avr 93
%
%***************************************************************************

operators

% booleens  
  true, false : constant
  and, or : AC
  if_then_else : 3

% listes
  nil : constant
  . : infix binary
  a,b,c :constant
  append : binary

  is_perm : binary
  is_perm_aux : 3

% ensembles
  vide : constant
  singl : unary
  union : AC

  set_of : unary
  eq : binary
  
% variables
  x,y,z : variable
  l1,l2,l3 : variable
  x1,x2,x3 : variable
  l,m:variable

theory  
  ACU(or,false)
  ACU(and,true)
  ACU(union,vide)

axioms

% booleens
  true or x = true;
  false and x = false;  
  if_then_else(true,x,y) = x;
  if_then_else(false,x,y) = y;

% listes    

%  append(nil,l2) = l2;
%  append(x1.l1,l2) = x1.append(l1,l2);

% tris

%  is_perm(nil,nil) = true ;
%  is_perm(x.l,nil) = false ;
%  is_perm(nil,x.l) = false ;
%  is_perm(x.l,x.m) = is_perm(l,m) ;
%  is_perm(x.(y.l),y.(x.m)) = is_perm(l,m) ;

%  is_perm(l1,l2) = is_perm_aux(l1,l2,nil);

% is_perm_aux l1 l2 l3 = true si l1 est une permutation de append(l2,l3)

%  is_perm_aux(nil,nil,nil) = true;
%  is_perm_aux(x1.l1,nil,nil) = false;
%  is_perm_aux(nil,x2.l2,l3) = false;
%  is_perm_aux(nil,l2,x3.l3) = false;
%  is_perm_aux(x.l1,x.l2,l3) = is_perm_aux(l1,l2,l3);
%  is_perm_aux(x.l1,l2,x.l3) = is_perm_aux(l1,l2,l3);
%  is_perm_aux(l1,l2,l3) = is_perm_aux(l1,append(l2,l3),nil);
%  is_perm_aux(l1,l2,l3) = is_perm_aux(l1,nil,append(l2,l3));

  set_of(nil) = vide ; 
  set_of(x.l) = union (singl(x),set_of(l)) ;

  eq(x,x) = true ;
%  eq(union(x,y),union(x,z)) = eq(y,z) ;
%  eq(vide,singl(x)) = false ;
%  eq(vide,union(singl(x),y)) = false ;

%  eq(singl(x),vide) = false ;
%  eq(union(singl(x),y),vide) = false ;

%  eq(union(x,y),x) = eq(y,nil) ;
%  eq(x,union(x,y)) = eq(nil,y) ;

  is_perm(l,m) = eq(set_of(l),set_of(m)) ;

order
 lexico ( rpo( 	eq > true, eq > false,
		set_of > union > vide, 
		is_perm > eq, 
		is_perm > set_of, 
		set_of > singl) ;
  interactive)


problems
  
  reduce is_perm(x.(y.(z.nil)),z.(y.(x.nil)));

  reduce is_perm(x.(y.(z.nil)),z.(y.(l.nil)));

  reduce is_perm(x.(y.(z.nil)),z.(y.nil));

  reduce is_perm(true.nil,false.nil);

end

