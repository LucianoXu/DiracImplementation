%***************************************************************************
%
% sort
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo5.nc
% Created on:              1 avr 93
% Last modified on: 1 avr 93
%
%***************************************************************************

%=========
% booleens  
%=========

operators

  true, false : constant
  and, or, xor : AC
  if_then_else : 3
  x,y,z : variable

 theory BR(xor,false,and,true)
% unification theory  BR(xor,false,and,true)

%axioms

%  x xor false = x ;
%  x and true = x ;
%  x and false = false ;
%  x xor x = false ;
%  x and x = x ;
%  x and (y xor z) = (x and y) xor (x and z) ;

  x or y = (x and y) xor (x xor y); 
  if_then_else(true,x,y) = x;
  if_then_else(false,x,y) = y;


%========
% entiers
%========

operators

  0,1,2,3,4,5,6,7 : constant
  s : unary
  eq : infix commutative
  le : infix binary

axioms

  1 = s(0);
  2 = s(1);
  3 = s(2);
  4 = s(3);
  5 = s(4);
  6 = s(5);
  7 = s(6);

  0 eq 0 = true;
  0 eq s(y) = false;
  s(x) eq s(y) = x eq y;

  0 le x = true;
  s(x) le 0 = false;
  s(x) le s(y) = x le y;


%=======
% listes
%=======

operators

  nil : constant
  . : infix binary
  mem : binary
  append : binary
  l1,l2,l3 : variable
  x1,x2 : variable

axioms

  mem(x,nil) = false;
  mem(x,y.z) = (x eq y) or (mem(x,z));
 
  append(nil,l2) = l2;
  append(x1.l1,l2) = x1.append(l1,l2);

%=====
% bags
%=====

operators

  empty : constant
  singl : unary
  union : AC

  eq_bag : infix commutative
  bag_of_list : unary

% theory ACU(union,empty)
% unification theory  ACU(union,empty)

axioms

  x union empty = x;

  x eq_bag x = true;
  singl(x) eq_bag singl(y) = x eq y;
  singl(x) eq_bag empty = false;
  (x union y) eq_bag (x union z) = y eq_bag z;

  bag_of_list(nil) = empty;
  bag_of_list(x.y) = singl(x) union bag_of_list(y);

%=======================
% specification d'un tri
%=======================

operators

  sorted : unary
  is_perm : binary

axioms

  sorted(nil) = true;
  sorted(x.nil) = true;
  sorted(x.(y.z)) = (x le y) and sorted(y.z);

  is_perm(l1,l2) = bag_of_list(l1) eq_bag bag_of_list(l2);

%=====================
% le tri par insertion
%=====================

operators

  sort : unary
  insert : binary

axioms

  sort(nil) = nil;
  sort(x.y) = insert(x,sort(y));

  insert(x,nil) = x.nil;
  insert(x,y.z) = if_then_else(x le y, x.(y.z), y.insert(x,z));





order
 rpo( 7>6>5>4>3>2>1>s>0,
        true > and > xor > false,
	mem > false,
        sorted > true,
	le > true,
	if_then_else > true,
	if_then_else > false,
	insert > . > nil,
	eq > true,
	sort > insert,
	eq > false,
	mem > eq,
	mem > or,
	or > xor,
        or > and,
        sorted > and,
	sorted > le > false,
	insert > if_then_else,
	insert > le,
	is_perm > if_then_else,
	is_perm > nil,
	is_perm > eq_bag,
	is_perm > bag_of_list,
	eq_bag > true,
	eq_bag > false,
        eq_bag > eq,
	bag_of_list > union > empty,
	bag_of_list > singl,
	append > .
      )
 % interactive

conjectures

  sorted(7.(1.(2.(6.(3.nil))))) = false ;
  sorted(1.(2.(3.(6.(7.nil))))) = true ;

  is_perm(1.(2.(3.nil)),3.(2.(1.nil))) = true ;
  is_perm(1.(2.(3.nil)),3.(2.(4.nil))) = false ;

  sort(7.(1.(2.(6.(3.nil))))) = 1.(2.(3.(6.(7.nil)))) ;

problems
  
  reduce sort(7.(1.(2.(6.(3.nil)))));

  reduce sorted(7.(1.(2.(6.(3.nil)))));
  reduce sorted(1.(2.(3.(6.(7.nil)))));

  reduce is_perm(7.(1.(2.(6.(3.nil)))),1.(2.(3.(6.(7.nil)))));
  reduce is_perm(7.(1.(2.(6.(3.nil)))),1.(2.(4.(6.(7.nil)))));

%  reduce mem(7,1.(2.(x.(3.nil)))) ;
%  reduce mem(7,1.(2.(x.(3.(y.nil))))) ;
%  reduce mem(7,1.(2.(x.(7.(y.nil))))) ;

%  sorted(sort(x)) = true;
 
%  sorted(sort(nil)) = true;

%  sorted(sort(a)) = true -> sorted(sort(x.a)) = true;

%  sorted(sort(x.a)) = true;

%   sorted(sort(x.nil)) = true  ;

%  sorted(sort(x.a)) = true -> sorted(sort(x.(y.a))) = true ;

%  sorted(sort(a.(b.c))) = true ;


end
