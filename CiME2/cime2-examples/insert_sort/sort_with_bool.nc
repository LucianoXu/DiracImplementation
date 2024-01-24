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

operators

% booleens  
  true, false : constant
  and, or, xor : AC
  if_then_else : 3

% entiers
  0,1,2,3,4,5,6,7 : constant
  s : unary
  eq : infix commutative
  le : infix binary

% listes
  nil : constant
  . : infix binary
  mem : binary
  a,b,c :constant
  append : binary

% tris
  sorted : unary
  sort : unary
  insert : binary
  is_perm : binary
  is_perm_aux : 3

% variables
  x,y,z : variable
  l1,l2,l3 : variable
  x1,x2 : variable

theory BR(xor,false,and,true)
unification theory  BR(xor,false,and,true)

axioms

% booleens
  x or y = (x and y) xor (x xor y); 
  if_then_else(true,x,y) = x;
  if_then_else(false,x,y) = y;

% entiers  
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

% listes    
  mem(x,nil) = false;
  mem(x,y.z) = (x eq y) or (mem(x,z));
 
  append(nil,l2) = l2;
  append(x1.l1,l2) = x1.append(l1,l2);

% tris

  sorted(nil) = true;
  sorted(x.nil) = true;
  sorted(x.(y.z)) = (x le y) and sorted(y.z);

  sort(nil) = nil;
  sort(x.y) = insert(x,sort(y));

  insert(x,nil) = x.nil;
  insert(x,y.z) = if_then_else(x le y, x.(y.z), y.insert(x,z));


  is_perm(l1,l2) = is_perm_aux(l1,l2,nil);

  is_perm_aux(nil,nil,nil) = true;
  is_perm_aux(x1.l1,x2.l2,l3) = 
	if_then_else(x1 eq x2,
		is_perm_aux(l1,append(l2,l3),nil),
		is_perm_aux(x1.l1,l2,x2.l3));
  is_perm_aux(nil,x2.l2,l3) = false;
  is_perm_aux(x1.l1,nil,l3) = false;

order
 rpo( 7>6>5>4>3>2>1>s>0,
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
	is_perm > is_perm_aux > if_then_else,
	is_perm_aux > append,
	is_perm_aux > eq,
	is_perm > nil,
	append > .;
	is_perm_aux lrlex
      )
 % interactive

problems
  
  reduce mem(7,1.(2.(x.(3.nil)))) ;
  reduce mem(7,1.(2.(x.(3.(y.nil))))) ;
  reduce mem(7,1.(2.(x.(7.(y.nil))))) ;

  reduce sort(7.(1.(2.(6.(3.nil)))));
  reduce sort(1.(2.(x.(3.nil))));

  reduce sorted(7.(1.(2.(6.(3.nil)))));
  reduce sorted(1.(2.(x.(3.nil))));

  reduce is_perm(1.(2.(3.nil)),3.(2.(1.nil)));

  reduce is_perm(1.(2.(3.nil)),3.(2.(4.nil)));

end

