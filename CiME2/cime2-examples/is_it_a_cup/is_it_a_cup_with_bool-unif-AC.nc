operators

  true, false : constant
  and, or, xor : AC
  implies : infix binary
  not : unary

  x,y : variable

theory BR(xor,false,and,true)

axioms

  not(x) = x xor true;
  x or y = (x and y) xor (x xor y); 
  x implies y = not(x) or y;

operators
  owner : binary
  cup : unary
  open_vessel : unary
  stable : unary
  liftable : unary
  part_of : binary
  iso : binary
  concavity : constant
  flat : unary
  light : unary
  color : binary
  bottom : constant
  hug : constant
  handle : constant
  base : constant
  objet : constant
  claude : constant
  hollow : constant
  white :constant

  X,Y,Z : variable

axioms

open_vessel(X) implies
  (stable(X) implies (liftable(X) implies cup(X))) = true ;

part_of(X,Y) implies
  (iso(Y,concavity) implies open_vessel(X)) = true ;

part_of(X,Y) implies
  (iso(Y,bottom) implies (flat(Y) implies stable(X))) = true; 

part_of(X,Y) implies
  (iso(Y,handle) implies (light(X) implies liftable(X))) = true ;

owner(objet,claude) = true ;
part_of(objet,hollow)= true ;
part_of(objet,base)= true ;
part_of(objet,hug)= true ;
iso(hollow,concavity)= true ;
iso(base,bottom)= true ;
iso(hug,handle)= true ;
flat(base)= true ;
light(objet)= true ;
color(objet,white)= true ;

order 

  rpo(  implies > xor,
	implies > and,
	implies > true,
	not > xor,
	not > true,
	or > xor,
        or > and,
       owner > true,
       part_of > true,
       iso > true,
       flat > true,
       light > true,
       color > true,
       liftable > true,
       stable > true,
       open_vessel > true,
       cup > true)

conjectures

  cup(objet) = true ;
  
end
