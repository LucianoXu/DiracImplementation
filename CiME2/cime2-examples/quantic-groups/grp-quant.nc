%***************************************************************************
%
% Groupes Quantiques
% (Probleme de Guichardet)
% cas general
% 
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        grp-quant.nc
% Created on:              22 nov 93
% Last modified on: 22 nov 93
%
%***************************************************************************

operators

% booleens
  true, false : constant
  cond : 3

% entiers
  u : constant
  s : unary
  eq : binary
  ge,geq,le,leq : binary

% anneau non commutatif plus une constante t
  .,* : binary
  + : AC
  0,1,t : constant
  - : unary
  pm2mp2,p2,pm2 : unary

  x,y,z : variable
  i,j,k,l : variable

% generateurs X(i,j)
  X : binary

theory 
  AU(.,1)
  AG(+,0,-)
  AU(*,1)

axioms
% definition de cond

  cond(true,x,y) = x;
  cond(false,x,y) = y;

% entiers
  u eq u = true;
  s(x) eq u = false;
  u eq s(x) = false;
  s(x) eq s(y) = x eq y;

  x geq u = true;
  u geq s(x) = false;
  s(x) geq s(y) = x geq y;

  u ge x = false;
  s(x) ge u = true;
  s(x) geq s(y) = x geq y;

  u leq x = true;
  s(x) leq u = false;
  s(x) leq s(y) = x leq y;

  x le u = false;
  u le s(y) = true;
  s(x) le s(y) = x le y;

% t commute
  X(x,y).t = t.X(x,y);
  X(x,y).p2(t) = p2(t).X(x,y);
  X(x,y).pm2(t) = pm2(t).X(x,y);
  x*t = t.x;
  t*x = t.x;

  pm2mp2(t) = pm2(t) + -(p2(t));


  p2(t).t = t.p2(t);
  pm2(t).t = t.pm2(t);
  pm2(t).p2(t) = 1; 
  p2(t).pm2(t) = 1;
 
  x.(y+z) = (x.y) + (x.z);
  (x+y).z = (x.z) + (y.z);
  x.0 = 0;
  0.x = 0;
  x.-(y) = -(x.y);
  -(x).y = -(x.y);

  x*(y+z) = (x*y) + (x*z);
  (x+y)*z = (x*z) + (y*z);
  x*0 = 0;
  0*x = 0;
  x*-(y) = -(x*y);
  -(x)*y = -(x*y);


% regles 

  X(i,j)*X(k,l) = 
   cond (s(j) le k,
     X(k,l).X(i,j),
     cond (s(j) eq k,
       (p2(t).X(k,l).X(i,j)) + (t.X(i,l)),
       cond (i le k,
	 cond (j le l,
           (X(k,l).X(i,j)) + (pm2mp2(t).X(k,j).X(i,l)),
           cond (j eq l,
             pm2(t).X(k,l).X(i,j),
             X(k,l).X(i,j))),
         cond (i eq k,
	   cond (j le l,
             pm2(t).X(k,l).X(i,j),
             X(i,j).X(k,l)),
         X(i,j).X(k,l))))) ;


order 
 rpo( * > X >  
      pm2mp2 > pm2 > p2 > t > 1,
      1 > . > - > + > 0,
      * > s > u,
      leq > eq,
      le > eq,
      ge > eq,
      geq > eq,
      cond > true,
      cond > false,
      eq > true,
      eq > false,
      u > cond,
      u > le,
      u > leq,
      u > ge,
      u > geq     
      ; 
      . lrlex, + mul, * lrlex
   )

end

