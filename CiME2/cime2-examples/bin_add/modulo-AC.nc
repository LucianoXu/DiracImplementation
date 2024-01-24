%
% Specification of natural numbers with addition
%

operators

% constructors
  O : constant    % nat
  S : unary       % nat -> nat

% variables
  n,m : variable  % nat

% the unary addition

operators
  + : AC          % nat x nat -> nat
axioms
  n + O = n ;    
  n + S(m) = S(n+m) ;
  
%
% binary realization
%

operators

% a binary number is of the form B.d_1...d_n 
% where d_i is a digit

  0,1 : constant              % digit
  B : constant                % bin
  . : infix binary            % bin x digit -> bin

  and,or,xor : AC             % digit x digit -> digit
  not : unary                 % digit x digit

  d,d1,d2 : variable          % digit
  x,y,x1,y1,x2,y2 : variable  % bin

axioms
  d xor 0 = d ;
  d and 1 = d ;
  d and 0 = 0 ;
  d xor d = 0 ;
  d and d = d ;
  d and (d1 xor d2) = (d and d1) xor (d and d2) ;

  B.0 = B ;
  d1 or d2 = d1 xor d2 xor (d1 and d2) ;  
  not(d) = d xor 1 ;

operators 

  nat_of_bin : unary          % bin -> nat

axioms

  nat_of_bin(B) = O ;
  nat_of_bin(x.0) = nat_of_bin(x) + nat_of_bin(x) ;
  nat_of_bin(x.1) = nat_of_bin(x) + nat_of_bin(x) + S(O) ;

operators

  bin_add : binary            % bin x bin -> bin
  ter_add : 3                 % bin x bin x digit -> bin
  sum, carry : 3              % digit x digit x digit -> digit

  semi_sum,semi_carry : binary %  digit x digit -> digit

axioms

  bin_add(x,y) = ter_add(x,y,0) ;

  ter_add(B,B,d) = B.d ;
  ter_add(x1.d1,x2.d2,d) = 
    ter_add(x1,x2,carry(d1,d2,d)).sum(d1,d2,d) ;

%
% additionneur proprement dit
%
%  1/2 additionneur :        
%         
%          x      y
%          |  ____|
%          |_|___ |
%          | |   ||
%          and   xor
%           |     |
%           c     s
%
%  additionneur :
%
%         d1    d2
%         |     | 
%         |_____|
%         \_1/2_/
%       ____| |
%  c -or__    |     d
%         |   |_____|
%         |   \_1/2_/
%         |_____| |
%                 s

  sum(d1,d2,d) =  semi_sum(semi_sum(d1,d2),d) ;

  carry(d1,d2,d) = 
    semi_carry(d1,d2) or semi_carry(semi_sum(d1,d2),d) ;


  semi_sum(d1,d2) = d1 xor d2 ;
  semi_carry(d1,d2) = d1 and d2 ;

order
  rpo (or >  1 > and > xor > 0,
       nat_of_bin > + > S > O,
       not > 1 ,
       semi_sum > xor,
       semi_carry > and,
       bin_add > ter_add,
       bin_add > 0,
       sum > xor,
       ter_add > .,
       carry > and,
       ter_add > . > or;
       ter_add lrlex) 

conjectures
% axioms

  nat_of_bin(x) + nat_of_bin(y) =
    nat_of_bin(bin_add(x,y)) ;



end
 
