
operators

% naturals

  1 : constant       % nat
  Suc : unary        % nat -> nat

  +   : infix binary % nat, nat -> nat

% terms & subs

  L : constant       % term
  Lbd : unary        % term -> term
  App : binary       % term, term -> term
  Sub : binary       % term, subs -> term
  Id : constant      % subs
  Sh : binary        % nat, subs -> subs
  Lf : unary         % subs -> subs
  * : infix binary   % term, subs -> subs
  o : infix binary   % subs, subs -> subs


  x,y,z,z1,w : variable

theory empty

axioms

% naturals

  1 + y = Suc(y) ;
  Suc(x) + y = Suc(x + y) ;
  y + 1 = Suc(y);
  x + Suc(y) = Suc(x + y);
  x + (y + z) = (x + y) + z;

% substitution

  % Ass
  (x o y) o z = x o (y o z) ;

  % IdL
  x o Id = x  ;

  % IdR
  Id o x = x ;

  % LiftId
  Lf(Id) = Id;

  % IdEnv
  Sub(x,Id) = x;

  % Clos
  Sub(Sub(x,y),z) = Sub(x,y o z);

  % Fvar
  Sub(L,x * y) = x;

  % FVarlift1
  Sub(L,Lf(x)) = L;

  % FVarlift2
  Sub(L,Lf(x) o y) = Sub(L,y);

  % FVarshift1
  Sub(L,Sh(y,Lf(x))) = Sub(L,Sh(y,Id));

  % FVarshift2
  Sub(L, Sh(y, Lf(x)) o z) = Sub(L, Sh(y, Id) o z)  ;

  % IdShift1
  x o Sh(y,Id) = Sh(y,x);

  % IdShift2
  x o (Sh(y,Id) o z) = Sh(y,x) o z;

  % ShiftShift
  Sh(x,Sh(y,z)) = Sh(x + y,z);

  % ShiftAss
  Sh(x, y o z) = y o Sh(x, z);

  % ShiftLift1
  Sh(1,x) o Lf(y) = x o Sh(1,y);

  % ShiftLift2
  Sh(1,x) o (Lf(y) o z) = x o (Sh(1,y) o z) ;

  % ShiftShiftLift1
  Sh(1,x) o Sh(z,Lf(y)) = x o Sh(Suc(z),y);

  % ShiftShiftLift2
  Sh(1, x) o (Sh(z, Lf(y)) o z1) = x o (Sh(Suc(z), y) o z1);

  % ShiftLift1+1
  Sh(Suc(x),y) o Lf(z) = Sh(x,y) o Sh(1,z) ;

  % ShiftLift2+1
  Sh(Suc(x),y) o (Lf(z) o w) = Sh(x,y) o (Sh(1,z) o w);

  % ShiftShiftLift1+1
  Sh(Suc(x),y) o Sh(w,Lf(z)) = Sh(x,y) o Sh(Suc(w),z);

  % ShiftShiftLift2+1
  Sh(Suc(x), y) o (Sh(w, Lf(z)) o z1) = Sh(x, y) o (Sh(Suc(w), z) o z1);

  % Lift1
  Lf(x) o Lf(y) = Lf(x o y);

  % Lift2
  Lf(x) o (Lf(y) o z) = Lf(x o y) o z;

  % LiftShift1
  Lf(x) o Sh(y,Lf(z)) = Sh(y,Lf(x o z)) ;

  % LiftShift2
  Lf(x) o (Sh(y, Lf(z)) o z1) = Sh(y, Lf(x o z)) o z1 ;
 
  % App
  Sub(App(x, y), z) = App(Sub(x, z), Sub(y, z));

  % Lbd
  Sub(Lbd(x),y) = Lbd(Sub(x, Lf(y)));

  % Shift
  Sh(1,x) o (y * z) = x o z;

  % Shift+1
  Sh(Suc(x),y) o (z * w) = Sh(x,y) o w;

  % MapEnv1
  (x * y) o z = Sub(x,z)*(y o z);

  % MapEnv2
  Sh(y,x * z) = Sub(x,Sh(y,Id)) * Sh(y,z);

  % LiftMap
  Lf(x) o (y * z) = y * (x o z);

  % Beta
  App(Lbd(x), y) = Sub(x, y * Id);

order
  interactive

end






