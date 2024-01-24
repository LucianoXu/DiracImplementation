%***************************************************************************
%
% L'exemple de Siva 
%
% File name:        $Source: /users/demons/demons/master-sources-repository/cime/examples/others/siva.nc,v $
% Revision:         $Revision: 1.2 $ 
% Last modified by: $Author: marche $
% Last modified on: $Date: 1995/09/12 12:38:38 $
%
%***************************************************************************



operators
  + : AC
  c,d : constant
  x,y,x1 : variable
  0 : constant
  n : unary

axioms

  n(x + n(y) + n(x + y)) = 0;
  n(c + n(c+x1) + n(d+x1)) = 0;

order
  interactive

end


