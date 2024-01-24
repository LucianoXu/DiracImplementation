%***************************************************************************
%
% Chameleons problem
%
% Project:    Cime
% Author(s):  Claude Marché
% Created on: 08 mar 93
%
% Last modified by $Author: marche $ 
% File name: $Source: /users/demons/demons/master-sources-repository/cime/examples/others/chameleons-problem-ACU.nc,v $
% $Revision: 1.1 $ 
% Last modified on $Date: 1997/03/14 13:56:56 $
% 
%***************************************************************************

operators
  & : AC
  Red,Green,Blue,0 : constant

theory ACU(&,0)
% unification theory ACU(&,0)

axioms
  Red & Blue = Green & Green;
  Red & Green = Blue & Blue;
  Green & Blue  = Red & Red;

order 
  rpo(Red>Blue>Green > & ; & mul)

problems
  Red & Red & Red & Red & Blue & Blue & Blue & Green & Green =
  Red & Red & Red & Red & Red & Red & Red & Red & Red;
  Red & Red & Red & Red & Blue & Blue & Blue & Green & Green =
  Blue & Blue & Blue & Blue & Blue & Blue & Blue & Blue & Blue;
  Red & Red & Red & Red & Blue & Blue & Blue & Green & Green =
  Green & Green & Green & Green & Green & Green & Green & Green & Green;

end

