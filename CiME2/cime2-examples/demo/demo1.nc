%***************************************************************************
%
%
% Comple'tion des came'le'ons - Demo 1 : ordre interactif 
%
%
% Project:                Cime
% Author(s):             Claude March\'e
%
% File name:        demo1.nc
% Created on:              08 mar 93
% Last modified on: 08 mar 93
%
%***************************************************************************

operators
  & : AC
  Rouge,Vert,Bleu : constant

axioms
  Rouge & Bleu = Vert & Vert;
  Rouge & Vert = Bleu & Bleu;
  Vert & Bleu  = Rouge & Rouge;

order  rpo( Rouge>Bleu>Vert > & ; & mul)
%interactive

problems
  Rouge & Rouge & Rouge & Rouge & Bleu & Bleu & Bleu & Vert & Vert =
  Rouge & Rouge & Rouge & Rouge & Rouge & Rouge & Rouge & Rouge & Rouge;

  Rouge & Rouge & Rouge & Rouge & Bleu & Bleu & Bleu & Vert & Vert =
  Bleu & Bleu & Bleu & Bleu & Bleu & Bleu & Bleu & Bleu & Bleu;

  Rouge & Rouge & Rouge & Rouge & Bleu & Bleu & Bleu & Vert & Vert =
  Vert & Vert & Vert & Vert & Vert & Vert & Vert & Vert & Vert;

end

