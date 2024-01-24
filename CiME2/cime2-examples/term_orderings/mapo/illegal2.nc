% Example of a precedence which is not admissible for mapo.
% The binary function symbol f is inferior to the AC-symbol *.

operators
  +,* 	: AC
  I,J,K : 1
  g	: 2
  1	: constant

order
  mapo(*>I>J>K>+>1,J>g)

end
