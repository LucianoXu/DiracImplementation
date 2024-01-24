% Example of a precedence which is not admissible for mapo.
% There are two different constants (0 and 1) inferior to the AC symbol +.

operators
  +,*	: AC
  I,J,K	: 1
  0,1	: constant

order
  mapo(+>0,*>I>J>K>+>1)

end
