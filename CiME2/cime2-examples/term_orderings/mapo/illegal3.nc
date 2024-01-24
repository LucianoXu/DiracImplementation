% Example of a precedence which is not admissible for mapo.
% The AC symbol @ is between the AC symbols * and +.

operators
  +,*,@ : AC
  I,J,K : 1
  g	: 2
  1	: constant

order
  mapo(g>*>I,I>@>J,J>+>K>1)

end
