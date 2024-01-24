operators
  +,.,plus,times      : AC
  0,1,zero,one : constant
  -,minus,H        : unary
  x,y,z,t,u    : variable

theory  CR(+,0,-,.,1)  CR(plus,zero,minus,times,one)

axioms H(x+y) = H(x) plus H(y); H(x.y) = H(x) times H(y);  

order  rpo( H>1>.>->+>0, H>one>times>minus>plus>zero  )

end

