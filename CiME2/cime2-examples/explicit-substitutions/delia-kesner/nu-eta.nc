operators

    uno,sh,id,1,0: constant
    app,subst,comp,eti,ou: binary
    lambda,ts,li,suc: unary
    a,b,s,t,u,e1,e2,e3:variable

axioms

ou(0,0) = 0;
ou(0,1) = 1;
ou(1,0) = 1;
ou(1,1) = 1;

%eti(a,0)                      
%                              = eti(lambda(eti(app(eti(subst(eti(a,1),sh),1),eti(uno,0)),0)),1);
eti(subst(eti(app(eti(a,e1),eti(b,e2)),e3),s),e3)
                              = eti(app(eti(subst(eti(a,e1),s),e1),eti(subst(eti(b,e2),s),e2)),e3);
eti(subst(eti(lambda(eti(a,e1)),e2),s),e2)
                              = eti(lambda(eti(subst(eti(a,e1),li(s)),e1)),e2);
eti(subst(eti(uno,e1),ts(eti(a,e2))),e1)
                              = eti(a,ou(e1,e2));
eti(subst(eti(suc(a),e1),ts(b)),e1)
                              = eti(a,e1);
eti(subst(eti(uno,e1),li(s)),e1)
                              = eti(uno,e1); 
eti(subst(eti(suc(a),e1),li(b)),e1)
                              = eti(subst(eti(subst(eti(a,e1),s),e1),sh),e1);
eti(subst(eti(a,e1),sh),e1)   = eti(suc(a),e1);

order   interactive

end
