operators

    uno,sh,id: constant
    app,subst,comp: binary
    lambda,ts,li,suc,var: unary
    a,b,s,t,u,n:variable

axioms

subst(app(a,b),s)                  = app(subst(a,s),subst(b,s));
subst(lambda(a),s)                 = lambda(subst(a,li(s)));
subst(subst(a,s),t)                = subst(a,comp(s,t));
subst(uno,ts(a))                   = a;
subst(uno,li(s))                   = uno; 
subst(uno,comp(li(s),t))           = subst(uno,t);
comp(comp(s,t),u)                  = comp(s,comp(t,u)); 
comp(sh,ts(a))                     = id;
comp(sh,li(s))                     = comp(s, sh); 
comp(sh,comp(li(s),t))             = comp(s, comp(sh,t));
li(comp(s,t))                      = comp(li(s), li(t));
comp(li(comp(s,t)),u)              = comp(li(s),comp(li(t),u)); 
comp(id,s)                         = s;
comp(s,id)                         = s;
li(id)                             = id; 
subst(a,id)                        = a; 
subst(uno,comp(ts(a),b))           = subst(a,b);
comp(sh,comp(ts(a),b))             = b;

order   interactive

end





