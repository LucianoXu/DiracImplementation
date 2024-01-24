operators

    uno,sh,id: constant
    app,subst,comp: binary
    lambda,ts,li: unary
    a,b,s,t,u:variable

axioms

subst(app(a,b),s)             = app(subst(a,s),subst(b,s));
subst(lambda(a),s)            = lambda(subst(a,li(s)));
subst(subst(a,s),t)           = subst(a,comp(s,t));
subst(uno,ts(a))              = a;
subst(uno,li(s))              = uno; 
subst(uno,comp(li(s),t))      = subst(uno,t);
comp(comp(s,t),u)             = comp(s,comp(t,u)); 
comp(sh,ts(a))                = id;
comp(sh,li(s))                = comp(s, sh); 
comp(sh,comp(li(s),t))        = comp(s, comp(sh,t));
comp(li(s), li(t))            = li(comp(s,t));
comp(li(s),comp(li(t),u))     = comp(li(comp(s,t)),u); 
comp(id,s)                    = s;
comp(s,id)                    = s;
li(id)                        = id; 
subst(a,id)                   = a; 
comp(ts(a),a)                 = comp(li(s),ts(subst(a,s))); 


order   interactive

end