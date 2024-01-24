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
comp(li(s), li(t))                 = li(comp(s,t));
comp(li(s),comp(li(t),u))          = comp(li(comp(s,t)),u); 
comp(id,s)                         = s;
comp(s,id)                         = s;
li(id)                             = id; 
subst(a,id)                        = a; 
subst(suc(var(n)),ts(a))           = var(n);
subst(var(n),sh)                   = suc(var(n));
subst(suc(var(n)),li(s))           = subst(var(n),comp(s,sh));
subst(var(n),comp(sh,s))           = subst(suc(var(n)),s);
subst(suc(var(n)),comp(li(s),t))   = subst(var(n),comp(s,comp(sh,t)));
subst(uno,comp(ts(a),b))           = subst(a,b);
comp(sh,comp(ts(a),b))             = b;
subst(suc(var(a)),comp(ts(b),s))   = subst(var(a),s); 

order   interactive

end





