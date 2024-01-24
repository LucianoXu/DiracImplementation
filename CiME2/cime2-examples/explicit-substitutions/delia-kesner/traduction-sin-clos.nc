operators

    sh,id: constant
    comp: binary
    ts,li: unary
    a,b,c,s,t,u,n:variable

axioms

comp(li(a),li(b))                  = li(comp(a,b));
comp(comp(s,t),u)                  = comp(s,comp(t,u)); 
comp(sh,ts(a))                     = id;
comp(sh,li(s))                     = comp(s, sh); 
comp(sh,comp(li(s),t))             = comp(s, comp(sh,t));
comp(li(s),comp(li(t),u))          = comp(li(comp(s,t)),u);
comp(id,s)                         = s;
comp(s,id)                         = s;
li(id)                             = id; 
comp(sh,comp(ts(a),b))             = b;

order   interactive

end





