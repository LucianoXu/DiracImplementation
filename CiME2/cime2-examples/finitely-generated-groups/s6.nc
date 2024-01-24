%***************************************************************************
%
%
% Comple'tion du groupe $S_6$
%
%
%***************************************************************************

operators
  . : infix binary
  I : unary
  e : constant
  x,y,z : variable
  a1,a2,a3,a4,a5 : constant

axioms
  x.(y.z) = (x.y).z;
  x.e = x;
  e.x = x;
  x.I(x) = e;
  I(x).x = e;
  a1.a1 = e;
  a2.a2 = e;
  a3.a3 = e;
  a4.a4 = e;
  a5.a5 = e;
  ((a1.a2).(a1.a2)).(a1.a2) = e;
  ((a2.a3).(a2.a3)).(a2.a3) = e;
  ((a3.a4).(a3.a4)).(a3.a4) = e;
  ((a4.a5).(a4.a5)).(a4.a5) = e;
  a1.a3 = a3.a1;
  a1.a4 = a4.a1;
  a1.a5 = a5.a1;
  a2.a4 = a4.a2;
  a2.a5 = a5.a2;
  a3.a5 = a5.a3;

order
  rpo(a1>a2>a3>a4>a5>I>e>. ; . lrlex)

end

resultats:

Resultat :
{.(a2,.(a3,.(a4,.(a5,.(a2,z))))) -> .(a3,.(a2,.(a3,.(a4,.(a5,z))))),
.(a1,.(a2,.(a3,.(a4,.(a5,a1))))) -> .(a2,.(a1,.(a2,.(a3,.(a4,a5))))),
.(a1,.(a2,.(a3,.(a4,.(a1,z))))) -> .(a2,.(a1,.(a2,.(a3,.(a4,z))))),
.(a3,.(a4,.(a5,.(a3,z)))) -> .(a4,.(a3,.(a4,.(a5,z)))),
.(a1,.(a2,.(a3,.(a4,a1)))) -> .(a2,.(a1,.(a2,.(a3,a4)))),
.(a1,.(a2,.(a3,.(a1,z)))) -> .(a2,.(a1,.(a2,.(a3,z)))),
.(a2,.(a3,.(a4,.(a5,a2)))) -> .(a3,.(a2,.(a3,.(a4,a5)))),
.(a2,.(a3,.(a4,.(a2,z)))) -> .(a3,.(a2,.(a3,.(a4,z)))),
.(a2,.(a3,.(a4,a2))) -> .(a3,.(a2,.(a3,a4))),
.(a2,.(a3,.(a2,z))) -> .(a3,.(a2,.(a3,z))),
.(a1,.(a2,.(a3,a1))) -> .(a2,.(a1,.(a2,a3))),
.(a1,.(a2,.(a1,z))) -> .(a2,.(a1,.(a2,z))),
.(a4,.(a5,.(a4,z))) -> .(a5,.(a4,.(a5,z))),
.(a3,.(a4,.(a5,a3))) -> .(a4,.(a3,.(a4,a5))),
.(a3,.(a4,.(a3,z))) -> .(a4,.(a3,.(a4,z))),
.(a3,.(a4,a3)) -> .(a4,.(a3,a4)),
.(a1,.(a2,a1)) -> .(a2,.(a1,a2)),
.(a1,.(a5,z)) -> .(a5,.(a1,z)),
.(a1,.(a4,z)) -> .(a4,.(a1,z)),
.(a1,.(a3,z)) -> .(a3,.(a1,z)),
.(a2,.(a5,z)) -> .(a5,.(a2,z)),
.(a2,.(a4,z)) -> .(a4,.(a2,z)),
.(a3,.(a5,z)) -> .(a5,.(a3,z)),
.(.(x,y),z) -> .(x,.(y,z)),
.(a2,.(a3,a2)) -> .(a3,.(a2,a3)),
.(a4,.(a5,a4)) -> .(a5,.(a4,a5)),
I(.(z,y)) -> .(I(y),I(z)),
.(y,.(I(y),z)) -> z,
.(I(z),.(z,y)) -> y,
.(a3,.(a3,z)) -> z,
.(a5,.(a5,z)) -> z,
.(a2,.(a2,z)) -> z,
.(a2,a4) -> .(a4,a2),
.(a2,a5) -> .(a5,a2),
.(a3,a5) -> .(a5,a3),
.(a1,a3) -> .(a3,a1),
.(a1,a4) -> .(a4,a1),
.(a1,a5) -> .(a5,a1),
.(a1,.(a1,z)) -> z,
.(a4,.(a4,z)) -> z,
.(x,I(x)) -> e,
.(I(x),x) -> e,
.(a5,a5) -> e,
.(a3,a3) -> e,
.(a1,a1) -> e,
.(e,x) -> x,
.(x,e) -> x,
.(a2,a2) -> e,
I(I(z)) -> z,
.(a4,a4) -> e,
I(a1) -> a1,
I(e) -> e,
I(a4) -> a4,
I(a3) -> a3,
I(a5) -> a5,
I(a2) -> a2,
.(a1,.(a2,.(a3,.(a4,.(a5,.(a1,z)))))) -> .(a2,.(a1,.(a2,.(a3,.(a4,.(a5,z))))))} (57 regles)

Nombre d'appels au filtrage etendu  : 0
Nombre d'appels au filtrage general : 0
Nombre d'appels reussis             : 0
Nombre d'appels au filtrage AC     : 1146694
Nombre d'appels reussis            : 6170 (0%)
Nombre d'appels a l'unification AC : 12535
Nombre de solutions trouvees       : 1764 (0 en moyenne)

Resolution des problemes :
I(.(x,y)) = .(I(x),I(y)) est fausse (formes normales .(I(y),I(x)) et .(I(x),I(y)))
Temps utilisateur : 1023.120 s
Temps syste`me : 12.550 s


resultats obtenus sur reve:

Systeme canonique:

 1.   [0] x . e -> x
 2.   [0] e . x -> x
 3.   [0] x . I(x) -> e
 4.   [0] I(x) . x -> e
 5.   [0] I(e) -> e
 6.   [0] (x . y) . z -> x . (y . z)
 7.   [0] x . (I(x) . z) -> z
 8.   [0] I(y) . (y . z) -> z
 9.   [0] I(I(x)) -> x
10.   [0] I(y . z) -> I(z) . I(y)
11.   [0] a1 . a1 -> e
12.   [0] a1 . (a1 . z) -> z
13.   [0] I(a1) -> a1
14.   [0] a2 . a2 -> e
15.   [0] a2 . (a2 . z) -> z
16.   [0] I(a2) -> a2
17.   [0] a3 . a3 -> e
18.   [0] a3 . (a3 . z) -> z
19.   [0] I(a3) -> a3
20.   [0] a4 . a4 -> e
21.   [0] a4 . (a4 . z) -> z
22.   [0] I(a4) -> a4
23.   [0] a5 . a5 -> e
24.   [0] a5 . (a5 . z) -> z
25.   [0] I(a5) -> a5
26.   [0] a1 . a3 -> a3 . a1
27.   [0] a1 . a4 -> a4 . a1
28.   [0] a1 . a5 -> a5 . a1
29.   [0] a2 . a4 -> a4 . a2
30.   [0] a2 . a5 -> a5 . a2
31.   [0] a3 . a5 -> a5 . a3
32.   [0] a3 . (a5 . z) -> a5 . (a3 . z)
33.   [0] a2 . (a5 . z) -> a5 . (a2 . z)
34.   [0] a1 . (a4 . z) -> a4 . (a1 . z)
35.   [0] a1 . (a3 . z) -> a3 . (a1 . z)
36.   [0] a2 . (a4 . z) -> a4 . (a2 . z)
37.   [0] a1 . (a5 . z) -> a5 . (a1 . z)
38.   [0] a2 . (a3 . a2) -> a3 . (a2 . a3)
39.   [0] a3 . (a4 . a3) -> a4 . (a3 . a4)
40.   [0] a1 . (a2 . a1) -> a2 . (a1 . a2)
41.   [0] a4 . (a5 . a4) -> a5 . (a4 . a5)
42.   [0] a2 . (a3 . (a4 . a2)) -> a3 . (a2 . (a3 . a4))
43.   [0] a2 . (a3 . (a2 . z)) -> a3 . (a2 . (a3 . z))
44.   [0] a3 . (a4 . (a5 . a3)) -> a4 . (a3 . (a4 . a5))
45.   [0] a3 . (a4 . (a3 . z)) -> a4 . (a3 . (a4 . z))
46.   [0] a4 . (a5 . (a4 . z)) -> a5 . (a4 . (a5 . z))
47.   [0] a1 . (a2 . (a1 . z)) -> a2 . (a1 . (a2 . z))
48.   [0] a1 . (a2 . (a3 . a1)) -> a2 . (a1 . (a2 . a3))
49.   [0] a3 . (a4 . (a5 . (a3 . z))) -> a4 . (a3 . (a4 . (a5 . z)))
50.   [0] a2 . (a3 . (a4 . (a2 . z))) -> a3 . (a2 . (a3 . (a4 . z)))
51.   [0] a2 . (a3 . (a4 . (a5 . a2))) -> a3 . (a2 . (a3 . (a4 . a5)))
52.   [0] a1 . (a2 . (a3 . (a1 . z))) -> a2 . (a1 . (a2 . (a3 . z)))
53.   [0] a1 . (a2 . (a3 . (a4 . a1))) -> a2 . (a1 . (a2 . (a3 . a4)))
54.   [0] a2 . (a3 . (a4 . (a5 . (a2 . z)))) ->
          a3 . (a2 . (a3 . (a4 . (a5 . z))))
55.   [0] a1 . (a2 . (a3 . (a4 . (a1 . z)))) ->
          a2 . (a1 . (a2 . (a3 . (a4 . z))))
56.   [0] a1 . (a2 . (a3 . (a4 . (a5 . a1)))) ->
          a2 . (a1 . (a2 . (a3 . (a4 . a5))))
57.   [0] a1 . (a2 . (a3 . (a4 . (a5 . (a1 . z))))) ->
          a2 . (a1 . (a2 . (a3 . (a4 . (a5 . z)))))

Your system is complete!

Knuth-Bendix runtime:
  Total: 14:36.
    Unification: 2:06.72
    Rewriting: 11:02.10
    Ordering: 33.70
    Overhead: 54.40
  Computed 751 critical pairs and ordered 124 equations into rules.
 



