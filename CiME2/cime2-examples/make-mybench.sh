#!/bin/sh
#
# shell script for running some benchmarks: comparison between AC-complete
# and plain E-unification
#
# $Id: make-mybench.sh,v 1.1 1997/11/26 16:24:42 contejea Exp $
#
echo " ****************************************** "
echo " Benchmarks for: "
cime  | sed -n -e 's/Welcome to\(.*\)/\1/p' 
echo " On config: " 
uname -a
echo " started at `date '+%D %T'` "
echo " ****************************************** "
echo
echo
echo "Rings theory"
echo "------------"
echo
echo 
echo "Modulo AG(+,0,-):"
cime ../examples/rings-theory/r-modulo-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), plain ACU unification:"
cime ../examples/rings-theory/r-modulo-AG-plain-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), AC-complete ACU unification:"
cime ../examples/rings-theory/r-modulo-AG-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), plain AG unification:"
cime ../examples/rings-theory/r-modulo-AG-plain-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), AC-complete AG unification:"
cime ../examples/rings-theory/r-modulo-AG-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1), AC(+) unification"
cime ../examples/rings-theory/r-modulo-AG-AU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1), plain ACU(+,0) unification"
cime ../examples/rings-theory/r-modulo-AG-AU-plain-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1), AC-complete ACU(+,0) unification"
cime ../examples/rings-theory/r-modulo-AG-AU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1), plain AG(+,0,-) unification:"
cime ../examples/rings-theory/r-modulo-AG-AU-plain-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1), AC-complete AG(+,0,-) unification:"
cime ../examples/rings-theory/r-modulo-AG-AU-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo
echo "                ******************************"
echo "                *  Commutative rings theory  *"
echo "                ******************************"
echo
echo 
echo "Modulo AG(+,0,-) and AC(.), AC(+) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AC(.), plain ACU(+,0) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-plain-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AC(.), AC-complete ACU(+,0) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AC(.), plain AG(+,0,-) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-plain-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AC(.), AC-complete AG(+,0,-) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), AC(+) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), plain ACU(+,0) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-plain-unif-ACU+ | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), AC-complete ACU(+,0) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-unif-ACU+ | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), plain ACU(+,0) ACU(.,1) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-plain-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), AC-complete ACU(+,0) ACU(.,1) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), plain AG(+,0,-) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-plain-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), AC-complete AG(+,0,-) AC(.) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), plain AG(+,0,-) ACU(.,1) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-plain-unif-AG-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), AC-complete AG(+,0,-) ACU(.,1) unification:"
cime ../examples/commutative-rings-theory/cr-modulo-AG-ACU-unif-AG-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Boolean rings theory"
echo "--------------------"
echo
echo "Modulo ACUN(+,0) and ACUI(.,1), strategy c1:"
#main -strat 1 ../examples/boolean-rings/Boolean-rings-theory-modulo-ACIN | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AC1N(+,0) and AC1I(.,1), strategy c9:"
#main -strat 9 ../examples/boolean-rings/Boolean-rings-theory-modulo-ACIN | sed -n -e '/^Result/,$ p'
echo
echo "Modulo  AG(+,0,-) ACUI(.,1)), strategy c1:"
#main -strat 1 ../examples/boolean-rings/Boolean-rings-theory-modulo-AGUI | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo  AG(+,0,-) ACUI(.,1)), strategy c9:"
#main -strat 9 ../examples/boolean-rings/Boolean-rings-theory-modulo-AGUI | sed -n -e '/^Result/,$ p'
echo 
echo
echo "Commutative rings homomorphism"
echo "---------------------"
echo
echo "Modulo AC:"
#main ../examples/commutative-rings-theory/commutative-rings-homomorphism-AC | sed -n -e '/^Result/,$ p'
echo
echo "Modulo CR:"
#main ../examples/commutative-rings-theory/commutative-rings-homomorphism | sed -n -e '/^Result/,$ p'
echo
echo "Modulo CR, AG+ACU unif:"
#main ../examples/commutative-rings-theory/commutative-rings-homomorphism-AGunif | sed -n -e '/^Result/,$ p'
echo
echo
echo "Distributive lattices"
echo "---------------------"
echo
#main ../examples/distributive-lattices/distributive-lattices | sed -n -e '/^Result/,$ p'
echo
echo
echo "A finitely generated group: the diedral group of order 5"
echo "----------------------------------"
echo
echo "Modulo nothing:"
#main ../examples/finitely-generated-groups/diedral-group-of-order-5 | sed -n -e '/^Result/,$ p'
echo
echo "Modulo G(.,1,I):"
#main ../examples/finitely-generated-groups/diedral-group-of-order-5-G | sed -n -e '/^Result/,$ p'
echo
echo
echo "A finitely generated Abelian group"
echo "----------------------------------"
echo
echo "Modulo AC(+):"
#main ../examples/finitely-generated-groups/grf3-ac | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0):"
#main ../examples/finitely-generated-groups/grf3-acu | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0), ACU unification:"
#main ../examples/finitely-generated-groups/grf3-acu-acu | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG(+,0,-):"
#main ../examples/finitely-generated-groups/grf3-ag | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG(+,0,-), ACU unification:"
#main ../examples/finitely-generated-groups/grf3-ag-ACUunif | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG(+,0,-), AG unification:"
#main ../examples/finitely-generated-groups/grf3-ag-unif-AG | sed -n -e '/^Result/,$ p'
echo
echo
echo "Grobner bases"
echo "-------------"
echo
echo "Over Z (modulo AC):"
#main ../examples/grobner-bases/simple-over-Z-AC | sed -n -e '/^Result/,$ p'
echo
echo "Over Z (modulo CR):"
#main ../examples/grobner-bases/simple-over-Z | sed -n -e '/^Result/,$ p'
echo
echo "Over Z (modulo CR, ACU unification):"
#main ../examples/grobner-bases/simple-over-Z-ACU | sed -n -e '/^Result/,$ p'
echo
echo "Over Z (modulo CR, AG and ACU unification):"
#main ../examples/grobner-bases/simple-over-Z-unif-AG-ACU | sed -n -e '/^Result/,$ p'
echo
echo
echo "Over F5 (modulo AC):"
#main ../examples/grobner-bases/over-f5-AC | sed -n -e '/^Result/,$ p'
echo
echo "Over F5 (modulo F5):"
#main ../examples/grobner-bases/over-f5 | sed -n -e '/^Result/,$ p'
echo
echo "Over F5 (modulo F5, ACU unification):"
#main ../examples/grobner-bases/over-f5-ACU | sed -n -e '/^Result/,$ p'
echo
echo "Over F5 (modulo F5, AG and ACU unification):"
#main ../examples/grobner-bases/over-f5-unif-AG-ACU | sed -n -e '/^Result/,$ p'
echo
echo " ****************************************** "
echo " finished at `date '+%D %T'` "
echo " ****************************************** "
echo