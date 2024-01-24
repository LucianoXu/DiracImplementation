#!/bin/sh
#
# shell script for running all benchmarks
#
# $Id: make-bench.sh,v 1.25 1999/07/21 13:38:54 marche Exp $
#
echo " ****************************************** "
echo " Benchmarks for: "
../cime $*  | sed -n -e 's/Welcome to\(.*\)/\1/p' 
echo " On config: " 
uname -a
echo " started at `date '+%D %T'` "
echo " ****************************************** "
echo
echo
echo "Groups theory"
echo "-------------"
echo
echo "Modulo nothing:"
../cime $*  groups-theory/groups-theory | sed -n -e '/^Result/,$ p'
echo
echo "Modulo associativity:"
../cime $* groups-theory/groups-theory-modulo-A | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo associativity and unit:"
../cime $* groups-theory/groups-theory-modulo-AU | sed -n -e '/^Result/,$ p'
echo 
echo
echo "Abelian groups theory"
echo "---------------------"
echo
echo "Modulo AC:"
../cime $* Abelian-groups-theory/Abelian-groups-theory-modulo-AC | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU:"
../cime $*  Abelian-groups-theory/Abelian-groups-theory-modulo-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU, ACU unification:"
../cime $*  Abelian-groups-theory/Abelian-groups-theory-modulo-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo
echo "Rings theory"
echo "------------"
echo
echo "Modulo AC(+):"
../cime $* rings-theory/r | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0):"
../cime $*  rings-theory/r-modulo-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0), ACU unification:"
../cime $* rings-theory/r-modulo-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo
%echo "Modulo ACU(+,0), ACU unification (with strategy c9):"
%../cime $* -strat 9 rings-theory/r-modulo-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
%echo 
echo "Modulo ACU(+,0), systeme deja confluent:"
../cime $* -confl -strat 9 rings-theory/r-modulo-ACU-confluent | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0), ACU unification, systeme deja confluent:"
../cime $* -confl -strat 9 rings-theory/r-modulo-ACU-unif-ACU-confluent | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0) and AU(.,1):"
../cime $* rings-theory/r-modulo-ACU-AU | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0) and AU(.,1) (with strategy c4):"
../cime $* -strat 4 rings-theory/r-modulo-ACU-AU | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0) and AU(.,1) (with strategy c8):"
../cime $* -strat 8 rings-theory/r-modulo-ACU-AU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0) and AU(.,1), ACU unification:"
../cime $* rings-theory/r-modulo-ACU-AU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-):"
../cime $* rings-theory/r-modulo-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), ACU unification:"
../cime $* rings-theory/r-modulo-AG-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), AG unification:"
../cime $* rings-theory/r-modulo-AG-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1)"
../cime $* rings-theory/r-modulo-AG-AU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1), ACU unification:"
../cime $* rings-theory/r-modulo-AG-AU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and AU(.,1), AG unification:"
../cime $* rings-theory/r-modulo-AG-AU-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo
echo "                ******************************"
echo "                *  Commutative rings theory  *"
echo "                ******************************"
echo
echo "Modulo AC(+) and AC(*):"
../cime $* commutative-rings-theory/cr | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0) and ACU(.,1):"
../cime $* commutative-rings-theory/cr-modulo-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0) and ACU(.,1) (with strategy c3):"
../cime $* -strat 3 commutative-rings-theory/cr-modulo-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0) and ACU(.,1) (with strategy c9):"
../cime $* -strat 9 commutative-rings-theory/cr-modulo-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0) and ACU(.,1) (already confluent system):"
../cime $* -confl -strat 9 commutative-rings-theory/cr-modulo-ACU-confl | sed -n -e '/^Result/,$ p'
echo 
#echo "Modulo ACU(+,0) and ACU(.,1), ACU unification:"
#../cime $* commutative-rings-theory/cr-modulo-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo "Modulo ACU(+,0) and ACU(.,1), ACU unification (with strategy c2):"
../cime $* -strat 2 commutative-rings-theory/cr-modulo-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo "Modulo ACU(+,0) and ACU(.,1), ACU unification (with strategy c3):"
../cime $* -strat 3 commutative-rings-theory/cr-modulo-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0) and ACU(.,1), ACU unification (with strategy c4):"
../cime $* -strat 4 commutative-rings-theory/cr-modulo-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo ACU(+,0) and ACU(.,1), ACU unification (already confluent system):"
../cime $* -confl -strat 4 commutative-rings-theory/cr-modulo-ACU-unif-ACU-confl | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-):"
../cime $* commutative-rings-theory/cr-modulo-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), ACU unification:"
../cime $* commutative-rings-theory/cr-modulo-AG-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-), AG unification:"
../cime $* commutative-rings-theory/cr-modulo-AG-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1):"
../cime $* commutative-rings-theory/cr-modulo-AG-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), ACU unification:"
../cime $* commutative-rings-theory/cr-modulo-AG-ACU-unif-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), AG unification:"
../cime $* commutative-rings-theory/cr-modulo-AG-ACU-unif-AG | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo AG(+,0,-) and ACU(.,1), ACU and AG unification:"
../cime $* commutative-rings-theory/cr-modulo-AG-ACU-unif-AG-ACU | sed -n -e '/^Result/,$ p'
echo 
echo "Boolean rings theory"
echo "--------------------"
echo
echo "Modulo ACUN(+,0) and ACUI(.,1), strategy c1:"
../cime $* -strat 1 boolean-rings/Boolean-rings-theory-modulo-ACIN | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AC1N(+,0) and AC1I(.,1), strategy c9:"
../cime $* -strat 9 boolean-rings/Boolean-rings-theory-modulo-ACIN | sed -n -e '/^Result/,$ p'
echo
echo "Modulo  AG(+,0,-) ACUI(.,1)), strategy c1:"
../cime $* -strat 1 boolean-rings/Boolean-rings-theory-modulo-AGUI | sed -n -e '/^Result/,$ p'
echo 
echo "Modulo  AG(+,0,-) ACUI(.,1)), strategy c9:"
../cime $* -strat 9 boolean-rings/Boolean-rings-theory-modulo-AGUI | sed -n -e '/^Result/,$ p'
echo 
echo
echo "Commutative rings homomorphism"
echo "---------------------"
echo
echo "Modulo AC:"
yes "c" | ../cime $* commutative-rings-theory/commutative-rings-homomorphism-AC | sed -n -e '/^Result/,$ p'
echo
echo "Modulo CR:"
yes "c" | ../cime $* commutative-rings-theory/commutative-rings-homomorphism | sed -n -e '/^Result/,$ p'
echo
echo "Modulo CR, AG+ACU unif:"
../cime $* commutative-rings-theory/commutative-rings-homomorphism-AGunif | sed -n -e '/^Result/,$ p'
echo
echo
echo "Distributive lattices"
echo "---------------------"
echo
../cime $* distributive-lattices/distributive-lattices | sed -n -e '/^Result/,$ p'
echo
echo
echo "A finitely generated group: the diedral group of order 5"
echo "----------------------------------"
echo
echo "Modulo nothing:"
../cime $* finitely-generated-groups/diedral-group-of-order-5 | sed -n -e '/^Result/,$ p'
echo
echo "Modulo G(.,1,I):"
../cime $* finitely-generated-groups/diedral-group-of-order-5-G | sed -n -e '/^Result/,$ p'
echo
echo
echo "A finitely generated Abelian group"
echo "----------------------------------"
echo
echo "Modulo AC(+):"
../cime $* finitely-generated-groups/grf3-ac | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0):"
../cime $* finitely-generated-groups/grf3-acu | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU(+,0), ACU unification:"
../cime $* finitely-generated-groups/grf3-acu-acu | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG(+,0,-):"
../cime $* finitely-generated-groups/grf3-ag | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG(+,0,-), ACU unification:"
../cime $* finitely-generated-groups/grf3-ag-ACUunif | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG(+,0,-), AG unification:"
../cime $* finitely-generated-groups/grf3-ag-unif-AG | sed -n -e '/^Result/,$ p'
echo
echo
echo "Grobner bases"
echo "-------------"
echo
echo "Over Z (modulo AC):"
../cime $* grobner-bases/simple-over-Z-AC | sed -n -e '/^Result/,$ p'
echo
echo "Over Z (modulo CR):"
../cime $* grobner-bases/simple-over-Z | sed -n -e '/^Result/,$ p'
echo
echo "Over Z (modulo CR, ACU unification):"
../cime $* grobner-bases/simple-over-Z-ACU | sed -n -e '/^Result/,$ p'
echo
echo "Over Z (modulo CR, AG and ACU unification):"
../cime $* grobner-bases/simple-over-Z-unif-AG-ACU | sed -n -e '/^Result/,$ p'
echo
echo
echo "Over F5 (modulo AC):"
../cime $* grobner-bases/over-f5-AC | sed -n -e '/^Result/,$ p'
echo
echo "Over F5 (modulo F5):"
../cime $* grobner-bases/over-f5 | sed -n -e '/^Result/,$ p'
echo
echo "Over F5 (modulo F5, ACU unification):"
../cime $* grobner-bases/over-f5-ACU | sed -n -e '/^Result/,$ p'
echo
echo "Over F5 (modulo F5, AG and ACU unification):"
../cime $* grobner-bases/over-f5-unif-AG-ACU | sed -n -e '/^Result/,$ p'
echo
echo
echo
echo "                ****************************************"
echo "                * Cohen-Watson's system for arithmetic *"
echo "                ***************************************"
echo
echo "Modulo AC:"
echo
echo "  base 3:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_3.cim | sed -n -e '/^Result/,$ p'
echo
echo "  base 4:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_4.cim | sed -n -e '/^Result/,$ p'
echo
echo "  base 5:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_5.cim | sed -n -e '/^Result/,$ p'
echo
echo "  base 6:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_6.cim | sed -n -e '/^Result/,$ p'
echo
echo
echo "Modulo ACU, unif ACU:"
echo
echo "  base 3:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_3_unif_ACU.cim | sed -n -e '/^Result/,$ p'
echo
echo "  base 4:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_4_unif_ACU.cim | sed -n -e '/^Result/,$ p'
echo
echo "  base 5:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_5_unif_ACU.cim | sed -n -e '/^Result/,$ p'
echo
echo "  base 6:"
echo
yes ">" | ../cime $* -strat -100 arithmetic/cohen-watson/cohen_watson_base_6_unif_ACU.cim | sed -n -e '/^Result/,$ p'
echo
echo
echo
echo
echo "                *************************************"
echo "                * The Scottish private club problem *"
echo "                *************************************"
echo
echo "Modulo AC:"
echo
yes "s" | ../cime $* scottish-private-club-problem/private-club-AC.cim | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo BR:"
echo
yes "s" | ../cime $* scottish-private-club-problem/private-club-BR.cim | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo BR, unif BR:"
echo
yes "s" | ../cime $* scottish-private-club-problem/private-club-BR-unif-BR.cim | sed -n -e '/^All conjectures/,$ p'
echo
echo
echo
echo "                ******************************"
echo "                *        Is it a cup ?       *"
echo "                ******************************"
echo
echo "Modulo AC:"
echo
yes "s" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-AC.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo ACU:"
echo
yes "s" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-ACU.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo AG:"
echo
yes "s" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-AG.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo AG et ACU:"
echo
yes "s" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-AG-ACU.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo BR:"
echo
yes "s" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-BR.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "strategy 4 :"
echo "---------------------------------------"
echo
echo "Modulo AC:"
echo
yes "s" | ../cime $* -strat 4 is_it_a_cup/is_it_a_cup_with_bool-unif-AC.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo ACU:"
echo
yes "s" | ../cime $* -strat 4 is_it_a_cup/is_it_a_cup_with_bool-unif-ACU.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo AG:"
echo
yes "s" | ../cime $* -strat 4 is_it_a_cup/is_it_a_cup_with_bool-unif-AG.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo AG et ACU:"
echo
yes "s" | ../cime $* -strat 4 is_it_a_cup/is_it_a_cup_with_bool-unif-AG-ACU.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "Modulo BR:"
echo
yes "s" | ../cime $* -strat 4 is_it_a_cup/is_it_a_cup_with_bool-unif-BR.nc | sed -n -e '/^All conjectures/,$ p'
echo
echo "completion prolongee jusqu'a son terme:"
echo "---------------------------------------"
echo
echo "Modulo AC:"
echo
yes "c" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-AC.nc | sed -n -e '/^Result/,$ p'
echo
echo "Modulo ACU:"
echo
yes "c" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-ACU.nc | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG:"
echo
yes "c" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-AG.nc | sed -n -e '/^Result/,$ p'
echo
echo "Modulo AG et ACU:"
echo
yes "c" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-AG-ACU.nc | sed -n -e '/^Result/,$ p'
echo
echo "Modulo BR:"
echo
yes "c" | ../cime $* is_it_a_cup/is_it_a_cup_with_bool-unif-BR.nc | sed -n -e '/^Result/,$ p'
echo
echo " ****************************************** "
echo " finished at `date '+%D %T'` "
echo " ****************************************** "
echo