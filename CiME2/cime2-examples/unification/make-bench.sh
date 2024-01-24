echo " ****************************************** "
echo " Unification benchmarks for: "
../../cime | sed -n -e 's/Welcome to\(.*\)/\1/p' 
echo -n " On config: " ; uname -a
echo " started at `date '+%D %T'` "
echo " ****************************************** "
echo
echo
echo "Unification modulo AC"
echo "---------------------"
echo
../../cime ac-unification 
echo
echo "Unification modulo ACU"
echo "---------------------"
echo
../../cime acu-unification 
echo
echo " ****************************************** "
echo " finished at `date '+%D %T'` "
echo " ****************************************** "
echo