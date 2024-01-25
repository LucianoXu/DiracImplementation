from __future__ import annotations
import os
from typing import Tuple, List

class untyped_Dirac_TRS:
    def __init__(self):
        self.symbols = '''

let F = signature
"

  (* complex number *)
  + : AC ;
  * : AC ;
  0 : constant ;
  1 : constant ;
  ^* : postfix unary ;

  (* -------- internal langauge -------- *)

  (* Basis *)
  pair : binary ;
  fst : unary ;
  snd : unary ;

  (* Scalar *)
  C : unary ;
  delta : commutative ;
  ADDS : AC ;
  MLTS : AC ;
  CONJS : unary ;
  DOT : infix binary ;

  (* Ket *)
  0K : constant ;
  ket : unary ;
  CTK : unary ;
  SCRK : infix binary ;
  ADDK : AC ;
  MLTK : infix binary ;
  TSRK : infix binary ;

  (* Bra *)
  0B : constant ;
  bra : unary ;
  CTB : unary ;
  SCRB : infix binary ;
  ADDB : AC ;
  MLTB : infix binary ;
  TSRB : infix binary ;

  (* Operator *)
  0O : constant ;
  OUTER : infix binary ;
  CTO : unary ;
  SCRO : infix binary ;
  ADDO : AC ;
  MLTO : infix binary ;
  TSRO : infix binary ;

";
        '''

        self.variables = '''
let X = vars "a b c x S0 S1 S2 S3 s s1 s2 t t1 t2 B0 B1 B2 K0 K1 K2 O0 O1 O2 O1' O2' T1 T2 T3 T4";

'''

        self.rules = [

            ("0 + a -> a ;", "(0 + a) + x -> a + x ;"),
            ("0 * a -> 0 ;", "(0 * a) * x -> 0 * x ;"),
            ("1 * a -> a ;", "(1 * a) * x -> a * x ;"),
            ("a * (b + c) -> (a * b) + (a * c) ;", "(a * (b + c)) * x -> ((a * b) + (a * c)) * x ;"),
            "0 ^* -> 0 ;",
            "1 ^* -> 1 ;",
            "(a + b) ^* -> (a ^*) + (b ^*) ;",
            "(a * b) ^* -> (a ^*) * (b ^*) ;",
            "(a ^*) ^* -> a ;",


            "fst(pair(s, t)) -> s ;",
            "snd(pair(s, t)) -> t ;",
            "pair(fst(t), snd(t)) -> t ;",


            "delta(s, pair(t1, t2)) -> delta(fst(s), t1) MLTS delta(snd(s), t2) ;",
            "delta(fst(s), fst(t)) MLTS delta(snd(s), snd(t)) -> delta(s, t) ;",


            ("C(0) ADDS a -> a ;", "(C(0) ADDS a) ADDS x -> a ADDS x ;"),
            ("C(a) ADDS C(b) -> C(a + b) ;", "(C(a) ADDS C(b)) ADDS x -> C(a + b) ADDS x ;"),
            ("S0 ADDS S0 -> C(1 + 1) MLTS S0 ;", "(S0 ADDS S0) ADDS x -> (C(1 + 1) MLTS S0) ADDS x ;"),
            ("(C(a) MLTS S0) ADDS S0 -> C(a + 1) MLTS S0 ;", "((C(a) MLTS S0) ADDS S0) ADDS x -> (C(a + 1) MLTS S0) ADDS x ;"),
            ("(C(a) MLTS S0) ADDS (C(b) MLTS S0) -> C(a + b) MLTS S0 ;", "((C(a) MLTS S0) ADDS (C(b) MLTS S0)) ADDS x -> (C(a + b) MLTS S0) ADDS x ;"),

            ("C(0) MLTS a -> C(0) ;", "(C(0) MLTS a) MLTS x -> C(0) MLTS x ;"),
            ("C(1) MLTS a -> a ;", "(C(1) MLTS a) MLTS x -> a MLTS x ;"),
            ("C(a) MLTS C(b) -> C(a * b) ;", "(C(a) MLTS C(b)) MLTS x -> C(a * b) MLTS x ;"),
            ("S1 MLTS (S2 ADDS S3) -> (S1 MLTS S2) ADDS (S1 MLTS S3) ;", "(S1 MLTS (S2 ADDS S3)) MLTS x -> ((S1 MLTS S2) ADDS (S1 MLTS S3)) MLTS x ;"),


            "CONJS(C(a)) -> C(a ^*) ;",
            "CONJS(delta(s, t)) -> delta(s, t) ;",
            "CONJS(S1 ADDS S2) -> CONJS(S1) ADDS CONJS(S2) ;",
            "CONJS(S1 MLTS S2) -> CONJS(S1) MLTS CONJS(S2) ;",
            "CONJS(CONJS(S0)) -> S0 ;",
            "CONJS(B0 DOT K0) -> CTB(K0) DOT CTK(B0) ;",

            "0B DOT K0 -> C(0) ;",
            "B0 DOT 0K -> C(0) ;",
            "(S0 SCRB B0) DOT K0 -> S0 MLTS (B0 DOT K0) ;",
            "B0 DOT (S0 SCRK K0) -> S0 MLTS (B0 DOT K0) ;",
            "(B1 ADDB B2) DOT K0 -> (B1 DOT K0) ADDS (B2 DOT K0) ;",
            "B0 DOT (K1 ADDK K2) -> (B0 DOT K1) ADDS (B0 DOT K2) ;",
            "bra(s) DOT ket(t) -> delta(s, t) ;",
            "(B1 TSRB B2) DOT ket(t) -> (B1 DOT ket(fst(t))) MLTS (B2 DOT ket(snd(t))) ;",
            "bra(t) DOT (K1 TSRK K2) -> (bra(fst(t)) DOT K1) MLTS (bra(snd(t)) DOT K2) ;",
            "(B1 TSRB B2) DOT (K1 TSRK K2) -> (B1 DOT K1) MLTS (B2 DOT K2) ;",

            "(B0 MLTB O0) DOT K0 -> B0 DOT (O0 MLTK K0) ;",
            "bra(s) DOT ((O1 TSRO O2) MLTK K0) -> ((bra(fst(s)) MLTB O1) TSRB (bra(snd(s)) MLTB O2)) DOT K0 ;",
            "(B1 TSRB B2) DOT ((O1 TSRO O2) MLTK K0) -> ((B1 MLTB O1) TSRB (B2 MLTB O2)) DOT K0 ;",




            "CTK(0B) -> 0K ;",
            "CTK(bra(t)) -> ket(t) ;",
            "CTK(CTB(K0)) -> K0 ;",
            "CTK(S0 SCRB B0) -> CONJS(S0) SCRK CTK(B0) ;",
            "CTK(B1 ADDB B2) -> CTK(B1) ADDK CTK(B2) ;",
            "CTK(B0 MLTB O0) -> CTO(O0) MLTK CTK(B0) ;",
            "CTK(B1 TSRB B2) -> CTK(B1) TSRK CTK(B2) ;",

            "CTB(0K) -> 0B ;",
            "CTB(ket(t)) -> bra(t) ;",
            "CTB(CTK(B0)) -> B0 ;",
            "CTB(S0 SCRK K0) -> CONJS(S0) SCRB CTB(K0) ;",
            "CTB(K1 ADDK K2) -> CTB(K1) ADDB CTB(K2) ;",
            "CTB(O0 MLTK K0) -> CTB(K0) MLTB CTO(O0) ;",
            "CTB(K1 TSRK K2) -> CTB(K1) TSRB CTB(K2) ;",

            "C(0) SCRK K0 -> 0K ;",
            "C(1) SCRK K0 -> K0 ;",
            "S0 SCRK 0K -> 0K ;",
            "S1 SCRK (S2 SCRK K0) -> (S1 MLTS S2) SCRK K0 ;",
            "S0 SCRK (K1 ADDK K2) -> (S0 SCRK K1) ADDK (S0 SCRK K2) ;",

            "C(0) SCRB B0 -> 0B ;",
            "C(1) SCRB B0 -> B0 ;",
            "S0 SCRB 0B -> 0B ;",
            "S1 SCRB (S2 SCRB B0) -> (S1 MLTS S2) SCRB B0 ;",
            "S0 SCRB (B1 ADDB B2) -> (S0 SCRB B1) ADDB (S0 SCRB B2) ;",

            ("K0 ADDK 0K -> K0 ;", "(K0 ADDK 0K) ADDK x -> K0 ADDK x ;"),
            ("K0 ADDK K0 -> C(1 + 1) SCRK K0 ;", "(K0 ADDK K0) ADDK x -> (C(1 + 1) SCRK K0) ADDK x ;"),
            ("(S0 SCRK K0) ADDK K0 -> (S0 ADDS C(1)) SCRK K0 ;", "((S0 SCRK K0) ADDK K0) ADDK x -> ((S0 ADDS C(1)) SCRK K0) ADDK x ;"),
            ("(S1 SCRK K0) ADDK (S2 SCRK K0) -> (S1 ADDS S2) SCRK K0 ;", "((S1 SCRK K0) ADDK (S2 SCRK K0)) ADDK x -> ((S1 ADDS S2) SCRK K0) ADDK x ;"),

            ("B0 ADDB 0B -> B0 ;", "(B0 ADDB 0B) ADDB x -> B0 ADDB x ;"),
            ("B0 ADDB B0 -> C(1 + 1) SCRB B0 ;", "(B0 ADDB B0) ADDB x -> (C(1 + 1) SCRB B0) ADDB x ;"),
            ("(S0 SCRB B0) ADDB B0 -> (S0 ADDS C(1)) SCRB B0 ;", "((S0 SCRB B0) ADDB B0) ADDB x -> ((S0 ADDS C(1)) SCRB B0) ADDB x ;"),
            ("(S1 SCRB B0) ADDB (S2 SCRB B0) -> (S1 ADDS S2) SCRB B0 ;", "((S1 SCRB B0) ADDB (S2 SCRB B0)) ADDB x -> ((S1 ADDS S2) SCRB B0) ADDB x ;"),


            "0O MLTK K0 -> 0K ;",
            "O0 MLTK 0K -> 0K ;",
            "(S0 SCRO O0) MLTK K0 -> S0 SCRK (O0 MLTK K0) ;",
            "O0 MLTK (S0 SCRK K0) -> S0 SCRK (O0 MLTK K0) ;",
            "(O1 ADDO O2) MLTK K0 -> (O1 MLTK K0) ADDK (O2 MLTK K0) ;",
            "O0 MLTK (K1 ADDK K2) -> (O0 MLTK K1) ADDK (O0 MLTK K2) ;",
            "(K1 OUTER B0) MLTK K2 -> (B0 DOT K2) SCRK K1 ;",
            "(O1 MLTO O2) MLTK K0 -> O1 MLTK (O2 MLTK K0) ;",
            "(O1 TSRO O2) MLTK ((O1' TSRO O2') MLTK K0) -> ((O1 MLTO O1') TSRO (O2 MLTO O2')) MLTK K0 ;",
            "(O1 TSRO O2) MLTK ket(t) -> (O1 MLTK ket(fst(t))) TSRK (O2 MLTK ket(snd(t))) ;",
            "(O1 TSRO O2) MLTK (K1 TSRK K2) -> (O1 MLTK K1) TSRK (O2 MLTK K2) ;",

            "B0 MLTB 0O -> 0B ;",
            "0B MLTB O0 -> 0B ;",
            "B0 MLTB (S0 SCRO O0) -> S0 SCRB (B0 MLTB O0) ;",
            "(S0 SCRB B0) MLTB O0 -> S0 SCRB (B0 MLTB O0) ;",
            "B0 MLTB (O1 ADDO O2) -> (B0 MLTB O1) ADDB (B0 MLTB O2) ;",
            "(B1 ADDB B2) MLTB O0 -> (B1 MLTB O0) ADDB (B2 MLTB O0) ;",
            "B1 MLTB (K0 OUTER B2) -> (B1 DOT K0) SCRB B2 ;",
            "B0 MLTB (O1 MLTO O2) -> (B0 MLTB O1) MLTB O2 ;",
            "(B0 MLTB (O1' TSRO O2')) MLTB (O1 TSRO O2) -> B0 MLTB ((O1' MLTO O1) TSRO (O2' MLTO O2)) ;",
            "bra(t) MLTB (O1 TSRO O2) -> (bra(fst(t)) MLTB O1) TSRB (bra(snd(t)) MLTB O2) ;",
            "(B1 TSRB B2) MLTB (O1 TSRO O2) -> (B1 MLTB O1) TSRB (B2 MLTB O2) ;",

            "0K TSRK K0 -> 0K ;",
            "K0 TSRK 0K -> 0K ;",
            "ket(s) TSRK ket(t) -> ket(pair(s, t)) ;",
            "(S0 SCRK K1) TSRK K2 -> S0 SCRK (K1 TSRK K2) ;",
            "K1 TSRK (S0 SCRK K2) -> S0 SCRK (K1 TSRK K2) ;",
            "(K1 ADDK K2) TSRK K0 -> (K1 TSRK K0) ADDK (K2 TSRK K0) ;",
            "K0 TSRK (K1 ADDK K2) -> (K0 TSRK K1) ADDK (K0 TSRK K2) ;",

            "0B TSRB B0 -> 0B ;",
            "B0 TSRB 0B -> 0B ;",
            "bra(s) TSRB bra(t) -> bra(pair(s, t)) ;",
            "(S0 SCRB B1) TSRB B2 -> S0 SCRB (B1 TSRB B2) ;",
            "B1 TSRB (S0 SCRB B2) -> S0 SCRB (B1 TSRB B2) ;",
            "(B1 ADDB B2) TSRB B0 -> (B1 TSRB B0) ADDB (B2 TSRB B0) ;",
            "B0 TSRB (B1 ADDB B2) -> (B0 TSRB B1) ADDB (B0 TSRB B2) ;",


            "0K OUTER B0 -> 0O ;",
            "K0 OUTER 0B -> 0O ;",
            "(S0 SCRK K0) OUTER B0 -> S0 SCRO (K0 OUTER B0) ;",
            "K0 OUTER (S0 SCRB B0) -> S0 SCRO (K0 OUTER B0) ;",
            "(K1 ADDK K2) OUTER B0 -> (K1 OUTER B0) ADDO (K2 OUTER B0) ;",
            "K0 OUTER (B1 ADDB B2) -> (K0 OUTER B1) ADDO (K0 OUTER B2) ;",

            "CTO(0O) -> 0O ;",
            "CTO(K0 OUTER B0) -> CTK(B0) OUTER CTB(K0) ;",
            "CTO(CTO(O0)) -> O0 ;",
            "CTO(S0 SCRO O0) -> CONJS(S0) SCRO CTO(O0) ;",
            "CTO(O1 ADDO O2) -> CTO(O1) ADDO CTO(O2) ;",
            "CTO(O1 MLTO O2) -> CTO(O2) MLTO CTO(O1) ;",
            "CTO(O1 TSRO O2) -> CTO(O1) TSRO CTO(O2) ;",

            "C(0) SCRO O0 -> 0O ;",
            "C(1) SCRO O0 -> O0 ;",
            "S0 SCRO 0O -> 0O ;",
            "S1 SCRO (S2 SCRO O0) -> (S1 MLTS S2) SCRO O0 ;",
            "S0 SCRO (O1 ADDO O2) -> (S0 SCRO O1) ADDO (S0 SCRO O2) ;",

            ("O0 ADDO 0O -> O0 ;", "(O0 ADDO 0O) ADDO x -> O0 ADDO x ;"),
            ("O0 ADDO O0 -> C(1 + 1) SCRO O0 ;", "(O0 ADDO O0) ADDO x -> (C(1 + 1) SCRO O0) ADDO x ;"),
            ("(S0 SCRO O0) ADDO O0 -> (S0 ADDS C(1)) SCRO O0 ;", "((S0 SCRO O0) ADDO O0) ADDO x -> ((S0 ADDS C(1)) SCRO O0) ADDO x ;"),
            ("(S1 SCRO O0) ADDO (S2 SCRO O0) -> (S1 ADDS S2) SCRO O0 ;", "((S1 SCRO O0) ADDO (S2 SCRO O0)) ADDO x -> ((S1 ADDS S2) SCRO O0) ADDO x ;"),

            "0O MLTO O0 -> 0O ;",
            "O0 MLTO 0O -> 0O ;",
            "(K0 OUTER B0) MLTO O0 -> K0 OUTER (B0 MLTB O0) ;",
            "O0 MLTO (K0 OUTER B0) -> (O0 MLTK K0) OUTER B0 ;",
            "(S0 SCRO O1) MLTO O2 -> S0 SCRO (O1 MLTO O2) ;",
            "O1 MLTO (S0 SCRO O2) -> S0 SCRO (O1 MLTO O2) ;",
            "(O1 ADDO O2) MLTO O0 -> (O1 MLTO O0) ADDO (O2 MLTO O0) ;",
            "O0 MLTO (O1 ADDO O2) -> (O0 MLTO O1) ADDO (O0 MLTO O2) ;",
            "(O1 MLTO O2) MLTO O0 -> O1 MLTO (O2 MLTO O0) ;",
            "(O1 TSRO O2) MLTO (O1' TSRO O2') -> (O1 MLTO O1') TSRO (O2 MLTO O2') ;",
            "(O1 TSRO O2) MLTO ((O1' TSRO O2') MLTO O0) -> ((O1 MLTO O1') TSRO (O2 MLTO O2')) MLTO O0 ;",

            "0O TSRO O0 -> 0O ;",
            "O0 TSRO 0O -> 0O ;",
            "(K1 OUTER B1) TSRO (K2 OUTER B2) -> (K1 TSRK K2) OUTER (B1 TSRB B2) ;",
            "(S0 SCRO O1) TSRO O2 -> S0 SCRO (O1 TSRO O2) ;",
            "O1 TSRO (S0 SCRO O2) -> S0 SCRO (O1 TSRO O2) ;",
            "(O1 ADDO O2) TSRO O0 -> (O1 TSRO O0) ADDO (O2 TSRO O0) ;",
            "O0 TSRO (O1 ADDO O2) -> (O0 TSRO O1) ADDO (O0 TSRO O2) ;",
            
        ]

    def get_script(self, remove : None | int = None) -> str:
        if remove is None:
            new_rules = self.rules
        else:
            new_rules = self.rules[:remove] + self.rules[remove + 1:]

        rule_txt = ""

        for rule_set in new_rules:
            if isinstance(rule_set, str):
                rule_txt += rule_set + "\n"
            else:
                for rule in rule_set:
                    rule_txt += rule + "\n"
        
        trs_txt = f'''
let R = TRS F X "

{rule_txt}

";
        '''

        return self.symbols + self.variables + "\n" + trs_txt

    def check_confluence(self, remove : None | int = None) -> bool:
        script = f"""
{self.get_script(remove)}

confluence R;

#quit;
"""
        
        with open("temp.cim2", "w") as f:
            f.write(script)
        a = os.popen("./cime2 temp.cim2")
        txt = a.read()[-200:]
        return txt.find("System is confluent") != -1



if __name__ == "__main__":
    print("Checking redundency ...")
    trs = untyped_Dirac_TRS()

    unnecessary_rules = []

    for i in range(len(trs.rules)):
        print(f"{i}-th rule: {trs.rules[i]}")
        if trs.check_confluence(remove=i):
            print("UNNECESSARY")
            unnecessary_rules.append(trs.rules[i])

        else:
            print("necessary")

        print()

    print("Found unnecessary rules:")
    print(unnecessary_rules)