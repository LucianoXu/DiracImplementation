

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Require Import List.


(* Terms and types for atomic quantum subsystems. *)
Module Type AtomicType.

    Axiom AType : Type.
    Axiom ATerm : Type.

    (* well-typed relation should be decidable for atomic terms and types.*)
    Axiom WT : ATerm -> AType -> bool.

End AtomicType.


(* Quantum types and terms. *)
Module QuType (AT : AtomicType).

    Inductive QType : Type :=
        | QUnit : QType
        | atomic_type : AT.AType -> QType.

    Inductive QTerm : Type :=
        | atomic_term : AT.ATerm -> QTerm.

End QuType.


(*  The module for linear algebra.

    Note that the type of Hilbert spaces comes from the [AtomicType] module. *)

Module Type LinAlg (AT : AtomicType).

    (* The QType terms act as linear spaces, and QTerm terms act as the basis. *)
    Module QT := QuType AT.
    
    (* vectors in some space *)
    Axiom Vec : QT.QType -> Type.

    (* linear operators with the domain and codomain *)
    Axiom LOpt : QT.QType * QT.QType -> Type.

    (* somehow we will need a simple typed lambda calculus.
        - Basic type: VecType and LOptType *)
    
End LinAlg.



(* The L0 Dirac notation depends on the atomic type system and the linear algebra module. *)
Module DiracL0 
        (CT : AtomicType)
        (LA_Fun : LinAlg).

    Module LA := LA_Fun CT.
    Module QT := LA.QT.

    (* quantum register *)
    Inductive QReg : Type :=
        | qvar : string -> QReg.

    (* typing of quantum variables *)
    Module QVarTyping.
        Record type := Pack {
            qvar : string;
            qtype : QT.QType;
        }.
    End QVarTyping.

    (* quantum context *)
    Definition QCont := list QVarTyping.type.

    Fixpoint var_notin_qc (var : string) (qc : QCont) : bool :=
        match qc with 
        | nil => true
        | h :: t => var_notin_qc var t && string_dec (QVarTyping.qvar h) var
        end.

    (* well-formed quantum context *)
    Module WF_QCont.
        Fixpoint qcont_wf (qc : QCont) : bool := 
            match qc with
            | nil => true
            | h :: t => qcont_wf t && var_notin_qc (QVarTyping.qvar h) t
            end.

        Record type := Pack {
            sort : _;
            class_of : qcont_wf sort;
        }.
    End WF_QCont.

    (* well-typed quantum registers *)
    Module WT_QReg.
        Axiom axiom : WF_QCont.type -> QReg -> QT.QType -> bool.

        Record type (qc : WF_QCont.type):= Pack {
            qreg : QReg;
            qtype : QT.QType;
            class_of : axiom qc qreg qtype = true;
        }.
    End WT_QReg.

    (* disjointness omitted *)



    (* atomic quantum registers *)
    Module Atomic_QReg.

        Definition qreg_atomic (qc : WF_QCont.type) (qr : WT_QReg.type qc) : bool :=
            match WT_QReg.qtype qr with
            | QT.QUnit => true
            | QT.atomic_type _ => true
            (* | _ => false *)
            end.

        Record type (qc : WF_QCont.type) := {
            sort : WT_QReg.type qc;
            class_of : qreg_atomic sort;
        }.

    End Atomic_QReg.



    (* about the set of atomic quantum systems *)
    Module QSysSet.

        Inductive type (qc : WF_QCont.type) : Type := 
            | ls_set : list (Atomic_QReg.type qc) -> type qc.

        (* qsysset is decidable *)
        Axiom dec : forall qc (s1 s2: type qc), (s1 = s1) + (s1 <> s1).
        
        Axiom union : forall qc, type qc -> type qc -> type qc.

        Axiom intersec : forall qc, type qc -> type qc -> type qc.
        
        Axiom sub : forall qc, type qc -> type qc -> type qc.

        Axiom setof_qreg : forall qc, WT_QReg.type qc -> type qc.

        Module Exports.
            Notation " A '∪' B " := (union A B) (at level 43).
            Notation " A '∩' B " := (intersec A B) (at level 42).
            Notation " A '--' B " := (sub A B) (at level 42).
            Notation "∅" := (ls_set nil).
        End Exports.

    End QSysSet.
    Export QSysSet.Exports.

    

    (* Dirac Notations *)
    Module Dirac.

        Record Ket := {
            ket_qt : QT.QType;
            ket_v : LA.Vec ket_qt;
            ket_qr : QReg;
        }.

        Record Bra := {
            bra_qt : QT.QType;
            bra_v : LA.Vec bra_qt;
            bra_qr : QReg;
        }.

        Record Opt := {
            opt_qtk : QT.QType;
            opt_qtb : QT.QType;
            opt_lo : LA.LOpt (opt_qtk, opt_qtb);
            opt_qrk : QReg;
            opt_qrb : QReg;
        }.
        
        Inductive type : Type :=
            | ket : Ket -> type
            | bra : Bra -> type
            | opt : Opt -> type

            | add : type -> type -> type
            | mul : type -> type -> type
            | tensor : type -> type -> type
            | conj : type -> type
            | trans : type -> type.

    End Dirac.



    (* well-typed Dirac notations *)

    Module WT_Dirac.

        Record dirac_typing (qc : WF_QCont.type) := {
            dirac : Dirac.type;
            setK : QSysSet.type qc;
            setB : QSysSet.type qc;
        }.


        Inductive axiom (qc : WF_QCont.type) : 

                dirac_typing qc -> Prop :=

            | ket 
                (e : Dirac.Ket)
                (H : WT_QReg.axiom qc (Dirac.ket_qr e) (Dirac.ket_qt e)) :
                    axiom 
                    {|  
                        dirac := Dirac.ket e; 
                        setK := QSysSet.setof_qreg (WT_QReg.Pack H); 
                        setB := ∅
                    |}

            | bra             
                (e : Dirac.Bra)
                (H : WT_QReg.axiom qc (Dirac.bra_qr e) (Dirac.bra_qt e)) :
                    axiom 
                    {|  
                        dirac := Dirac.bra e;
                        setK := QSysSet.setof_qreg (WT_QReg.Pack H); 
                        setB := ∅
                    |}

            | opt 
                (e : Dirac.Opt)
                (Hk : WT_QReg.axiom qc (Dirac.opt_qrk e) (Dirac.opt_qtk e))
                (Hb : WT_QReg.axiom qc (Dirac.opt_qrb e) (Dirac.opt_qtb e)) :
                    axiom 
                    {|  
                        dirac := Dirac.opt e;
                        setK := QSysSet.setof_qreg (WT_QReg.Pack Hk);
                        setB := QSysSet.setof_qreg (WT_QReg.Pack Hb);
                    |}

            | add 
                (tl : dirac_typing qc) (Hl : axiom tl)
                (tr : dirac_typing qc) (Hr : axiom tr)
                (HSk_eq : QSysSet.dec (setK tl) (setK tr)) 
                (HSb_eq : QSysSet.dec (setB tl) (setB tl)):
                    axiom 
                    {|  
                        dirac := Dirac.add (dirac tl) (dirac tr);
                        setK := setK tl;
                        setB := setB tl;
                    |}

            | mul
                (tl : dirac_typing qc) (Hl : axiom tl)
                (tr : dirac_typing qc) (Hr : axiom tr)
                (Hdisj_k : QSysSet.dec ((setK tl) ∩ (setK tr -- setB tl)) ∅)
                (Hdisj_b : QSysSet.dec ((setB tl -- setK tr) ∩ (setB tr)) ∅) :
                    axiom 
                    {|  
                        dirac := Dirac.mul (dirac tl) (dirac tr);
                        setK := (setK tl) ∪ (setK tr -- setB tl);
                        setB := (setB tl -- setK tr) ∪ (setB tr);
                    |}

            | tensor
                (tl : dirac_typing qc) (Hl : axiom tl)
                (tr : dirac_typing qc) (Hr : axiom tr)
                (Hdisj_k : QSysSet.dec ((setK tl) ∩ (setK tr)) ∅)
                (Hdisj_b : QSysSet.dec ((setB tl) ∩ (setB tr)) ∅) :
                    axiom 
                    {|  
                        dirac := Dirac.tensor (dirac tl) (dirac tr);
                        setK := (setK tl) ∪ (setK tr);
                        setB := (setB tl) ∪ (setB tr);
                    |}

            | conj
                (t : dirac_typing qc) (H : axiom t):
                    axiom 
                    {|
                        dirac := Dirac.conj (dirac t);
                        setK := setK t;
                        setB := setB t;
                    |}
            
            | trans
                (t : dirac_typing qc) (H : axiom t):
                    axiom 
                    {|
                        dirac := Dirac.trans (dirac t);
                        setK := setB t;
                        setB := setK t;
                    |}.

            Record type (qc : WF_QCont.type) := {
                sort : dirac_typing qc;
                class_of : axiom sort;
            }.

    End WT_Dirac.


    (* The reduction for dirac typings. *)
    Module WT_DiracR.

        Inductive Step qc : WT_Dirac.dirac_typing qc -> WT_Dirac.dirac_typing qc -> Prop := 
        (* | ..... *)
        .

        Lemma StepPreserveWT qc (t1 t2 : WT_Dirac.dirac_typing qc) :
        
            Step t1 t2 -> WT_Dirac.axiom t1 -> WT_Dirac.axiom t2.

        Proof.
        Admitted.

    End WT_DiracR.


End DiracL0.

Print DiracL0.