# Compiling the development

We depend on the following external libraries:

```
  "coq"                      { = "8.18.0"           }
  "coq-core"                 { = "8.18.0"           }
  "coq-elpi"                 { = "2.0.0"            }
  "dune"                     {>= "3.2" & <= "3.13.0"}
  "dune-configurator"        { = "3.12.1"           }
  "coq-hierarchy-builder"    { = "1.7.0"            }
  "coq-mathcomp-ssreflect"   { = "2.2.0"            }
  "coq-mathcomp-algebra"     { = "2.2.0"            }
  "coq-mathcomp-fingroup"    { = "2.2.0"            }
  "coq-mathcomp-analysis"    { = "1.0.0"            }
  "coq-mathcomp-real-closed" { = "2.0.0"            }
  "coq-mathcomp-finmap"      { = "2.1.0"            }
```

The easiest way to install the above libraries is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```bash
opam switch create \
    --yes \
    --deps-only \
    --repositories=default=https://opam.ocaml.org,coq-released=https://coq.inria.fr/opam/released \
    .
```

Then, you can compile the development by just typing `make` (or `opam
config exec -- make` if you used a local opam switch to install the
dependencies).

Remark: if any unexpected error occurs, please follow the exact version of the 
above libraries. It's known that dune-configurator >= 3.13.0 will kill the 
compilation (incompatible with coq.8.18.0 if use `-(notation)` attribute 
for importing files).

# Axioms present in the develoment

Our development is made assuming the informative excluded middle and
functional extensionality. The axioms are not explicitly stated in our
development but inherited from mathcomp analysis.

# Comments for each file

Our development is based on the CoqQ project [Zhou et al. 2023] and recent development of [FZY23].

Formalization of this work is displayed in the /src/example.

## dirac_notation.v (Section 8.2)

Our formalization includes three layers :

    L1. core language DN (without big sum and fst/snd) with static type checking done by coq directly;
      a) define the semantics
      b) prove all the rules
      c) prove axiomatic semantics
    L2. extended language DNE with static type checking done by coq directly;
      a) define the semantics
      b) relation between L1 and L2 for syntax and semantis
    L3. DNE with dynamic types (corresponding to Mathematica implementation)
      a) define semantics
      b) relation between L2 and L3 for syntax and semantis
      c) prove all rewriting rules

    Relation: L1 - L2 - L3
      L1_L2_syn : formula in L1 -> formula in L2
      L1_L2_sem : forall t : formula in L1,
                    L2_sem (L1_L2_syn t) = L1_sem t
      L2_L3_syn : formula in L2 -> formula in L3
      L2_L3_type : forall t : formula in L2 with type T,
                    L3_type (L2_L3_syn t) = T
      L2_L3_sem : forall t : formula in L2,
                    L3_sem (L2_L3_syn t) = L2_sem t

    Conclusion: L1 - L2 - L3
      1. L1_L2_syn and L2_L3_syn are trivial
      2. L1 -> L2 -> L3, the former the easier to understand
      3. L1_L2_sem and L2_L3_sem shows that L2_sem and L3_sem are correctly
          defined, the former the easier to understand
      4. according to 3, we conclude,
          a). if two formulas t1 = t2 in L1, then it is sufficient to show
              that L1_L2_syn t1 = L1_L2_syn t2 in L2
          b). if two formulas t1 = t2 in L2, then it is sufficient to show
              that L2_L3_syn t1 = L2_L3_syn t2 in L3

# Files copy from CoqQ or [FZY23]

### mcextra.v (copy from CoqQ)
Extra of mathcomp and mathcomp-real-closed

### mcaextra.v (copy from CoqQ)
Extra of mathcomp-analysis

### notation.v
Collecting common notations of CoqQ

### xvector.v (copy from CoqQ)
Extra of mathcomp/algebra/vector.v

### setdec.v (copy from CoqQ)
A prove-by-reflection tactic for efficient automated reasoning about
  set theory goals based on the tableau decision procedure in
  [Anisimov 2015].

### mxpred.v (copy from CoqQ)
Predicate for matrix and their hierarchy theory; 
  modules for vector norm, vector order;
  define matrix norm includes pnorm (entry-wise p-norm),
  i2norm (induced 2-norm), trnorm (trace/nuclear norm/schatten 1
  norm), fbnorm (Frobenius norm/schatten 2 norm). Provide singular
  value decomposition. Define Lowner order of matrices.

### cpo.v (copy from CoqQ)
Module for complete partial order.

### orthomodular.v (inherited from CoqQ, copy from [FZY23])
Module for orthomodular lattice (inherited from CoqQ); 
 establish foundational theories of orthomodular lattices following
 from [Beran 1985; Gabriëls et al . 2017], prove extensive properties 
 and tactics for determining the equivalence and order relations of 
 free bivariate formulas [Beran 1985].

### hermitian.v (copy from CoqQ)
Define the Hermitian space and its instance chsType -- hermitian
  type with a orthonormal canonical basis. Define and prove correct
  the Gram–Schmidt process that allows the orthonormalization a set of
  vectors w.r.t. an inner product. Define outer product and
  basic operators such as adjoint, transpose, conjugate of linear functions.

### quantum.v (copy from CoqQ)
Define most of the basic concept of quantum mechanics based on
  linear function representation (lfun). Concepts includes:
  normal/hermitian/positive-semidefinite/density/observable/projection/isometry/unitary
  linear operators, super-operators and its norms and topology,
  (partial) orthonormal basis, normalized state, trace-nonincreasing /
  trace-preserving (quantum measurement) maps, completely-positive
  super-operators (CP, via choi matrix theory), quantum operation
  (QO), quantum channel (QC). Basic constructs of super-operator
  (initialization, unitary transformation, if and while, dual
  super-operator) and their canonical structure to CP/QO/QC.

### extnum.v (reformalization of mxtopology from CoqQ, copy from [FZY23])
Define $\small\texttt{extNumType}$ as the common parent type of 
  $\small\mathbb{R}$ and $\small\mathbb{C}$ 
  to prove the topological properties of $\small\mathbb{R}^n$ and $\small\mathbb{C}^n$ 
  under the same framework. Modules for 
  finite-dimensional normed module type $\small\texttt{finNormedModType}$
  (equipped with a vector order) and finite-dimensional ordered topological 
  vector space $\small\texttt{vorderFinNormedModType}$. 
  Prove the Bolzano-Weierstrass theorem, the equivalence of vector norms,
  the monotone convergence theorem for vector space w.r.t. arbitrary
  vector order with closed condition.

### ctopology.v (reformalization of mxtopology from CoqQ, copy from [FZY23])
Instantiate extnum.v to complex number. Show density matrices
  form a cpo w.r.t. Lowner order.

### prodvect.v (copy from CoqQ)
Variant of dependent finite function.

### tensor.v (copy from CoqQ)
Define the tensor product over a family of Hermitian space based on
  their bases. define multi-linear maps. Prove that the tensor produce
  of Hermitian/chsType is still a Hermitian/chsType with inner product
  consistent with each components. 

### inhabited.v (copy from CoqQ)
Define inhabited finite type (ihbFinType), Hilbert space associated
  to a ihbFinType, tensor product of state/operator in/on associated
  Hilbert space (for pair, tuple, finite function and dependent finite
  function)

### qtype.v (copy from CoqQ)
Utility of quantum data type; includes common 1/2-qubit gates,
  multiplexer, quantum Fourier bases/transformation, (phase) oracle
  (i.e., quantum access to a classical function) etc.

### hspace.v (copy from CoqQ)
Hilbert subspace theory based on projection representation; i.e., the theory
  of projection lattice.

### hstensor.v (rearrange tensor.v + lfundef.v + quantum.v from CoqQ, copy from [FZY23])
For a given $\small L$ and $\small{\mathcal{H}_i}$ for $\small{i\in L}$, 
define Hilbert space $\bigotimes_{i \in S}\mathcal{H}_i$ for any subsystem $\small{S \subseteq L}$.
  Define the tensor product of vectors and linear functions, 
  and general composition of linear functions.
  Define the cylindrical extension of linear functions (lifting to a larger space).

### dirac.v (copy from CoqQ)
Labelled Dirac notation, defined as a non-dependent type and have
  linear algebraic structure. Using canonical structures to trace the
  domain and codomain of a labelled Dirac notation.
Make it compatible with mathcomp-analysis/forms.v.

### autonat.v (copy from [FZY23])
Light-weight tactic for mathcomp nat based on standard Lia/Nia: dealing with 
ordinal numbers, divn, modn, half/uphalf and bump. It served as the automated 
checking for the disjointness of quantum registers (of array variables with 
indexes).

### hspace_extra.v (copy from [FZY23])
Extra of hspace.v, formalizing infinite caps and cups of Hilbert subspaces 
and related theories.

### qreg.v (copy from [FZY23])
Formalization of quantum registers. define $\small\texttt{qType}$, 
$\small\texttt{cType}$ and classical/quantum variables. define quantum 
registers as an inductive type that reflects the manipulation of 
quantum variables (e.g., merging and splitting). An automated type-checker 
for the disjointness condition is implemented to enhance usability.

### qmem.v (copy from [FZY23])
Formalization of quantum memory model: mapping each quantum variable/register 
to a tensor Hilbert system (as its semantics). It is consistent with the 
merging and splitting of quantum registers. A default memory model is established. 
Related theories that facilitate the use of Dirac notation are re-proved.

# Files copy from Mathcomp

### complex.v (copy from mathcomp-real-closed)
Fixing canonical problem (unexpected coercion from 
$\small\mathbb{C}$ to $\small{\texttt{lmodType R}}$ without alias).

### spectral.v (copy from mathcomp-algebra 'experiment/forms' branch)

# Reference

[Zhou et al. 2023] Li Zhou, Gilles Barthe, Pierre-Yves Strub, Junyi Liu, and Mingsheng Ying. 2023. CoqQ: Foundational Verification of Quantum Programs. Proc. ACM Program. Lang. 7, POPL, Article 29 (jan 2023), 33 pages. https://doi.org/10.1145/3571222

[FZY23] Yuan Feng, Li Zhou, and Yingte Xu. 2023. Refinement calculus of quantum programs with projective assertions. arXiv:2311.14215 [cs.LO]