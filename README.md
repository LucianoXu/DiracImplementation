# DiracDec Artifact

This repository contains the artifact for the paper "Automating equational proofs in Dirac notation".

Our main artifact for evaluation is the Mathematica implementation to decide the equivalence of Dirac notations.
As is mentioned in the paper, the Coq mechanization formalizes the core language, extended language and implementation enhancements.
The termination and confluence proofs are conducted on the untyped version of the core language.

## Mathematica implementation
The implementation is in the folder `Mathematica`.
To run the tool, you should have Mathematica installed on your machine. The file for evaluation is the Mathematica notebook `Tutorial.nb` and `eval.nb`.

Other files in the folder are:

- `DiracDec`: the Mathematica implmenetation of DiracDec. The rewriting rules for the core language can be found in `DiracDec/DiracCore.wl`.
- `ExampleList.nb`: the Mathematica notebook containing the example list.
- `HHL.nb`: the Mathematica notebook containing the exceprt verification of the HHL example.


## CoqQ Mechanization
The Coq mechanization of the Dirac notation is in the folder `CoqQ`. This folder contains the CoqQ project, and 
the formalization for the soundness of our system is in `CoqQ/src/dirac_notation.v`.

To check the Coq mechanism project, install opam, and follow the instructions in the `CoqQ/README.md` file.


## Termination Proof
The termination proof in the `termination` folder is accomplished with the AProVE tool (https://aprove.informatik.rwth-aachen.de/interface/v-AProVE2023/trs_aprove).
The encoding of the untyped system is in `termination/dirac untyped.tes`, and the verified result is already in the html file.

To reproduce the result, you can submit the `dirac untyped.tes` file to the online AProVE tool. But because of the resource limitation and some randomness in the tool, it typically takes several retries to get the successful result.

## Confluence Proof
The binary and scripts of the confluence proof is in `CiME2`.
The encoding of the untyped system is in `CiME2/dirac.cim2`. 
The binary file (x86, Linux) for the CiME2 tool is `CiME2/cime2`.

To reproduce the result, open a terminal in the `CiME2` folder and run the following command:
```
sudo chmod +x ./cime2
./cime2
```
It starts the CiME2 tool. Then you can load the encoding file by running the following command in the CiME2 tool:
```
#load "dirac.cim2";
```
The term rewriting system is defined as `R` after loading the file. Then to check the confluence, type in the following command:
```
confluence R；
```
And the tool will confirm that all critical pairs are joinable, which means the system is confluent.