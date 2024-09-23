From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth.
From ASMinCoq Require Export AsmGen.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invGS Σ;
  mem_gen_memG :: gen_heapGS Addr Word Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invGS Σ;
  reg_gen_regG :: gen_heapGS Reg Word Σ; }.


(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{!memG Σ, !regG Σ} : irisGS asm_lang Σ := {
  iris_invGS := mem_invG;
  state_interp σ _ κs _ := ((gen_heap_interp σ.1) ∗ (gen_heap_interp σ.2))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.