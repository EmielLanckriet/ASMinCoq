From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.
From ASMinCoq Require Import CpdtTactics.
From ASMinCoq Require Import AsmGen progLog.




(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{!invG Σ, !memG Σ, !regG Σ, !traceG (list leak) Σ, !pcG Σ, !programG Σ,
    !memG Σ', !regG Σ', !traceG (list leak) Σ', !pcG Σ', !programG Σ'} :
      irisGS asm_lang2 (Σ * Σ')
      := {
  iris_invGS := inv_invG;
  state_interp σ _ κs _ :=
    ((gen_heap_interp (reg σ.1.1.2)) ∗
    (gen_heap_interp (mem σ.1.1.2)) ∗
    tr_auth trace_name σ.2 ∗ pc_auth PC_name (PC σ.1.1.2) ∗
    program_auth Program_name σ.1.1.1
    ∗
    (gen_heap_interp (reg σ.2.1.2)) ∗
    (gen_heap_interp (mem σ.2.1.2)) ∗
    tr_auth trace_name σ.2.2 ∗ pc_auth PC_name (PC σ.2.1.2) ∗
    program_auth Program_name σ.2.1.1)%I;
  fork_post _ := False%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.