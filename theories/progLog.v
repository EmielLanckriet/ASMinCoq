From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap excl.
From ASMinCoq Require Export AsmGen.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invGS Σ;
  mem_gen_memG :: gen_heapGS Addr Word Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invGS Σ;
  reg_gen_regG :: gen_heapGS Reg Word Σ; }.


(* Stuff for the trace copied from Katamaran *)
Class traceG (Trace : Type) Σ := TraceG {
    trace_inG :: inG Σ (authR (optionUR (exclR (leibnizO Trace))));
    trace_name : gname
}.

Definition tracePreΣ (Trace : Type) : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO Trace))))].

Class trace_preG (Trace : Type) Σ := {
  trace_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO Trace))));
}.

#[export] Instance traceG_preG `{traceG T Σ} : trace_preG T Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance subG_tracePreΣ {Σ T}:
  subG (tracePreΣ T) Σ →
  trace_preG T Σ.
Proof. solve_inG. Qed.

Section S.
  Context `{!trace_preG T Σ}.
  Context (γ : gname). (* To allow using different gnames *)

  Definition tr_auth (t: T) : iProp Σ := own γ (● (Some (Excl (t: leibnizO T)))).
  Definition tr_frag (t: T) : iProp Σ := own γ (◯ (Some (Excl (t: leibnizO T)))).

  Lemma trace_full_frag_eq t t':
    tr_auth t -∗ tr_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi.  apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma tr_frag_excl t t' :
    tr_frag t -∗ tr_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma trace_update t t' :
    tr_auth t ∗ tr_frag t ==∗
    tr_auth t' ∗ tr_frag t'.
  Proof.
    rewrite /tr_auth /tr_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance tr_auth_Timeless t : Timeless (tr_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance tr_frag_Timeless t : Timeless (tr_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

(* Stuff for the PC *)
Class pcG Σ := PcG {
    PC_inG :: inG Σ (authR (optionUR (exclR (leibnizO Word))));
    PC_name : gname
}.

Definition PcPreΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO 
Word))))].

Class PC_preG Σ := {
  PC_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO Word))));
}.

#[export] Instance PcG_preG `{pcG Σ} : PC_preG Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance subG_PcPreΣ {Σ}:
  subG PcPreΣ Σ →
  PC_preG Σ.
Proof. solve_inG. Qed.

Section S.
  Context `{!PC_preG Σ}.
  Context (γ : gname). (* To allow using different gnames *)

  Definition pc_auth (w : Word) : iProp Σ := own γ (● (Some (Excl (w : leibnizO Word)))).
  Definition pc_frag (w : Word) : iProp Σ := own γ (◯ (Some (Excl (w : leibnizO Word)))).

  Lemma pc_full_frag_eq t t':
    pc_auth t -∗ pc_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi. apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma pc_frag_excl t t' :
    pc_frag t -∗ pc_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma pc_update t t' :
    pc_auth t ∗ pc_frag t ==∗
    pc_auth t' ∗ pc_frag t'.
  Proof.
    rewrite /pc_auth /pc_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance pc_auth_Timeless t : Timeless (pc_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance pc_frag_Timeless t : Timeless (pc_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

(* Stuff for the prog *)
Class programG Σ := ProgramG {
    Program_inG :: inG Σ (authR (optionUR (exclR (leibnizO program))));
    Program_name : gname
}.

Definition ProgramPreΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO program))))].

Class Program_preG Σ := {
  Program_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO program))));
}.

#[export] Instance ProgramG_preG `{programG Σ} : Program_preG Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance subG_ProgramPreΣ {Σ}:
  subG ProgramPreΣ Σ →
  Program_preG Σ.
Proof. solve_inG. Qed.

Section S.
  Context `{!Program_preG Σ}.
  Context (γ : gname). (* To allow using different gnames *)

  Definition program_auth (p : program) : iProp Σ := own γ (● (Some (Excl (p : leibnizO program)))).
  Definition program_frag (p : program) : iProp Σ := own γ (◯ (Some (Excl (p : leibnizO program)))).

  Lemma program_full_frag_eq t t':
    program_auth t -∗ program_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi. apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma program_frag_excl t t' :
    program_frag t -∗ program_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma program_update t t' :
    program_auth t ∗ program_frag t ==∗
    program_auth t' ∗ program_frag t'.
  Proof.
    rewrite /program_auth /program_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance program_auth_Timeless t : Timeless (program_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance program_frag_Timeless t : Timeless (program_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{!memG Σ, !regG Σ, !traceG (list leak) Σ, !pcG Σ, !programG Σ} : irisGS asm_lang Σ := {
  iris_invGS := mem_invG;
  state_interp σ _ κs _ := ((gen_heap_interp σ.1.2.1.2) ∗ (gen_heap_interp σ.1.2.2) ∗ tr_auth trace_name σ.2 ∗ pc_auth PC_name σ.1.2.1.1 ∗ program_auth Program_name σ.1.1)%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.