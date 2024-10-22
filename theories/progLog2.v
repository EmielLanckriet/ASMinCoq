From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.
From ASMinCoq Require Import CpdtTactics.
From ASMinCoq Require Import AsmGen.


(* CMRA for invariants *)
Class invG Σ := InvG {
  inv_invG : invGS Σ;}.

(* CMRΑ for memory *)
Class mem1G Σ := Mem1G {
  mem_gen_mem1G :: gen_heapGS Addr Word Σ}.

Class mem2G Σ := Mem2G {
  mem_gen_mem2G :: gen_heapGS Addr Word Σ}.

(* CMRA for registers *)
Class reg1G Σ := Reg1G {
  reg_gen_reg1G :: gen_heapGS Reg Word Σ; }.

Class reg2G Σ := Reg2G {
  reg_gen_reg2G :: gen_heapGS Reg Word Σ; }.


(* Stuff for the trace copied from Katamaran *)
Class trace1G (Trace : Type) Σ := Trace1G {
    trace1_inG :: inG Σ (authR (optionUR (exclR (leibnizO Trace))));
    trace1_name : gname
}.

Class trace2G (Trace : Type) Σ := Trace2G {
    trace2_inG :: inG Σ (authR (optionUR (exclR (leibnizO Trace))));
    trace2_name : gname
}.

Definition trace1PreΣ (Trace : Type) : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO Trace))))].
Definition trace2PreΣ (Trace : Type) : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO Trace))))].

Class trace1_preG (Trace : Type) Σ := {
  trace1_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO Trace))));
}.

Class trace2_preG (Trace : Type) Σ := {
  trace2_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO Trace))));
}.

#[export] Instance trace1G_preG `{trace1G T Σ} : trace1_preG T Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance trace2G_preG `{trace2G T Σ} : trace2_preG T Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance subG_trace1PreΣ {Σ T}:
  subG (trace1PreΣ T) Σ →
  trace1_preG T Σ.
Proof. solve_inG. Qed.

#[export] Instance subG_trace2PreΣ {Σ T}:
  subG (trace2PreΣ T) Σ →
  trace2_preG T Σ.
Proof. solve_inG. Qed.


Section S.
  Context `{!trace1_preG T Σ}.
  Context (γ : gname).

  Definition tr1_auth (t : T) : iProp Σ := own γ  (● (Some (Excl (t : leibnizO T)))).
  Definition tr1_frag (t : T) : iProp Σ := own γ (◯ (Some (Excl (t : leibnizO T)))).

  Lemma trace1_full_frag_eq t t':
    tr1_auth t -∗ tr1_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi.  apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma tr1_frag_excl t t' :
    tr1_frag t -∗ tr1_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma trace1_update t t' :
    tr1_auth t ∗ tr1_frag t ==∗
    tr1_auth t' ∗ tr1_frag t'.
  Proof.
    rewrite /tr1_auth /tr1_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance tr1_auth_Timeless t : Timeless (tr1_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance tr1_frag_Timeless t : Timeless (tr1_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

Section S.
  Context `{!trace2_preG T Σ}.
  Context (γ : gname).

  Definition tr2_auth (t : T) : iProp Σ := own γ (● (Some (Excl (t : leibnizO T)))).
  Definition tr2_frag (t : T) : iProp Σ := own γ (◯ (Some (Excl (t : leibnizO T)))).

  Lemma trace2_full_frag_eq t t':
    tr2_auth t -∗ tr2_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi.  apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma tr2_frag_excl t t' :
    tr2_frag t -∗ tr2_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma trace2_update t t' :
    tr2_auth t ∗ tr2_frag t ==∗
    tr2_auth t' ∗ tr2_frag t'.
  Proof.
    rewrite /tr2_auth /tr2_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance tr2_auth_Timeless t : Timeless (tr2_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance tr2_frag_Timeless t : Timeless (tr2_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

(* Stuff for the PC *)
Class pc1G Σ := Pc1G {
    pc1_inG :: inG Σ (authR (optionUR (exclR (leibnizO Word))));
    pc1_name : gname
}.

Class pc2G Σ := Pc2G {
    pc2_inG :: inG Σ (authR (optionUR (exclR (leibnizO Word))));
    pc2_name : gname
}.

Definition Pc1PreΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO 
Word))))].

Definition Pc2PreΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO 
Word))))].

Class PC1_preG Σ := {
  PC1_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO Word))));
}.

Class PC2_preG Σ := {
  PC2_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO Word))));
}.

#[export] Instance Pc1G_preG `{pc1G Σ} : PC1_preG Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance Pc2G_preG `{pc2G Σ} : PC2_preG Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance subG_Pc1PreΣ {Σ}:
  subG Pc1PreΣ Σ →
  PC1_preG Σ.
Proof. solve_inG. Qed.

#[export] Instance subG_Pc2PreΣ {Σ}:
  subG Pc2PreΣ Σ →
  PC2_preG Σ.
Proof. solve_inG. Qed.

Section S.
  Context `{!pc1G Σ}.
  Context (γ : gname).

  Definition pc1_auth (w : Word) : iProp Σ := own γ (● (Some (Excl (w : leibnizO Word)))).
  Definition pc1_frag (w : Word) : iProp Σ := own γ (◯ (Some (Excl (w : leibnizO Word)))).

  Lemma pc1_full_frag_eq t t':
    pc1_auth t -∗ pc1_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi. apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma pc1_frag_excl t t' :
    pc1_frag t -∗ pc1_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma pc1_update t t' :
    pc1_auth t ∗ pc1_frag t ==∗
    pc1_auth t' ∗ pc1_frag t'.
  Proof.
    rewrite /pc1_auth /pc1_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance pc1_auth_Timeless t : Timeless (pc1_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance pc1_frag_Timeless t : Timeless (pc1_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

Section S.
  Context `{!pc2G Σ}.
  Context (γ : gname).

  Definition pc2_auth (w : Word) : iProp Σ := own γ (● (Some (Excl (w : leibnizO Word)))).
  Definition pc2_frag (w : Word) : iProp Σ := own γ (◯ (Some (Excl (w : leibnizO Word)))).

  Lemma pc2_full_frag_eq t t':
    pc2_auth t -∗ pc2_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi. apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma pc2_frag_excl t t' :
    pc2_frag t -∗ pc2_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma pc2_update t t' :
    pc2_auth t ∗ pc2_frag t ==∗
    pc2_auth t' ∗ pc2_frag t'.
  Proof.
    rewrite /pc2_auth /pc2_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance pc2_auth_Timeless t : Timeless (pc2_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance pc2_frag_Timeless t : Timeless (pc2_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

(* Stuff for the prog *)
Class program1G Σ := Program1G {
    program1_inG :: inG Σ (authR (optionUR (exclR (leibnizO program))));
    program1_name : gname
}.

Class program2G Σ := Program2G {
    program2_inG :: inG Σ (authR (optionUR (exclR (leibnizO program))));
    program2_name : gname
}.

Definition Program1PreΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO program))))].
Definition Program2PreΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (leibnizO program))))].

Class Program1_preG Σ := {
  Program1_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO program))));
}.

Class Program2_preG Σ := {
  Program2_preG_inG :: inG Σ (authR (optionUR (exclR (leibnizO program))));
}.

#[export] Instance Program1G_preG `{program1G Σ} : Program1_preG Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance Program2G_preG `{program2G Σ} : Program2_preG Σ.
Proof. constructor. typeclasses eauto. Defined.

#[export] Instance subG_Program1PreΣ {Σ}:
  subG Program1PreΣ Σ →
  Program1_preG Σ.
Proof. solve_inG. Qed.

#[export] Instance subG_Program2PreΣ {Σ}:
  subG Program2PreΣ Σ →
  Program2_preG Σ.
Proof. solve_inG. Qed.

Section S.
  Context `{!program1G Σ}.
  Context (γ : gname).

  Definition program1_auth (p : program) : iProp Σ := own γ (● (Some (Excl (p : leibnizO program)))).
  Definition program1_frag (p : program) : iProp Σ := own γ (◯ (Some (Excl (p : leibnizO program)))).

  Lemma program1_full_frag_eq t t':
    program1_auth t -∗ program1_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi. apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma program1_frag_excl t t' :
    program1_frag t -∗ program1_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma program1_update t t' :
    program1_auth t ∗ program1_frag t ==∗
    program1_auth t' ∗ program1_frag t'.
  Proof.
    rewrite /program1_auth /program1_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance program1_auth_Timeless t : Timeless (program1_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance program1_frag_Timeless t : Timeless (program1_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

Section S.
  Context `{!program2G Σ}.
  Context (γ : gname).

  Definition program2_auth (p : program) : iProp Σ := own γ (● (Some (Excl (p : leibnizO program)))).
  Definition program2_frag (p : program) : iProp Σ := own γ (◯ (Some (Excl (p : leibnizO program)))).

  Lemma program2_full_frag_eq t t':
    program2_auth t -∗ program2_frag t' -∗
    ⌜ t = t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hi Hv]%auth_both_valid_discrete.
    rewrite Excl_included in Hi. apply leibniz_equiv in Hi. subst; auto.
  Qed.

  Lemma program2_frag_excl t t' :
    program2_frag t -∗ program2_frag t' -∗ ⌜ False ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    now apply excl_auth.excl_auth_frag_op_valid in Hv.
  Qed.

  Lemma program2_update t t' :
    program2_auth t ∗ program2_frag t ==∗
    program2_auth t' ∗ program2_frag t'.
  Proof.
    rewrite /program2_auth /program2_frag. rewrite -!own_op.
    iApply own_update. apply auth_update.
    apply option_local_update.
    apply exclusive_local_update. constructor.
  Qed.

  (* For the moment, there is no need for a lemma stating that traces can only be appened to, but we could customize the RA to enforce this. *)

  #[export] Instance program2_auth_Timeless t : Timeless (program2_auth t).
  Proof.
    intros. apply _.
  Qed.

  #[export] Instance program2_frag_Timeless t : Timeless (program2_frag t).
  Proof.
    intros. apply _.
  Qed.
End S.

(* A lot of duplication for the resources right now.
   Since only 2 types of resources are used heaps (with gen_heap_interp)
   and exclusive (with copy paste for Katamaran),
   it should be possible to get rid of most copy paste.
  *)


(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG
  `{!invG Σ,
    !mem1G Σ, !reg1G Σ, !trace1G (list leak) Σ, !pc1G Σ, !program1G Σ,
    !mem2G Σ, !reg2G Σ, !trace2G (list leak) Σ, !pc2G Σ, !program2G Σ
} : irisGS asm_lang2 Σ
      := {
  iris_invGS := inv_invG;
  state_interp σ _ κs _ :=
    ((gen_heap_interp (reg σ.1.1.2)) ∗
    (gen_heap_interp (mem σ.1.1.2)) ∗
    tr1_auth trace1_name σ.1.2 ∗ pc1_auth pc1_name (PC σ.1.1.2) ∗
    program1_auth program1_name σ.1.1.1
    ∗
    (gen_heap_interp (reg σ.2.1.2)) ∗
    (gen_heap_interp (mem σ.2.1.2)) ∗
    tr2_auth trace2_name σ.2.2 ∗ pc2_auth pc2_name (PC σ.2.1.2) ∗
    program2_auth program2_name σ.2.1.1)%I;
  fork_post _ := False%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section asm_lang_rules.
  Context `{!invG Σ,
  !mem1G Σ, !reg1G Σ, !trace1G (list leak) Σ, !pc1G Σ, !program1G Σ,
  !mem2G Σ, !reg2G Σ, !trace2G (list leak) Σ, !pc2G Σ, !program2G Σ
}.
  Context (γ ζ ξ : gname).
(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (mapsto (L:=Register) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦1ᵣ w" := (mapsto (L:=Register) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "r ↦2ᵣ w" := (mapsto (L:=Register) (V:=Word) r (DfracOwn 2) w) (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (mapsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦1ₐ w" := (mapsto (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.
Notation "a ↦2ₐ w" := (mapsto (L:=Addr) (V:=Word) a (DfracOwn 2) w) (at level 20) : bi_scope.

Lemma wp_halt pc prog ll E Φ :
    prog pc = Halt ->
    program1_frag program1_name prog -∗ pc1_frag pc1_name pc -∗ tr1_frag trace1_name ll -∗
    program2_frag program2_name prog -∗ pc2_frag pc2_name pc -∗ tr2_frag trace2_name ll -∗
    ▷ (program1_frag program1_name prog ∗ pc1_frag pc1_name pc ∗ tr1_frag trace1_name (NoLeak :: ll) -∗
       program2_frag program2_name prog ∗ pc2_frag pc2_name pc ∗ tr2_frag trace2_name (NoLeak :: ll) -∗
      Φ HaltedV) -∗
    WP (Instr Executable, Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt) "Hprog Hpc Hll HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hauthreg & Hauthmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@pc_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@program_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible.
    - iIntros (e2 σ2 efs) "%steps test".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *. iFrame.
      iPoseProof (trace_update trace_name _ (NoLeak :: ll) with "[$Hauthtrace $Hll]") as "H".
      iMod "H". iModIntro. iNext. iModIntro.
      iDestruct "H" as "[Hauthll Hfragll]". iFrame.
      iSplitR.
      { iPureIntro; reflexivity. }
      iApply "HΦ". iFrame.
  Qed.


