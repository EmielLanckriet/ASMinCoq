From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap excl.

Section wp'.
  Context {Λ : language} `{!irisGS_gen hlc Λ Σ}.

  Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 efs ?) "Hcred". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#] Hcred") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

  Lemma wp_lift_atomic_step_no_fork_fupd {s E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
      ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
      ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
        ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs nt ∗ from_option Φ False (to_val e2))
    ⊢ WP e1 @ s; E1 {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
    iIntros (v2 σ2 efs Hstep) "Hcred".
    iMod ("H" $! v2 σ2 efs with "[# //] Hcred") as "H".
    iIntros "!> !>". iMod "H" as "(-> & ? & ?) /=". by iFrame.
  Qed.

End wp'.


From ASMinCoq Require Export AsmGen.


(* CMRA for invariants *)
Class invG Σ := InvG {
  inv_invG : invGS Σ;}.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_gen_memG :: gen_heapGS Addr Word Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
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
Global Instance memG_irisG `{!invG Σ, !memG Σ, !regG Σ, !traceG (list leak) Σ, !pcG Σ, !programG Σ} : irisGS asm_lang Σ := {
  iris_invGS := inv_invG;
  state_interp σ _ κs _ := ((gen_heap_interp (reg σ.1.2)) ∗ (gen_heap_interp (mem σ.1.2)) ∗ tr_auth trace_name σ.2 ∗ pc_auth PC_name (PC σ.1.2) ∗ program_auth Program_name σ.1.1)%I;
  fork_post _ := False%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Section asm_lang_rules.
  Context `{!invG Σ, !memG Σ, !regG Σ, !traceG (list leak) Σ, !pcG Σ, !programG Σ}.
  Context (γ ζ ξ : gname).
(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (mapsto (L:=Register) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (mapsto (L:=Register) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (mapsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦ₐ w" := (mapsto (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.

(* ------------------------- registers points-to --------------------------------- *)

  Lemma register_dupl_false r w1 w2 :
    r ↦ᵣ w1 -∗ r ↦ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %H.
    destruct H as [H1 H2]. eapply dfrac_full_exclusive in H1. auto.
  Qed.

  Lemma register_neq r1 r2 w1 w2 :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (register_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: Register) (w1: Word) :
    r1 ↦ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma regs_of_map_1 (r1: Register) (w1: Word) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y) -∗
    r1 ↦ᵣ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma map_of_regs_2 (r1 r2: Register) (w1 w2: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (register_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: Register) (w1 w2: Word) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: Register) (w1 w2 w3: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (register_neq with "H1 H2") as "%".
    iPoseProof (register_neq with "H1 H3") as "%".
    iPoseProof (register_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_3 (r1 r2 r3: Register) (w1 w2 w3: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: Register) (w1 w2 w3 w4: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗ r4 ↦ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4 ∧ r2 ≠ r3 ∧ r2 ≠ r4 ∧ r3 ≠ r4 ⌝.
  Proof.
    iIntros "H1 H2 H3 H4".
    iPoseProof (register_neq with "H1 H2") as "%".
    iPoseProof (register_neq with "H1 H3") as "%".
    iPoseProof (register_neq with "H1 H4") as "%".
    iPoseProof (register_neq with "H2 H3") as "%".
    iPoseProof (register_neq with "H2 H4") as "%".
    iPoseProof (register_neq with "H3 H4") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_4 (r1 r2 r3 r4: Register) (w1 w2 w3 w4: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3 ∗ r4 ↦ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* ------------------------- memory points-to --------------------------------- *)

  Lemma addr_dupl_false a w1 w2 :
    a ↦ₐ w1 -∗ a ↦ₐ w2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (mapsto_valid_2 with "Ha1 Ha2") as %H.
    destruct H as [H1 H2]. eapply dfrac_full_exclusive in H1.
    auto.
  Qed.

  Lemma wp_halt pc prog ll E :
    prog pc = Halt ->
    {{{ program_frag Program_name prog ∗ pc_frag PC_name pc ∗ tr_frag trace_name ll }}}
      NextI @ E
    {{{ RET HaltedV; program_frag Program_name prog ∗ pc_frag PC_name pc ∗ tr_frag trace_name (NoLeak :: ll) }}}.
  Proof.
    iIntros (prpcHalt Φ) "(Hprog & Hpc & Hll) HΦ".
    iApply wp_lift_atomic_step_fupd; auto.
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
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *. iFrame.
      iPoseProof (trace_update trace_name _ (NoLeak :: ll) with "[$Hauthtrace $Hll]") as "H".
      iMod "H". iModIntro. iNext. iModIntro.
      iDestruct "H" as "[Hauthll Hfragll]". iFrame.
      iSplitR "test".
      + iApply "HΦ". iFrame.
      + 


  End asm_lang_rules.