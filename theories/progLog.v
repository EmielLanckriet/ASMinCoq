From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.

Section wp'.
  Context {Λ : language} `{!irisGS_gen hlc Λ Σ}.

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
      (Instr Executable) @ E
    {{{ RET HaltedV; program_frag Program_name prog ∗ pc_frag PC_name pc ∗ tr_frag trace_name (NoLeak :: ll) }}}.
  Proof.
    iIntros (prpcHalt Φ) "(Hprog & Hpc & Hll) HΦ".
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
      + iPureIntro. reflexivity.
      + iApply "HΦ". iFrame.
  Qed.

  Fixpoint regs_from_inputs {n : nat} (inputs : vec (Word + Register) n) : gset Register :=
    match inputs with
    | [# ] => ∅
    | wr ::: inputs' => match wr with
                        | inl _ => regs_from_inputs inputs'
                        | inr r => {[ r ]} ∪ regs_from_inputs inputs'
                        end
    end.

  Fixpoint replace_in_inputs {n : nat} (words : list Word) (inputs : vec (Word + Register) n)
    : vec Word n :=
    match inputs, words with
    | Vector.nil, _ => Vector.nil
    | Vector.cons input inputs', [] => match input with
                                | inl word => Vector.cons word (replace_in_inputs words inputs')
                                | inr _ => Vector.cons 0 (replace_in_inputs words inputs')
                                end
    | Vector.cons input inputs', word' :: words' => match input with
                                | inl word => Vector.cons word (replace_in_inputs words inputs')
                                | inr _ => Vector.cons word' (replace_in_inputs words' inputs')
                                end
    end.

  Definition regs_of_argument (arg: Word + Register) : gset Register :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
  end.

Definition regs_of (i: instr): gset Register :=
match i with
    | Computation inputs rres f_result => {[ rres ]} ∪ regs_from_inputs inputs
    | ControlFlow inputs dst f_condition => regs_of_argument dst ∪ regs_from_inputs inputs
    | Load rres rsrc => {[ rres; rsrc ]}
    | Store rdst src => {[ rdst ]} ∪ regs_of_argument src
    | _ => ∅
end.

Lemma indom_regs_incl D (regs regs': Reg) :
  D ⊆ dom regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:Word), (regs !! r = Some w) ∧ (regs' !! r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (regs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset Register). typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

Lemma indom_regs_incl_default D (regs regs': Reg) :
  D ⊆ dom regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:Word), (regs !!! r = w) ∧ (regs' !!! r = w).
Proof.
  intros * HD Hincl rr Hr.
  specialize (indom_regs_incl _ _ _ HD Hincl rr Hr) as [w [Hw Hw']].
  unfold "!!!". unfold map_lookup_total. unfold default. simpl. rewrite Hw.
  exists w. split; auto. rewrite (lookup_weaken _ _ _ _ Hw Hincl). reflexivity.
Qed.

Lemma gen_heap_update_inSepM :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapGS L V Σ}
      (σ σ' : gmap L V) (l : L) (v : V),
      is_Some (σ' !! l) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), mapsto k (DfracOwn 1) y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.

  Lemma gen_heap_valid_inSepM':
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜forall (l: L) (v: V), σ' !! l = Some v → σ !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inclSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k (DfracOwn q) y) -∗
      ⌜σ' ⊆ σ⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ !! l) eqn:HH; naive_solver.
  Qed.

Lemma inputs_are_enough {B : Type} {n : nat} regs regs' (f_result : vec Word n -> B) (inputs : vec (Word + Register) n)
  (inputs_in_regs : regs_from_inputs inputs ⊆ dom regs)
  (regs_in_regs' : regs ⊆ regs') :
  f_result (inputs_from_inputnatregs regs inputs) = f_result (inputs_from_inputnatregs regs' inputs).
Proof.
  induction inputs.
  - reflexivity.
  - destruct h.
    + simpl. unfold regs_from_inputs in inputs_in_regs. simpl in inputs_in_regs.
      apply (IHinputs (fun inputs' => f_result (w ::: inputs'))) in inputs_in_regs.
      apply inputs_in_regs.
    + simpl. specialize (indom_regs_incl_default _ _ _ inputs_in_regs regs_in_regs' r) as Hri.
      destruct Hri.
      { set_solver+. }
      destruct H as [Hregs Hregs']. rewrite Hregs Hregs'.
      simpl in inputs_in_regs. apply union_subseteq in inputs_in_regs. 
      apply (IHinputs (fun inputs' => f_result (x ::: inputs'))).
      destruct inputs_in_regs as [_ ->]. reflexivity.
Qed.

Lemma regs_of_computation {n : nat} (inputs : vec (Word + Register) n)
    (rres : Register) (f_result : vec Word n -> Word) i :
    i = Computation inputs rres f_result ->
    regs_of i = {[ rres ]} ∪ regs_from_inputs inputs.
Proof.
  intros. subst.
  reflexivity.
Qed.

Inductive Computation_spec {n : nat} (i: instr) (regs : Reg) (regs' : Reg) : Prop :=
  | Computation_spec_success vn (inputs : vec (Word + Register) n) f_result (rres : Register) :
      inputs_from_inputnatregs regs inputs = vn ->
      (<[ rres := f_result vn ]> regs) = regs' ->
      i = Computation inputs rres f_result ->
      Computation_spec i regs regs'.

Lemma wp_computation {n : nat} pc prog ll E (inputs : vec (Word + Register) n) rres f_result regs :
  prog pc = Computation inputs rres f_result ->
  regs_of (Computation inputs rres f_result) ⊆ dom regs →
  {{{ program_frag Program_name prog ∗ pc_frag PC_name pc ∗ tr_frag trace_name ll ∗
      [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      (Instr Executable) @ E
  {{{ regs', RET NextIV; program_frag Program_name prog ∗ pc_frag PC_name (pc + 1) ∗ tr_frag trace_name (NoLeak :: ll) ∗
    ⌜ Computation_spec (n := n) (Computation inputs rres f_result) regs regs' ⌝ ∗
    [∗ map] k↦y ∈ regs', k ↦ᵣ y
     }}}.
  Proof.
    iIntros (prpcHalt regs_subset Φ) "(Hprog & Hpc & Hll & HlistOfRegs) HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@pc_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@program_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iPoseProof (trace_update trace_name _ (NoLeak :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (pc_update PC_name _ (PC (s.2) + 1) with "[$Hauthpc $Hpc]") as "H2".
    

    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    specialize (indom_regs_incl _ _ _ regs_subset Hregs) as Hri.
    destruct (Hri rres) as [wdst [H'dst Hdst]]. by set_solver+.        
    iMod "H1". iMod "H2". iModIntro.

    iDestruct "H1" as "[Hauthll Hfragll]". iDestruct "H2" as "[Hauthpc Hfragpc]".
    iSplitR.
    - iPureIntro. apply normal_always_reducible.
    - iIntros (e2 σ2 efs) "%steps _".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.     
      iFrame.
      unfold incr_PC. rewrite -(update_pc_no_change_reg).
      rewrite reg_is_updated_value.
      iMod ((gen_heap_update_inSepM _ _ rres) with "Hreg HlistOfRegs") as "[Hr Hmap]".
      { eauto.  }
      iModIntro. iNext. iModIntro.
      iFrame.
      iSplitR.
      { iPureIntro. reflexivity. }
      iApply "HΦ". iFrame.
      iPureIntro.
      econstructor; try reflexivity.
      rewrite (inputs_are_enough regs (reg φ)); auto. apply union_subseteq in regs_subset as [_ ->]. reflexivity.
Qed.

Lemma regs_of_control_flow {n : nat} (inputs : vec (Word + Register) n)
    (dst : Word + Register) (f_condition : vec Word n -> bool) i :
    i = ControlFlow inputs dst f_condition ->
    regs_of i = regs_of_argument dst ∪ regs_from_inputs inputs.
Proof.
  intros. subst.
  reflexivity.
Qed.

Inductive Control_flow_spec {n : nat} (i : instr) (pc pc' : Word) : Prop :=
  | Control_flow_spec_true_success vn (inputs : vec (Word + Register) n) (regs : Reg) f_condition (dst : Word + Register) :
      inputs_from_inputnatregs regs inputs = vn ->
      f_condition vn = true ->
      wordreg_to_word regs dst = pc' ->
      i = ControlFlow inputs dst f_condition ->
      Control_flow_spec i pc pc'
  | Control_flow_spec_false_success vn (inputs : vec (Word + Register) n) (regs : Reg) f_condition (dst : Word + Register) :
      inputs_from_inputnatregs regs inputs = vn ->
      f_condition vn = false ->
      pc + 1 = pc' ->
      i = ControlFlow inputs dst f_condition ->
      Control_flow_spec i pc pc'.

Lemma wp_control_flow {n : nat} pc prog ll E (inputs : vec (Word + Register) n) dst f_condition regs :
  prog pc = ControlFlow inputs dst f_condition ->
  regs_of (ControlFlow inputs dst f_condition) ⊆ dom regs →
  {{{ program_frag Program_name prog ∗ pc_frag PC_name pc ∗ tr_frag trace_name ll ∗
      [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      (Instr Executable) @ E
  {{{ pc', RET NextIV; program_frag Program_name prog ∗ pc_frag PC_name pc' ∗ tr_frag trace_name (ControlFlowLeak (f_condition (inputs_from_inputnatregs (regs) inputs)) :: ll) ∗
    ⌜ Control_flow_spec (n := n) (ControlFlow inputs dst f_condition) pc pc' ⌝ ∗
    [∗ map] k↦y ∈ regs, k ↦ᵣ y
     }}}.
  Proof.
    iIntros (prpcHalt regs_subset Φ) "(Hprog & Hpc & Hll & HlistOfRegs) HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@pc_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@program_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.   
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible.
    - iIntros (e2 σ2 efs) "%steps _".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.
      destruct (f_condition (inputs_from_inputnatregs (reg φ) inputs)) as [|] eqn:Hcondition.
      all: iPoseProof (trace_update trace_name _ (ControlFlowLeak (f_condition (inputs_from_inputnatregs (reg φ) inputs)) :: ll) with "[$Hauthtrace $Hll]") as "H1".
      1: iPoseProof (pc_update PC_name _ (wordreg_to_word (reg φ) dst) with "[$Hauthpc $Hpc]") as "H2".
      2: iPoseProof (pc_update PC_name _ (PC φ + 1) with "[$Hauthpc $Hpc]") as "H2".
      all: iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]";
      rewrite Hcondition; iFrame.
      all: iModIntro; iNext; iModIntro.
      all: iSplitR; try (iPureIntro; reflexivity).
      all: iApply "HΦ".
      all: assert ((f_condition (inputs_from_inputnatregs regs inputs) = f_condition (inputs_from_inputnatregs (reg φ) inputs))) as Hreg_regφ;
      try (apply (inputs_are_enough regs (reg φ)); auto; apply union_subseteq in regs_subset as [_ ->]; reflexivity); rewrite Hreg_regφ Hcondition.
      all: iFrame.
      all: iPureIntro.
      + eapply Control_flow_spec_true_success; eauto.
      + eapply Control_flow_spec_false_success; eauto.
Qed.

Lemma wp_load {n : nat} pc prog ll E rres rsrc regs v :
  prog pc = Load rres rsrc ->
  regs_of (Load rres rsrc) ⊆ dom regs →
  {{{ program_frag Program_name prog ∗ pc_frag PC_name pc ∗ tr_frag trace_name ll ∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
      word_to_addr (regs !!! rsrc) ↦ₐ v }}}
      (Instr Executable) @ E
  {{{ RET NextIV; program_frag Program_name prog ∗ pc_frag PC_name (pc + 1) ∗
      tr_frag trace_name (LoadLeak (regs !!! rsrc) :: ll) ∗
      [∗ map] k↦y ∈ <[ rres := v ]>regs, k ↦ᵣ y
     }}}.
  Proof.
    iIntros (prpcHalt regs_subset Φ) "(Hprog & Hpc & Hll & HlistOfRegs & Haddrv) HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@pc_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@program_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible. }
    iIntros (e2 σ2 efs) "%steps _".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update trace_name _ (LoadLeak (reg φ !!! rsrc) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (pc_update PC_name _ (PC φ + 1) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite reg_is_updated_value.
    iMod ((gen_heap_update_inSepM _ _ rres) with "Hreg HlistOfRegs") as "[Hr Hmap]".
    { eapply @elem_of_dom with (D := gset Register). typeclasses eauto.
    eapply elem_of_subseteq; eauto. set_solver. }
    iPoseProof (gen_heap_valid with "Hmem Haddrv") as "%Hmem'".
    iModIntro. iNext. iModIntro. iFrame.
    iSplitR.
    { iPureIntro. reflexivity. }
    
    iApply "HΦ"; iFrame.
    specialize (indom_regs_incl_default _ _ _ regs_subset Hregs rsrc) as Hri.
    destruct Hri as [w [Hw Hw']]. { set_solver. }
    rewrite Hw. rewrite Hw'. iFrame.
    rewrite Hw in Hmem'. unfold word_to_addr in Hmem'.
    assert (mem φ !!! w = v) as Hmem''. { unfold "!!!". unfold map_lookup_total. unfold default. rewrite Hmem'. reflexivity. }
    rewrite Hmem''. iFrame.
Qed.

Lemma wp_store {n : nat} pc prog ll E rdst src regs v :
  prog pc = Store rdst src ->
  regs_of (Store rdst src) ⊆ dom regs →
  {{{ program_frag Program_name prog ∗ pc_frag PC_name pc ∗ tr_frag trace_name ll ∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
      word_to_addr (regs !!! rdst) ↦ₐ v }}}
      (Instr Executable) @ E
  {{{ RET NextIV; program_frag Program_name prog ∗ pc_frag PC_name (pc + 1) ∗
      tr_frag trace_name (StoreLeak (wordreg_to_word regs src) :: ll) ∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
      word_to_addr (regs !!! rdst) ↦ₐ wordreg_to_word regs src
     }}}.
  Proof.
    iIntros (prpcHalt regs_subset Φ) "(Hprog & Hpc & Hll & HlistOfRegs & Haddrv) HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@pc_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@program_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible. }
    iIntros (e2 σ2 efs) "%steps _".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update trace_name _ (StoreLeak (wordreg_to_word regs src) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (pc_update PC_name _ (PC φ + 1) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite -update_mem_no_change_reg.
    iPoseProof (gen_heap_valid with "Hmem Haddrv") as "%Hmem'".
    
    iMod ((gen_heap_update _ (regs !!! rdst)) with "Hmem Haddrv") as "[Hr Hmap]".
    specialize (indom_regs_incl_default _ _ _ regs_subset Hregs rdst) as Hri.
    destruct Hri as [w [Hw Hw']]. { set_solver. }
    rewrite Hw Hw'.

    iModIntro. iNext. iModIntro. iFrame.
    iSplitR.
    { iPureIntro. reflexivity. }
    
    iSplitL "Hauthll".
    all: destruct src; simpl; iFrame.
    all: try iApply "HΦ"; iFrame.
    all: specialize (indom_regs_incl_default _ _ _ regs_subset Hregs r) as Hri.
    all: destruct Hri as [w1 [Hw1 Hw1']]; try set_solver; rewrite Hw1 Hw1'; iFrame.
Qed.




End asm_lang_rules.