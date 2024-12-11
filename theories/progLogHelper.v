From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export ectx_lifting total_lifting.
From iris.algebra Require Import frac auth gmap excl.

(* Local Variables: *)
(* proof-omit-proofs-option: t *)
(* End: *)


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

  Lemma twp_lift_atomic_step_no_fork_fupd {s E1 Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E1}=∗
     ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
     ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝  ={E1}=∗
         ⌜κ = []⌝ ∗⌜efs = []⌝ ∗
         state_interp σ2 (S ns) κs nt ∗ from_option Φ False (to_val e2))
    ⊢ twp s E1 e1 Φ.
  Proof.
    iIntros (?) "H". iApply twp_lift_atomic_step; [done|].
    iIntros (σ1 ns κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]". iModIntro.
    iIntros (κs' e2 σ2 efs Hstep). 
    iMod ("H" $! κs' e2 σ2 efs with "[# //]") as "(-> & -> & Hstate & Hval)". simpl.
    iModIntro. iFrame.
    iPureIntro. reflexivity.
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
  Context `{!traceG T Σ}.

  Definition tr_auth (t: T) : iProp Σ := own trace_name (● (Some (Excl (t: leibnizO T)))).
  Definition tr_frag (t: T) : iProp Σ := own trace_name (◯ (Some (Excl (t: leibnizO T)))).

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


(* ------------------------- registers points-to --------------------------------- *)

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
                                | inl w => Vector.cons w (replace_in_inputs words inputs')
                                | inr _ => Vector.cons (word 0) (replace_in_inputs words inputs')
                                end
    | Vector.cons input inputs', w' :: words' => match input with
                                | inl w => Vector.cons w (replace_in_inputs words inputs')
                                | inr _ => Vector.cons w' (replace_in_inputs words' inputs')
                                end
    end.

  Definition regs_of_argument (arg: Word + Register) : gset Register :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
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
  unfold "!!!". unfold lookup_total_register. unfold map_lookup_total. unfold default. simpl. rewrite Hw.
  exists w. split; auto. rewrite (lookup_weaken _ _ _ _ Hw Hincl). reflexivity.
Qed.

Lemma gen_heap_update_inSepM :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapGS L V Σ}
      (σ σ' : gmap L V) (l : L) (v : V),
      is_Some (σ' !! l) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), pointsto k (DfracOwn 1) y.
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
      ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn q) y) -∗
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
      ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn q) y) -∗
      ⌜σ' ⊆ σ⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ !! l) eqn:HH; naive_solver.
  Qed.

Lemma inputs_are_enough {B : Type} {n : nat} {regs regs'} {f_result : vec Word n -> B} {inputs : vec (Word + Register) n}
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


Definition loopify (e : expr) : expr :=
  match e with
  | Instr cf => Loop cf
  | Loop cf => Loop cf
  end.
