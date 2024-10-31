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

Class asmGS Σ := AsmGS {
                              asmGS_invGS : invGS Σ;
                              asm_memGS :: gen_heapGS Addr Word Σ;
                              asm_regGS :: gen_heapGS Register Word Σ;
                              asm_llGS :: traceG (list leak) Σ;
                              asm_pcGS :: traceG Word Σ;
                              asm_progGS :: traceG program Σ;
                            }.


Class allDG Σ := AllDG {
                      DG_invG :: invGS Σ;
                      DG_memG :: gen_heapGS Addr Word Σ;
                      DG_regG :: gen_heapGS Register Word Σ;
                      DG_llG :: traceG (list leak) Σ;
                      DG_pcG :: traceG Word Σ;
                      DG_progG :: traceG program Σ;
                    }.

Definition prog_frag `{!asmGS Σ} := @tr_frag program Σ asm_progGS.
Definition pc_frag `{!asmGS Σ} := @tr_frag Word Σ asm_pcGS.
Definition ll_frag `{!asmGS Σ} := @tr_frag (list leak) Σ asm_llGS.

Definition prog_auth `{!asmGS Σ} := @tr_auth program Σ asm_progGS.
Definition pc_auth `{!asmGS Σ} := @tr_auth Word Σ asm_pcGS.
Definition ll_auth `{!asmGS Σ} := @tr_auth (list leak) Σ asm_llGS.


Section prog_log_helper.
  Context `{!asmGS Σ}.
  (* Points to predicates for registers *)
  Print pointsto.
  Notation "r ↦ᵣ{ q } w" := (pointsto (hG := asm_regGS) (L:=Register) (V:=Word) r q w)
                              (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
  Notation "r ↦ᵣ w" := (pointsto (hG := asm_regGS) (L:=Register) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.

  (* Points to predicates for memory *)
  Notation "a ↦ₐ{ q } w" := (pointsto (hG := asm_memGS) (L:=Addr) (V:=Word) a q w)
                              (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
  Notation "a ↦ₐ w" := (pointsto (hG := asm_memGS) (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.

(* ------------------------- registers points-to --------------------------------- *)

  Lemma register_dupl_false r w1 w2 :
    r ↦ᵣ w1 -∗ r ↦ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (pointsto_valid_2 with "Hr1 Hr2") as %H.
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

(*
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
*)

  (* ------------------------- memory points-to --------------------------------- *)

  Lemma addr_dupl_false a w1 w2 :
    a ↦ₐ w1 -∗ a ↦ₐ w2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (pointsto_valid_2 with "Ha1 Ha2") as %H.
    destruct H as [H1 H2]. eapply dfrac_full_exclusive in H1.
    auto.
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

Lemma regs_of_computation {n : nat} (inputs : vec (Word + Register) n)
    (rres : Register) (f_result : vec Word n -> Word) i :
    i = Computation inputs rres f_result ->
    regs_of i = {[ rres ]} ∪ regs_from_inputs inputs.
Proof.
  intros. subst.
  reflexivity.
Qed.



Lemma regs_of_control_flow {n : nat} (inputs : vec (Word + Register) n)
    (dst : Word + Register) (f_condition : vec Word n -> bool) i :
    i = ControlFlow inputs dst f_condition ->
    regs_of i = regs_of_argument dst ∪ regs_from_inputs inputs.
Proof.
  intros. subst.
  reflexivity.
Qed.

Definition test_prog_not_constant_time (high_input : nat) :=
  list_prog_to_prog [Add (register 0) (inl (word high_input)) (inl (word high_input)); Jnz (inr (register 0)) (inl (word 3))].

Definition loopify (e : expr) : expr :=
  match e with
  | Instr cf => Loop cf
  | Loop cf => Loop cf
  end.

End prog_log_helper.
