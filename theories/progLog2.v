From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting total_weakestpre.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.
From ASMinCoq Require Import CpdtTactics.
From ASMinCoq Require Import AsmGen progLog dwp lifting.

Class binDG Σ := BinDG {
  bin_invG :: invGS Σ;
  fst_memG :: gen_heapGS Addr Word Σ;
  snd_memG :: gen_heapGS Addr Word Σ;
  fst_regG :: gen_heapGS Register Word Σ;
  snd_regG :: gen_heapGS Register Word Σ;
  fst_llG :: traceG (list leak) Σ;
  fst_pcG :: traceG Word Σ;
  fst_progG :: traceG program Σ;
  snd_llG :: traceG (list leak) Σ;
  snd_pcG :: traceG Word Σ;
  snd_progG :: traceG program Σ;
}.

Definition binG1 `{binDG Σ} : asmGS Σ :=
  {|
    asmGS_invGS := bin_invG;
    asm_memGS := fst_memG;
    asm_regGS := fst_regG;
    asm_llGS := fst_llG;
    asm_pcGS := fst_pcG;
    asm_progGS := fst_progG
  |}.

Definition binG2 `{binDG Σ} : asmGS Σ :=
  {|
    asmGS_invGS := bin_invG;
    asm_memGS := snd_memG;
    asm_regGS := snd_regG;
    asm_llGS := snd_llG;
    asm_pcGS := snd_pcG;
    asm_progGS := snd_progG
  |}.

Definition prog1_frag `{!binDG Σ} := @tr_frag program Σ fst_progG.
Definition pc1_frag `{!binDG Σ} := @tr_frag Word Σ fst_pcG.
Definition ll1_frag `{!binDG Σ} := @tr_frag (list leak) Σ fst_llG.

Definition prog2_frag `{!binDG Σ} := @tr_frag program Σ snd_progG.
Definition pc2_frag `{!binDG Σ} := @tr_frag Word Σ snd_pcG.
Definition ll2_frag `{!binDG Σ} := @tr_frag (list leak) Σ snd_llG.

Definition prog1_auth `{!binDG Σ} := @tr_auth program Σ fst_progG.
Definition pc1_auth `{!binDG Σ} := @tr_auth Word Σ fst_pcG.
Definition ll1_auth `{!binDG Σ} := @tr_auth (list leak) Σ fst_llG.

Definition prog2_auth `{!binDG Σ} := @tr_auth program Σ snd_progG.
Definition pc2_auth `{!binDG Σ} := @tr_auth Word Σ snd_pcG.
Definition ll2_auth `{!binDG Σ} := @tr_auth (list leak) Σ snd_llG.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Print asm_irisGS.
Global Instance irisG1 `{!binDG Σ} : irisGS asm_lang Σ := @asm_irisGS Σ binG1.

Global Instance irisG2 `{!binDG Σ} : irisGS asm_lang Σ := @asm_irisGS Σ binG2.


Definition TWP1 `{!binDG Σ} (e : AsmGen.expr) (E : coPset) (R : AsmGen.val → iProp Σ) :=
  @twp (iProp Σ) AsmGen.expr AsmGen.val stuckness
    (@twp' _ asm_lang Σ irisG1)
    NotStuck E e R.

Definition TWP2 `{!binDG Σ} (e : AsmGen.expr) (E : coPset) (R : AsmGen.val → iProp Σ) :=
  @twp (iProp Σ) AsmGen.expr AsmGen.val stuckness
    (@twp' _ asm_lang Σ irisG2)
    NotStuck E e R.

(* Points to predicates for registers *)
Definition pointsto_mem1 `{!binDG Σ} (a : Addr) (q : Qp) (w : Word) :=
    @pointsto Addr _ _ _ Σ fst_memG a (DfracOwn q) w.
Definition pointsto_mem2 `{!binDG Σ} (a : Addr) (q : Qp) (w : Word) :=
  @pointsto Addr _ _ _ Σ snd_memG a (DfracOwn q) w.

Definition pointsto_reg1 `{!binDG Σ} (r : Register) (q : Qp) (w : Word) :=
  @pointsto Register _ _ _ Σ fst_regG r (DfracOwn q) w.
Definition pointsto_reg2 `{!binDG Σ} (r : Register) (q : Qp) (w : Word) :=
  @pointsto Register _ _ _ Σ snd_regG r (DfracOwn q) w.

(* First register *)
Notation "r ↦1ᵣ{ q } w" := (pointsto_reg1 r q w)
                              (at level 20, q at level 50, format "r  ↦1ᵣ{ q }  w") : bi_scope.
Notation "r ↦1ᵣ w" :=
    (pointsto_reg1 r 1 w) (at level 20) : bi_scope.
Notation "r ↦1ᵣ{ q } -" := (∃ w, r ↦1ᵣ{q} w)%I
                              (at level 20, q at level 50, format "r  ↦1ᵣ{ q }  -") : bi_scope.
Notation "l ↦1ᵣ -" := (l ↦1ᵣ{1} -)%I (at level 20) : bi_scope.

(* Second register *)
Notation "r ↦2ᵣ{ q } w" := (pointsto_reg2 r q w)
                             (at level 20, q at level 50, format "r  ↦2ᵣ{ q }  w") : bi_scope.
Notation "r ↦2ᵣ w" :=
  (pointsto_reg2 r 1 w) (at level 20) : bi_scope.
Notation "r ↦2ᵣ{ q } -" := (∃ w, r ↦2ᵣ{q} w)%I
                             (at level 20, q at level 50, format "r  ↦2ᵣ{ q }  -") : bi_scope.
Notation "l ↦2ᵣ -" := (l ↦2ᵣ{1} -)%I (at level 20) : bi_scope.

(* First memory *)
Notation "r ↦1ₐ{ q } w" := (pointsto_mem1 r q w)
                             (at level 20, q at level 50, format "r  ↦1ₐ{ q }  w") : bi_scope.
Notation "r ↦1ₐ w" :=
  (pointsto_mem1 r 1 w) (at level 20) : bi_scope.
Notation "r ↦1ₐ{ q } -" := (∃ w, r ↦1ₐ{q} w)%I
                             (at level 20, q at level 50, format "r  ↦1ₐ{ q }  -") : bi_scope.
Notation "l ↦1ₐ -" := (l ↦1ₐ{1} -)%I (at level 20) : bi_scope.

(* Second memory *)
Notation "r ↦2ₐ{ q } w" := (pointsto_mem2 r q w)
                             (at level 20, q at level 50, format "r  ↦2ₐ{ q }  w") : bi_scope.
Notation "r ↦2ₐ w" :=
  (pointsto_mem2 r 1 w) (at level 20) : bi_scope.
Notation "r ↦2ₐ{ q } -" := (∃ w, r ↦2ₐ{q} w)%I
                             (at level 20, q at level 50, format "r  ↦2ₐ{ q }  -") : bi_scope.
Notation "l ↦2ₐ -" := (l ↦2ₐ{1} -)%I (at level 20) : bi_scope.


#[global] Instance binDG_irisDG `{!binDG Σ} : irisDG asm_lang Σ := {
    state_rel := (λ σ1 σ2 κs1 κs2,
                   @gen_heap_interp _ _ _ _ _ fst_regG (reg σ1.1.2) ∗
                   @gen_heap_interp _ _ _ _ _ fst_memG (mem σ1.1.2) ∗
                   @tr_auth _ _ fst_llG σ1.2 ∗
                   @tr_auth _ _ fst_pcG (PC σ1.1.2) ∗
                   @tr_auth _ _ fst_progG σ1.1.1 ∗
                   @gen_heap_interp _ _ _ _ _ snd_regG (reg σ2.1.2) ∗
                   @gen_heap_interp _ _ _ _ _ snd_memG (mem σ2.1.2) ∗
                   @tr_auth _ _ snd_llG σ2.2 ∗
                   @tr_auth _ _ snd_pcG (PC σ2.1.2) ∗
                   @tr_auth _ _ snd_progG σ2.1.1
  )%I
  }.

Section lifting.
  Context `{!binDG Σ}.

  Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _; simpl : core.

Lemma dwp_atomic_lift_wp Ψ1 Ψ2 E2 e1 e2 Φ
  `{!Atomic StronglyAtomic e1}
  `{!Atomic StronglyAtomic e2}
  {NF1 : NoFork e1}
  {NF2 : NoFork e2}
  {He1 : NotVal e1}
  {He2 : NotVal e2}:
  TWP1 e1 E2 Ψ1 -∗
  TWP2 e2 ∅ Ψ2 -∗
  (∀ v1 v2, Ψ1 v1 -∗ Ψ2 v2 -∗ ▷ Φ v1 v2) -∗
  dwp E2 e1 e2 Φ.
Proof.
  iIntros "HTWP1 HTWP2 H".
  rewrite dwp_unfold /dwp_pre /= He1 He2.
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hσ".
  iDestruct "Hσ" as "(Hregσ1 & Hmemσ1 & Hllσ1 & Hpcσ1 & Hprogσ1 &
                      Hregσ2 & Hmemσ2 & Hllσ2 & Hpcσ2 & Hprogσ2)".
  rewrite /TWP1 /TWP2 !twp_unfold /twp_pre /= !He1 !He2.
  iSpecialize ("HTWP1" $! σ1 0 (κ1++κs1) 0 with "[$Hregσ1 $Hmemσ1 $Hllσ1 $Hpcσ1 $Hprogσ1]").
  iSpecialize ("HTWP2" $! σ2 0 (κ2++κs2) 0%nat with "[$Hregσ2 $Hmemσ2 $Hllσ2 $Hpcσ2 $Hprogσ2]").
  iMod "HTWP1" as (Hred1) "HTWP1".
  iMod "HTWP2" as (Hred2) "HTWP2".
  destruct Hred1 as (? & ? & ? & Hred1).
  destruct Hred2 as (? & ? & ? & Hred2).
  iModIntro.
  iSplit. { iPureIntro. eexists. eauto. }
  iSplit. { iPureIntro. eexists. eauto. }
  iIntros (e1' σ1' efs e2' σ2' efs2 Hstep1 Hstep2).
  iSpecialize ("HTWP1" $! [] e1' σ1' efs with "[//]").
  iSpecialize ("HTWP2" with "[//]").
  iMod "HTWP2" as "(_ & (Hreg2 & Hmem2 & Hll2 & Hpc2 & Hprog2) & HTWP2 & _)".
  iMod "HTWP1" as "(_ & (Hreg1 & Hmem1 & Hll1 & Hpc1 & Hprog1) & HTWP1 & _)".
  destruct (to_val e1') as [v1|] eqn:Hv1; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep1). naive_solver. }
  destruct (to_val e2') as [v2|] eqn:Hv2; last first.
  { exfalso. destruct (atomic _ _ _ _ _ Hstep2). naive_solver. }
  rewrite -(of_to_val _ _ Hv1) -(of_to_val _ _ Hv2).
  rewrite !twp_value_fupd. iMod "HTWP1".
  rewrite (fupd_mask_mono ∅ E2); last by set_solver.
  iMod "HTWP2".
  iFrame "Hreg2 Hmem2 Hll2 Hpc2 Hprog2
    Hreg1 Hmem1 Hll1 Hpc1 Hprog1".
  iApply step_fupd_intro; first set_solver.
  iSpecialize ("H" with "HTWP1 HTWP2").
  iNext. rewrite -dwp_value. iFrame "H".
  rewrite (nofork _ _ _ _ _ Hstep1).
  rewrite (nofork _ _ _ _ _ Hstep2).
  simpl. eauto with iFrame.
Qed.


Lemma dwp_halt (pc1 pc2 : Word) (prog1 prog2 : program) (ll1 ll2 : list leak) E Φ :
    prog1 pc1 = Halt ->
    prog2 pc2 = Halt ->
    prog1_frag prog1 -∗ pc1_frag pc1 -∗ ll1_frag ll1 -∗
    prog2_frag prog2 -∗ pc2_frag pc2 -∗ ll2_frag ll2 -∗
    ▷ (prog1_frag prog1 ∗ pc1_frag pc1 ∗ ll1_frag (NoLeak :: ll1) -∗
       prog2_frag prog2 ∗ pc2_frag pc2 ∗ ll2_frag (NoLeak :: ll2) -∗
      Φ HaltedV HaltedV) -∗
    dwp E (Instr Executable) (Instr Executable) Φ.
  Proof.
    iIntros (prpc1Halt prpc2Halt) "Hprog1 Hpc1 Hll1 Hprog2 Hpc2 Hll2 HΦ".
    iApply (dwp_atomic_lift_wp
              (λ v, ⌜v = HaltedV⌝ ∗ prog1_frag prog1 ∗ pc1_frag pc1 ∗ ll1_frag (NoLeak :: ll1))%I
              (λ v, ⌜v = HaltedV⌝ ∗ prog2_frag prog2 ∗ pc2_frag pc2 ∗ ll2_frag (NoLeak :: ll2))%I
             with "[Hprog1 Hpc1 Hll1] [Hprog2 Hpc2 Hll2] [HΦ]").
    { iApply (twp_halt with "[Hprog1] [Hpc1] [Hll1] []"); try iFrame; eauto. }
    { iApply (twp_halt with "[Hprog2] [Hpc2] [Hll2] []"); eauto. }
    iIntros (? ?) "(% & Hprog1 & Hpc1 & Hll1) (% & Hprog2 & Hpc2 & Hll2)". subst.
    iNext.
    iApply ("HΦ" with "[$Hprog1 $Hpc1 $Hll1] [$Hprog2 $Hpc2 $Hll2]").
  Qed.

  Definition dwp_bind_loop_executable
    (E : coPset)
    (Φ : language.val asm_lang → language.val asm_lang → iProp Σ) :
    dwp E (Instr Executable) (Instr Executable)
      (fun v1 v2 => (dwp E (loopify (language.of_val v1)) (loopify (language.of_val v2)) Φ))
   ⊢ dwp E (loopify (Instr Executable)) (loopify (Instr Executable)) Φ :=
   dwp_bind loopify loopify E (Instr Executable) (Instr Executable) Φ.


Lemma dwp_loop_next Φ E :
  dwp E (Loop Executable) (Loop Executable) Φ ⊢
  dwp E (Loop NextI) (Loop NextI) Φ.
  Proof.
    iIntros "HExec".
    iApply dwp_lift_pure_step_no_fork; auto;
    try apply loop_next_always_reducible.
    { intros κ σ1 e2 σ1' efs steps. inversion steps. auto. }
    { intros κ σ2 e2 σ2' efs steps. inversion steps. auto. }
    
    iModIntro. iNext. iModIntro.
    
    iIntros (κ1 κ2 e1' σ1 efs1 e2' σ2 efs2) "%steps1 %steps2".
    inversion steps1; inversion steps2; auto.
Qed.

Lemma dwp_loop_halted Φ E :
  Φ LoopHaltedV LoopHaltedV -∗
  dwp E (Loop Halted) (Loop Halted) Φ.
  Proof.
    iIntros "HΦ".
    iApply (dwp_value _ _ _ _ LoopHaltedV LoopHaltedV); try reflexivity; try auto.
Qed.

  Lemma test_prog_not_constant_time_different_leakage Φ :
  prog1_frag (test_prog_not_constant_time 2) -∗
  prog2_frag (test_prog_not_constant_time 0) -∗
  pc1_frag (word 0) -∗ pc2_frag (word 0) -∗
  ll1_frag [] -∗ ll2_frag [] -∗
  register 0 ↦1ᵣ word 0 -∗
  register 0 ↦2ᵣ word 0 -∗
  ▷(∀ ll ll', prog1_frag (test_prog_not_constant_time 2) -∗
    prog2_frag (test_prog_not_constant_time 0) -∗
    pc1_frag (word 3) -∗ pc2_frag (word 2) -∗
    ll1_frag ll -∗ ll2_frag ll' -∗
    ⌜ll ≠ ll'⌝ -∗
      Φ LoopHaltedV LoopHaltedV) -∗
    dwp ∅ (Loop Executable) (Loop Executable) Φ.
  Proof.
    iIntros "Hprog1 Hprog2 Hpc1 Hpc2 Hll1 Hll2 Hr1 Hr2 HΦ".
    iApply dwp_bind_loop_executable.
    iApply (dwp_atomic_lift_wp
              (λ v, ⌜v = NextIV⌝ ∗ prog1_frag (test_prog_not_constant_time 2) ∗ pc1_frag (word 1) ∗ ll1_frag [NoLeak] ∗ [∗ map] k↦y ∈ <[register 0:=add_vec_2 (inputs_from_inputnatregs (<[register 0:=word 0]> ∅) [#inl (word 2); inl (word 2)])]> (<[register 0:=word 0]> ∅), k ↦1ᵣ y )%I
              (λ v, ⌜v = NextIV⌝ ∗ prog2_frag (test_prog_not_constant_time 0) ∗ pc2_frag (word 1) ∗ ll2_frag [NoLeak] ∗ [∗ map] k↦y ∈ <[register 0:=add_vec_2 [#word 0; word 0]]> (<[register 0:=word 0]> ∅), k ↦2ᵣ y)%I
             with "[Hprog1 Hpc1 Hll1 Hr1] [Hprog2 Hpc2 Hll2 Hr2] [HΦ]").
    { iApply (twp_computation (<[register 0 := word 0]> empty)
               with "[Hprog1] [Hpc1] [Hll1] [Hr1]"); try iFrame; try reflexivity.
      { econstructor; try reflexivity. }
      { iApply big_sepM_insert. { constructor. }
        iFrame. by iApply big_sepM_empty. }
      iIntros "(Hprog & Hpc & Hll & H)". simpl. iFrame. iPureIntro. reflexivity. }
    { iApply (twp_computation (<[register 0 := word 0]> empty)
               with "[Hprog2] [Hpc2] [Hll2] [Hr2]"); try iFrame; try reflexivity.
      { econstructor; try reflexivity. }
      { iApply big_sepM_insert. { constructor. }
        iFrame. by iApply big_sepM_empty. }
      iIntros "(Hprog & Hpc & Hll & H)". simpl. iFrame. iPureIntro. reflexivity. }

     iIntros (? ?) "(-> & Hprog1 & Hpc1 & Hll1 & Hr1) (-> & Hprog2 & Hpc2 & Hll2 & Hr2)".
     simpl. iNext.    
     iApply dwp_loop_next.

     iApply dwp_bind_loop_executable.
     iApply (dwp_atomic_lift_wp
               (λ v, ⌜v = NextIV⌝ ∗ prog1_frag (test_prog_not_constant_time 2) ∗ pc1_frag (word 3) ∗ ll1_frag [ControlFlowLeak (notzero_vec_1 [#<[register 0:=word 4]> ∅ !!! register 0]); NoLeak] ∗ [∗ map] k↦y ∈ <[register 0:=word 4]> ∅, k ↦1ᵣ y)%I
               (λ v, ⌜v = NextIV⌝ ∗ prog2_frag (test_prog_not_constant_time 0) ∗ pc2_frag (word 2) ∗ ll2_frag [ControlFlowLeak (notzero_vec_1 [#<[register 0:=word 0]> ∅ !!! register 0]); NoLeak] ∗ [∗ map] k↦y ∈ <[register 0:=word 0]> ∅, k ↦2ᵣ y)%I
              with "[Hprog1 Hpc1 Hll1 Hr1] [Hprog2 Hpc2 Hll2 Hr2] [HΦ]").
     { iApply (twp_control_flow (<[register 0:= word 4]> ∅) with "[Hprog1] [Hpc1] [Hll1] [Hr1]"); try iFrame; try reflexivity.
       { econstructor; reflexivity. }
       iIntros "(Hprog & Hpc & Hll & Hmap)".
       simpl. iFrame. iPureIntro. reflexivity.
     }
     { iApply (twp_control_flow (<[register 0:= word 0]> ∅) with "[Hprog2] [Hpc2] [Hll2] [Hr2]"); try iFrame; try reflexivity.
       { econstructor; reflexivity. }
       iIntros "(Hprog & Hpc & Hll & Hmap)".
       simpl. iFrame. iPureIntro. reflexivity.
     }


     iIntros (? ?) "(-> & Hprog1 & Hpc1 & Hll1 & Hr1) (-> & Hprog2 & Hpc2 & Hll2 & Hr2)".
     simpl. iNext.    
     iApply dwp_loop_next.
     iApply dwp_bind_loop_executable.
     iApply (dwp_halt with "Hprog1 Hpc1 Hll1 Hprog2 Hpc2 Hll2"); try reflexivity.
     iNext. iIntros "(Hprog1 & Hpc1 & Hll1) (Hprog2 & Hpc2 & Hll2)".
     iApply dwp_loop_halted. iApply ("HΦ" with "Hprog1 Hprog2 Hpc1 Hpc2 Hll1 Hll2").
     iPureIntro.
     intro H.

     apply (f_equal (fun l => nth 1 l NoLeak)) in H. simpl in H.
     do 2 (rewrite lookup_total_insert in H).
     unfold notzero_vec_1 in H. unfold unaryOn1Vec in H. simpl in H.
     congruence.
Qed.
