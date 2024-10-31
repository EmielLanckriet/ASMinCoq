From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting total_lifting total_weakestpre.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.
From ASMinCoq Require Import CpdtTactics progLogHelper AsmGen.

Section asm_lang_rules.
  Context `{!asmGS Σ}.
  Import asm_lang.

  

Global Program Instance asm_irisGS `{!asmGS Σ} : irisGS asm_lang Σ := {
    iris_invGS := asmGS_invGS;
    state_interp σ _ κs _ :=
      ((@gen_heap_interp _ _ _ _ _ asm_regGS (reg σ.1.2)) ∗
         (@gen_heap_interp _ _ _ _ _ asm_memGS (mem σ.1.2)) ∗
         ll_auth σ.2 ∗
         pc_auth (PC σ.1.2) ∗
         prog_auth σ.1.1)%I;
    fork_post _ := True%I;
    num_laters_per_step n := n;
  }.
Next Obligation.
  iIntros (Σ' ??? κs') "/= ($ & $ & H)".
  iFrame. by iModIntro.
Qed.

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

  Lemma addr_dupl_false a w1 w2 :
    a ↦ₐ w1 -∗ a ↦ₐ w2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (pointsto_valid_2 with "Ha1 Ha2") as %H.
    destruct H as [H1 H2]. eapply dfrac_full_exclusive in H1.
    auto.
  Qed.

  Lemma wp_halt pc prog ll E Φ :
    prog pc = Halt ->
    prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
    ▷ (prog_frag prog ∗ pc_frag pc ∗ ll_frag (HaltLeak :: ll) -∗ Φ HaltedV) -∗
    WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt) "Hprog Hpc Hll HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hauthreg & Hauthmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible.
    - iIntros (e2 σ2 efs) "%steps test".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *. iFrame.
      iPoseProof (trace_update _ (HaltLeak :: ll) with "[$Hauthtrace $Hll]") as "H".
      iMod "H". iModIntro. iNext. iModIntro.
      iDestruct "H" as "[Hauthll Hfragll]". iFrame.
      iSplitR.
      { iPureIntro; reflexivity. }
      iApply "HΦ". iFrame.
  Qed.

  Lemma twp_halt pc prog ll E Φ :
    prog pc = Halt ->
    prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
    (prog_frag prog ∗ pc_frag pc ∗ ll_frag (HaltLeak :: ll) -∗ Φ HaltedV) -∗
    twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt) "Hprog Hpc Hll HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hauthreg & Hauthmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible_no_obs.
    - iIntros (κ e2 σ2 efs) "%steps".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *. iFrame.
      iPoseProof (trace_update _ (HaltLeak :: ll) with "[$Hauthtrace $Hll]") as "H".
      iMod "H". iModIntro.
      iDestruct "H" as "[Hauthll Hfragll]". iFrame.
      iSplitR.
      { iPureIntro; reflexivity. }
      iSplitR.
      { iPureIntro; reflexivity. }
      iApply "HΦ". iFrame.
  Qed.

Inductive Computation_spec {n : nat} (inputs : vec (Word + Register) n) (rres : Register) f_result (regs : Reg) (regs' : Reg) : Prop :=
  | Computation_spec_success vn  :
      inputs_from_inputnatregs regs inputs = vn ->
      (<[ rres := f_result vn ]> regs) = regs' ->
      Computation_spec inputs rres f_result regs regs'.

Lemma wp_computation {n : nat} regs regs' pc prog ll
    (inputs : vec (Word + Register) n) rres f_result Φ E :
  prog pc = Computation inputs rres f_result ->
  regs_of (Computation inputs rres f_result) ⊆ dom regs →
  Computation_spec (n := n) inputs rres f_result regs regs' ->
  prog_frag prog -∗ pc_frag pc -∗
  ll_frag ll -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ ((prog_frag prog ∗ pc_frag (incr_word pc) ∗ ll_frag (ComputationLeak f_result :: ll) ∗
    [∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ Φ NextIV) -∗
    WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt regs_subset Hcomp) "Hprog Hpc Hll HlistOfRegs HΦ".
    inversion Hcomp; subst; clear Hcomp.
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll']. 
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iPoseProof (trace_update _ (ComputationLeak f_result :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC (s.2))) with "[$Hauthpc $Hpc]") as "H2".

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
      iSplitR; try (iPureIntro; reflexivity).
      iApply "HΦ"; iFrame.
      rewrite (inputs_are_enough _ Hregs); auto.
      apply union_subseteq in regs_subset as [_ ->]; reflexivity.
Qed.


Lemma twp_computation {n : nat} regs regs' pc prog ll
    (inputs : vec (Word + Register) n) rres f_result Φ E :
  prog pc = Computation inputs rres f_result ->
  regs_of (Computation inputs rres f_result) ⊆ dom regs →
  Computation_spec (n := n) inputs rres f_result regs regs' ->
  prog_frag prog -∗ pc_frag pc -∗
  ll_frag ll -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
                                                ((prog_frag prog -∗ pc_frag (incr_word pc) -∗ ll_frag (ComputationLeak f_result :: ll) -∗
    [∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ Φ NextIV) -∗
    twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt regs_subset Hcomp) "Hprog Hpc Hll HlistOfRegs HΦ".
    inversion Hcomp; subst; clear Hcomp.
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll']. 
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iPoseProof (trace_update _ (ComputationLeak f_result :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC (s.2))) with "[$Hauthpc $Hpc]") as "H2".

    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    specialize (indom_regs_incl _ _ _ regs_subset Hregs) as Hri.
    destruct (Hri rres) as [wdst [H'dst Hdst]]. by set_solver+.        
    iMod "H1". iMod "H2". iModIntro.

    iDestruct "H1" as "[Hauthll Hfragll]". iDestruct "H2" as "[Hauthpc Hfragpc]".
    iSplitR.
    - iPureIntro. apply normal_always_reducible_no_obs.
    - iIntros (κ e2 σ2 efs) "%steps".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.     
      iFrame.
      unfold incr_PC. rewrite -(update_pc_no_change_reg).
      rewrite reg_is_updated_value.
      iMod ((gen_heap_update_inSepM _ _ rres) with "Hreg HlistOfRegs") as "[Hr Hmap]".
      { eauto.  }
      iModIntro.
      iFrame.
      do 2 (iSplitR; try (iPureIntro; reflexivity)).
      iApply "HΦ"; iFrame.
      rewrite (inputs_are_enough _ Hregs); auto.
      apply union_subseteq in regs_subset as [_ ->]; reflexivity.
Qed.

Inductive Control_flow_spec {n : nat} (inputs : vec (Word + Register) n) (dst : Word + Register) f_condition (regs : Reg) (pc pc' : Word) : Prop :=
  | Control_flow_spec_true_success vn :
      inputs_from_inputnatregs regs inputs = vn ->
      f_condition vn = true ->
      wordreg_to_word regs dst = pc' ->
      Control_flow_spec inputs dst f_condition regs pc pc'
  | Control_flow_spec_false_success vn :
      inputs_from_inputnatregs regs inputs = vn ->
      f_condition vn = false ->
      incr_word pc = pc' ->
      Control_flow_spec inputs dst f_condition regs pc pc'.

Lemma wp_control_flow {n : nat} regs pc pc' prog ll (inputs : vec (Word + Register) n) dst f_condition E Φ :
  prog pc = ControlFlow inputs dst f_condition ->
  Control_flow_spec inputs dst f_condition regs pc pc' ->
  regs_of (ControlFlow inputs dst f_condition) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
  ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
  ▷(prog_frag prog ∗ pc_frag pc' ∗
      ll_frag (ControlFlowLeak pc' :: ll) ∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ NextIV) -∗
    WP (Instr Executable) @ E {{ v, Φ v }}.
Proof.
    iIntros (prpcHalt HcontrolFlow regs_subset) "Hprog Hpc Hll HlistOfRegs HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.   
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible.
    - iIntros (e2 σ2 efs) "%steps _".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.
      inversion HcontrolFlow; subst; clear HcontrolFlow.
      all: apply union_subseteq in regs_subset as [dst_subset inputs_subset].
      all: rewrite (inputs_are_enough _ Hregs) in H1; auto.
      all: destruct (f_condition (inputs_from_inputnatregs (reg φ) inputs)) as [|] eqn:Hcondition; try congruence.
      1: iPoseProof (trace_update _ (ControlFlowLeak (wordreg_to_word (reg φ) dst) :: ll) with "[$Hauthtrace $Hll]") as "H1".
      2: iPoseProof (trace_update _ (ControlFlowLeak (PC (incr_PC φ)) :: ll) with "[$Hauthtrace $Hll]") as "H1".
      1: iPoseProof (trace_update _ (wordreg_to_word (reg φ) dst) with "[$Hauthpc $Hpc]") as "H2".
      2: iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
      all: iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]"; iFrame.
      all: iModIntro; iNext; iModIntro.
      all: iSplitR; try (iPureIntro; reflexivity).
      all: iApply "HΦ".
      all: iFrame.
      destruct dst; iFrame.
      specialize (indom_regs_incl_default _ _ _ dst_subset Hregs r) as Hri.
      destruct Hri as [w [Hw Hw']]. {set_solver. }
      simpl.
      rewrite Hw Hw'. iFrame.
Qed.


Lemma twp_control_flow {n : nat} regs pc pc' prog ll (inputs : vec (Word + Register) n) dst f_condition E Φ :
  prog pc = ControlFlow inputs dst f_condition ->
  Control_flow_spec inputs dst f_condition regs pc pc' ->
  regs_of (ControlFlow inputs dst f_condition) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
  ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
  (prog_frag prog ∗ pc_frag pc' ∗
      ll_frag (ControlFlowLeak pc' :: ll) ∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ NextIV) -∗
    twp NotStuck E (Instr Executable) Φ.
Proof.
    iIntros (prpcHalt HcontrolFlow regs_subset) "Hprog Hpc Hll HlistOfRegs HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.   
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible_no_obs.
    - iIntros (κ e2 σ2 efs) "%steps".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.
      inversion HcontrolFlow; subst; clear HcontrolFlow.
      all: apply union_subseteq in regs_subset as [dst_subset inputs_subset].
      all: rewrite (inputs_are_enough _ Hregs) in H1; auto.
      all: destruct (f_condition (inputs_from_inputnatregs (reg φ) inputs)) as [|] eqn:Hcondition; try congruence.
      1: iPoseProof (trace_update _ (ControlFlowLeak (wordreg_to_word (reg φ) dst) :: ll) with "[$Hauthtrace $Hll]") as "H1".
      2: iPoseProof (trace_update _ (ControlFlowLeak (PC (incr_PC φ)) :: ll) with "[$Hauthtrace $Hll]") as "H1".
      1: iPoseProof (trace_update _ (wordreg_to_word (reg φ) dst) with "[$Hauthpc $Hpc]") as "H2".
      2: iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
      all: iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]"; iFrame.
      all: iModIntro.
      all: do 2 (iSplitR; try (iPureIntro; reflexivity)).
      all: iApply "HΦ".
      all: iFrame.
      destruct dst; iFrame.
      specialize (indom_regs_incl_default _ _ _ dst_subset Hregs r) as Hri.
      destruct Hri as [w [Hw Hw']]. {set_solver. }
      simpl.
      rewrite Hw Hw'. iFrame.
Qed.

Lemma wp_load {n : nat} pc prog ll regs rres rsrc v E Φ :
  prog pc = Load rres rsrc ->
  regs_of (Load rres rsrc) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
      word_to_addr (regs !!! rsrc) ↦ₐ v -∗
  ▷(prog_frag prog ∗ pc_frag (incr_word pc) ∗
      ll_frag (LoadLeak (word_to_addr (regs !!! rsrc)) :: ll) ∗
      ([∗ map] k↦y ∈ <[ rres := v ]>regs, k ↦ᵣ y) -∗ Φ NextIV) -∗
  WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hll HlistOfRegs Haddrv HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible. }
    iIntros (e2 σ2 efs) "%steps _".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update _ (LoadLeak (word_to_addr (reg φ !!! rsrc)) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite reg_is_updated_value.
    iMod ((gen_heap_update_inSepM _ _ rres) with "Hreg HlistOfRegs") as "[Hr Hmap]".
    { eapply @elem_of_dom with (D := gset Register). typeclasses eauto.
    eapply elem_of_subseteq; eauto. set_solver. }
    iPoseProof (gen_heap_valid (gen_heapGS0 := asm_memGS) with "Hmem Haddrv") as "%Hmem'".
    iModIntro. iNext. iModIntro. iFrame.
    iSplitR.
    { iPureIntro. reflexivity. }
    
    iApply "HΦ"; iFrame.
    specialize (indom_regs_incl_default _ _ _ regs_subset Hregs rsrc) as Hri.
    destruct Hri as [w [Hw Hw']]. { set_solver. }
    rewrite Hw. rewrite Hw'. iFrame.
    rewrite Hw in Hmem'. unfold word_to_addr in Hmem'.
    assert (mem φ !!! (word_to_addr w) = v) as Hmem''.
    { unfold "!!!". unfold lookup_total_memory. unfold map_lookup_total. unfold default. rewrite Hmem'. reflexivity. }
    rewrite Hmem''. iFrame.
Qed.


Lemma twp_load {n : nat} pc prog ll regs rres rsrc v E Φ :
  prog pc = Load rres rsrc ->
  regs_of (Load rres rsrc) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
      word_to_addr (regs !!! rsrc) ↦ₐ v -∗
  (prog_frag prog ∗ pc_frag (incr_word pc) ∗
      ll_frag (LoadLeak (word_to_addr (regs !!! rsrc)) :: ll) ∗
      ([∗ map] k↦y ∈ <[ rres := v ]>regs, k ↦ᵣ y) -∗ Φ NextIV) -∗
  twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hll HlistOfRegs Haddrv HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible_no_obs. }
    iIntros (κ e2 σ2 efs) "%steps".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update _ (LoadLeak (word_to_addr (reg φ !!! rsrc)) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite reg_is_updated_value.
    iMod ((gen_heap_update_inSepM _ _ rres) with "Hreg HlistOfRegs") as "[Hr Hmap]".
    { eapply @elem_of_dom with (D := gset Register). typeclasses eauto.
    eapply elem_of_subseteq; eauto. set_solver. }
    iPoseProof (gen_heap_valid (gen_heapGS0 := asm_memGS) with "Hmem Haddrv") as "%Hmem'".
    iModIntro. iFrame.
    do 2 (iSplitR; try (iPureIntro; reflexivity)).
    
    iApply "HΦ"; iFrame.
    specialize (indom_regs_incl_default _ _ _ regs_subset Hregs rsrc) as Hri.
    destruct Hri as [w [Hw Hw']]. { set_solver. }
    rewrite Hw. rewrite Hw'. iFrame.
    rewrite Hw in Hmem'. unfold word_to_addr in Hmem'.
    assert (mem φ !!! (word_to_addr w) = v) as Hmem''.
    { unfold "!!!". unfold lookup_total_memory. unfold map_lookup_total. unfold default. rewrite Hmem'. reflexivity. }
    rewrite Hmem''. iFrame.
Qed.

Lemma wp_store pc prog ll regs rdst src v E Φ :
  prog pc = Store rdst src ->
  regs_of (Store rdst src) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
      word_to_addr (regs !!! rdst) ↦ₐ v -∗
  ▷(prog_frag prog ∗ pc_frag (incr_word pc) ∗
      ll_frag (StoreLeak (word_to_addr (wordreg_to_word regs src)) :: ll) ∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
      word_to_addr (regs !!! rdst) ↦ₐ wordreg_to_word regs src -∗
    Φ NextIV) -∗
     WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hll HlistOfRegs Haddrv HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible. }
    iIntros (e2 σ2 efs) "%steps _".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update _ (StoreLeak ((word_to_addr (wordreg_to_word regs src))) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite -update_mem_no_change_reg.
    iPoseProof (gen_heap_valid with "Hmem Haddrv") as "%Hmem'".
    
    iMod ((gen_heap_update _ (word_to_addr (regs !!! rdst))) with "Hmem Haddrv") as "[Hr Hmap]".
    specialize (indom_regs_incl_default _ _ _ regs_subset Hregs rdst) as Hri.
    destruct Hri as [w [Hw Hw']]. { set_solver. }
    rewrite Hw Hw'.

    iModIntro. iNext. iModIntro. clear. iFrame.
    iSplitR.
    { iPureIntro. reflexivity. }
    
    iSplitL "Hauthll".
    all: destruct src; simpl; iFrame.
    all: try iApply "HΦ"; iFrame.
    all: specialize (indom_regs_incl_default _ _ _ regs_subset Hregs r) as Hri.
    all: destruct Hri as [w1 [Hw1 Hw1']]; try (rewrite Hw1 Hw1'; iFrame); try set_solver.
Qed.


Lemma twp_store pc prog ll regs rdst src v E Φ :
  prog pc = Store rdst src ->
  regs_of (Store rdst src) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
      word_to_addr (regs !!! rdst) ↦ₐ v -∗
  (prog_frag prog ∗ pc_frag (incr_word pc) ∗
      ll_frag (StoreLeak (word_to_addr (wordreg_to_word regs src)) :: ll) ∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
      word_to_addr (regs !!! rdst) ↦ₐ wordreg_to_word regs src -∗
    Φ NextIV) -∗
    twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hll HlistOfRegs Haddrv HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible_no_obs. }
    iIntros (κ e2 σ2 efs) "%steps".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update _ (StoreLeak ((word_to_addr (wordreg_to_word regs src))) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite -update_mem_no_change_reg.
    iPoseProof (gen_heap_valid with "Hmem Haddrv") as "%Hmem'".
    
    iMod ((gen_heap_update _ (word_to_addr (regs !!! rdst))) with "Hmem Haddrv") as "[Hr Hmap]".
    specialize (indom_regs_incl_default _ _ _ regs_subset Hregs rdst) as Hri.
    destruct Hri as [w [Hw Hw']]. { set_solver. }
    rewrite Hw Hw'.

    iModIntro. clear. iFrame.
    do 2 (iSplitR; try (iPureIntro; reflexivity)).
    
    iSplitL "Hauthll".
    all: destruct src; simpl; iFrame.
    all: try iApply "HΦ"; iFrame.
    all: specialize (indom_regs_incl_default _ _ _ regs_subset Hregs r) as Hri.
    all: destruct Hri as [w1 [Hw1 Hw1']]; try (rewrite Hw1 Hw1'; iFrame); try set_solver.
Qed.

#[export] Instance language_ctx_loopify : @LanguageCtx asm_lang loopify.
Proof.
  constructor.
  - intros e e_is_None.
    destruct e; destruct c; simpl in *; try congruence.
  - intros e1. intros. destruct e1; simpl; inversion H;
    try constructor; try assumption.
  - intros e1'. intros. destruct e1'; destruct c; simpl in *; inversion H0; subst.
    + exists (Instr Executable). crush.
    + exists (Instr cf). crush.
    + exists (Loop Executable). crush.
    + exists (Loop cf). crush.
Qed.

Definition wp_bind_loop_executable
    (s : stuckness) (E : coPset)
      (Φ : language.val asm_lang → iProp Σ) :
      WP Instr Executable @ s; E {{ v, WP ((fun v' => loopify (language.of_val v')) v) @ s; E {{ v, Φ v }} }}
      ⊢ WP Loop Executable @ s; E {{ Φ }} :=
  wp_bind loopify s E (Instr Executable) Φ.


#[export] Instance inhabited_asm_state : Inhabited (language.state asm_lang).
Proof.
  constructor.
  exact (list_prog_to_prog [], (word 0, emptyReg, emptyMem), []).
Qed.

Lemma wp_loop_next Φ E :
  WP Loop Executable @ E {{ Φ }} -∗
  WP Loop NextI @ E {{ Φ }}.
  Proof.
    iIntros "HExec".
    iApply wp_lift_pure_step_no_fork; auto.
    { apply loop_next_always_reducible. }
    { intros κ σ1 e2 σ2 efs steps. inversion steps. auto. }
    
    iModIntro. iNext. iModIntro.
    
    iIntros (κ e2 efs σ) "%steps _".
    inversion steps; auto.
Qed.

Lemma wp_loop_halted Φ E :
  Φ LoopHaltedV -∗
  WP Loop Halted @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (wp_value_fupd _ _ _ _ LoopHaltedV).
    { reflexivity. }
    iModIntro.
    done.
Qed.



Lemma wp_test :
  {{{ prog_frag (test_prog_not_constant_time 2) ∗
      pc_frag (word 0) ∗ ll_frag [] ∗
      register 0 ↦ᵣ word 0 }}}
      (Loop Executable)
  {{{ RET LoopHaltedV; prog_frag (test_prog_not_constant_time 2)
      ∗ pc_frag (word 3) ∗
      ll_frag ([HaltLeak; ControlFlowLeak (word 3); AddLeak]) ∗
      register 0 ↦ᵣ word 4
     }}}.
Proof.
  iIntros (Φ) "(Hprog & Hpc & Hll & Hr0) HΦ".
  iApply wp_bind_loop_executable.
  iApply (wp_computation (<[register 0 := word 0]> empty)
    with "Hprog Hpc Hll [Hr0]"); try reflexivity.
  { econstructor; try reflexivity. }
  { iApply big_sepM_insert. { constructor. }
    iFrame. by iApply big_sepM_empty. }
  iNext. iIntros "(Hprog & Hpc & Hll & H)". simpl.
  iApply wp_loop_next.
  iApply wp_bind_loop_executable.
  iApply (wp_control_flow (<[register 0:= word 4]> ∅) with "[$Hprog] [$Hpc] [$Hll] [$H]"); try reflexivity.
  { econstructor; reflexivity. }

  iNext. iIntros "(Hprog & Hpc & Hll & Hmap)".
  simpl. iApply wp_loop_next.
  iApply wp_bind_loop_executable.
  iApply (wp_halt with "[$Hprog] [$Hpc] [$Hll]"); try reflexivity.
  iNext. iIntros "(Hprog & Hpc & Hll)". simpl.
  iApply wp_loop_halted. iApply "HΦ". iFrame.
  iPoseProof (big_sepM_insert with "Hmap") as "[H1 H2]".
  { constructor. }
  iFrame.
Qed.



End asm_lang_rules.
