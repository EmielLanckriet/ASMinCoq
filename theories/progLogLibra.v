From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting total_lifting total_weakestpre.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.
From ASMinCoq Require Import CpdtTactics progLogHelper AsmGen AsmGenLibra.



Class libraGS Σ := LibraGS {
                              libraGS_invGS : invGS Σ;
                              libra_memGS :: gen_heapGS Addr Word Σ;
                              libra_regGS :: gen_heapGS Register Word Σ;
                              libra_llGS :: traceG (list leak) Σ;
                              libra_pcGS :: traceG Word Σ;
                              libra_progGS :: traceG programLibra Σ;
                              libra_loGS :: traceG LO Σ;
                            }.

(* Need it for dwp or something, forget how this worked momentarily
Class allDGLibra Σ := AllDGLibra {
                      DG_invG :: invGS Σ;
                      DG_memG :: gen_heapGS Addr Word Σ;
                      DG_regG :: gen_heapGS Register Word Σ;
                      DG_llG :: traceG (list leak) Σ;
                      DG_pcG :: traceG Word Σ;
                      DG_progG :: traceG programLibra Σ;
                    }.
*)

Definition prog_frag `{!libraGS Σ} := @tr_frag programLibra Σ libra_progGS.
Definition pc_frag `{!libraGS Σ} := @tr_frag Word Σ libra_pcGS.
Definition ll_frag `{!libraGS Σ} := @tr_frag (list leak) Σ libra_llGS.
Definition lo_frag `{!libraGS Σ} := @tr_frag LO Σ libra_loGS.

Definition prog_auth `{!libraGS Σ} := @tr_auth programLibra Σ libra_progGS.
Definition pc_auth `{!libraGS Σ} := @tr_auth Word Σ libra_pcGS.
Definition ll_auth `{!libraGS Σ} := @tr_auth (list leak) Σ libra_llGS.
Definition lo_auth `{!libraGS Σ} := @tr_auth LO Σ libra_loGS.

Section libra_lang_rules.
  Context `{!libraGS Σ}.
  Import libra_lang.



Global Program Instance libra_irisGS `{!libraGS Σ} : irisGS libra_lang Σ := {
    iris_invGS := libraGS_invGS;
    state_interp σ _ κs _ :=
      ((@gen_heap_interp _ _ _ _ _ libra_regGS (reg σ.1.2)) ∗
         (@gen_heap_interp _ _ _ _ _ libra_memGS (mem σ.1.2)) ∗
         ll_auth σ.2 ∗
         pc_auth (PC σ.1.2) ∗
         lo_auth (Lo σ.1.2) ∗
         prog_auth σ.1.1)%I;
    fork_post _ := True%I;
    num_laters_per_step n := n;
  }.
Next Obligation.
  iIntros (Σ' ??? κs') "/= ($ & $ & H)".
  iFrame. by iModIntro.
Qed.

  Notation "r ↦ᵣlibra{ q } w" := (pointsto (hG := libra_regGS) (L:=Register) (V:=Word) r q w)
                              (at level 20, q at level 50, format "r  ↦ᵣlibra{ q }  w") : bi_scope.
  Notation "r ↦ᵣlibra w" := (pointsto (hG := libra_regGS) (L:=Register) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.

  (* Points to predicates for memory *)
  Notation "a ↦ₐlibra{ q } w" := (pointsto (hG := libra_memGS) (L:=Addr) (V:=Word) a q w)
                              (at level 20, q at level 50, format "a  ↦ₐlibra{ q }  w") : bi_scope.
  Notation "a ↦ₐlibra w" := (pointsto (hG := libra_memGS) (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.


  Lemma wp_halt pc lo prog ll E Φ :
    prog (pc , lo) = HaltL ->
    prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗ ll_frag ll -∗
    ▷ (prog_frag prog ∗ pc_frag pc ∗ lo_frag lo ∗ ll_frag (HaltLeak :: ll) -∗ Φ HaltedV) -∗
    WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt) "Hprog Hpc Hlo Hll HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hauthreg & Hauthmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible.
    - iIntros (e2 σ2 efs) "%steps test".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite PCLO_is_PC_LO in prpcHalt.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *. iFrame.
      iPoseProof (trace_update _ (HaltLeak :: ll) with "[$Hauthtrace $Hll]") as "H".
      iMod "H". iModIntro. iNext. iModIntro.
      iDestruct "H" as "[Hauthll Hfragll]". iFrame.
      iSplitR.
      { iPureIntro; reflexivity. }
      iApply "HΦ". iFrame.
  Qed.

  Lemma twp_halt pc lo prog ll E Φ :
    prog (pc , lo) = HaltL ->
    prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗ ll_frag ll -∗
    (prog_frag prog ∗ pc_frag pc ∗ lo_frag lo ∗ ll_frag (HaltLeak :: ll) -∗ Φ HaltedV) -∗
    twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt) "Hprog Hpc Hlo Hll HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hauthreg & Hauthmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible_no_obs.
    - iIntros (κ e2 σ2 efs) "%steps".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite PCLO_is_PC_LO in prpcHalt.
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


  Definition regs_of (i: instrLibra): gset Register :=
    match i with
    | ComputationL inputs rres f_result => {[ rres ]} ∪ regs_from_inputs inputs
    | ControlFlowL inputs dst f_condition => regs_from_inputs inputs
    | LOControlFlowL inputs offset1 offset2 f_condition => regs_from_inputs inputs
    | LoadL rres rsrc => {[ rres; rsrc ]}
    | StoreL rdst src => {[ rdst ]} ∪ regs_of_argument src
    | _ => ∅
    end.

  Lemma regs_of_computation {n : nat} (inputs : vec (Word + Register) n)
    (rres : Register) (f_result : vec Word n -> Word) i :
    i = ComputationL inputs rres f_result ->
    regs_of i = {[ rres ]} ∪ regs_from_inputs inputs.
  Proof.
    intros. subst.
    reflexivity.
  Qed.



  Lemma regs_of_control_flow {n : nat} (secret : bool) (inputs : vec (Word + Register) n)
    (dst : Word) (f_condition : vec Word n -> bool) i :
    i = ControlFlowL inputs dst f_condition ->
    regs_of i = regs_from_inputs inputs.
  Proof.
    intros. subst.
    reflexivity.
  Qed.

  Lemma regs_of_locontrol_flow {n : nat} (secret : bool) (inputs : vec (Word + Register) n)
    (offset1 offset2 : LO) (f_condition : vec Word n -> bool) i :
    i = LOControlFlowL inputs offset1 offset2 f_condition ->
    regs_of i = regs_from_inputs inputs.
  Proof.
    intros. subst.
    reflexivity.
  Qed.


Inductive Computation_spec {n : nat} (inputs : vec (Word + Register) n) (rres : Register) f_result (regs : Reg) (regs' : Reg) : Prop :=
  | Computation_spec_success vn  :
      inputs_from_inputnatregs regs inputs = vn ->
      (<[ rres := f_result vn ]> regs) = regs' ->
      Computation_spec inputs rres f_result regs regs'.

Lemma wp_computation {n : nat} regs regs' pc lo prog ll
    (inputs : vec (Word + Register) n) rres f_result Φ E :
  prog (pc , lo) = ComputationL inputs rres f_result ->
  regs_of (ComputationL inputs rres f_result) ⊆ dom regs →
  Computation_spec (n := n) inputs rres f_result regs regs' ->
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗
  ll_frag ll -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
    ▷ ((prog_frag prog ∗ pc_frag (incr_word pc) ∗ lo_frag lo ∗ ll_frag (ComputationLeak f_result :: ll) ∗
    [∗ map] k↦y ∈ regs', k ↦ᵣlibra y) -∗ Φ NextIV) -∗
    WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt regs_subset Hcomp) "Hprog Hpc Hlo Hll HlistOfRegs HΦ".
    inversion Hcomp; subst; clear Hcomp.
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll']. 
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
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
      rewrite PCLO_is_PC_LO in prpcHalt.
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


Lemma twp_computation {n : nat} regs regs' pc lo prog ll
    (inputs : vec (Word + Register) n) rres f_result Φ E :
  prog (pc , lo) = ComputationL inputs rres f_result ->
  regs_of (ComputationL inputs rres f_result) ⊆ dom regs →
  Computation_spec (n := n) inputs rres f_result regs regs' ->
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗
  ll_frag ll -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
  ((prog_frag prog -∗ pc_frag (incr_word pc) -∗ lo_frag lo -∗ ll_frag (ComputationLeak f_result :: ll) -∗
    [∗ map] k↦y ∈ regs', k ↦ᵣlibra y) -∗ Φ NextIV) -∗
    twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt regs_subset Hcomp) "Hprog Hpc Hlo Hll HlistOfRegs HΦ".
    inversion Hcomp; subst; clear Hcomp.
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll']. 
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
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
      rewrite PCLO_is_PC_LO in prpcHalt.
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

Inductive Control_flow_spec {n : nat} (inputs : vec (Word + Register) n) (dst : Word) f_condition (regs : Reg) (pc pc' : Word) : Prop :=
  | Control_flow_spec_true_success vn :
      inputs_from_inputnatregs regs inputs = vn ->
      f_condition vn = true ->
      dst = pc' ->
      Control_flow_spec inputs dst f_condition regs pc pc'
  | Control_flow_spec_false_success vn :
      inputs_from_inputnatregs regs inputs = vn ->
      f_condition vn = false ->
      incr_word pc = pc' ->
      Control_flow_spec inputs dst f_condition regs pc pc'.

Lemma wp_control_flow {n : nat} regs pc pc' lo' prog ll (inputs : vec (Word + Register) n) dst f_condition E Φ :
  prog (pc, lo') = ControlFlowL inputs dst f_condition ->
  Control_flow_spec inputs dst f_condition regs pc pc' ->
  regs_of (ControlFlowL inputs dst f_condition) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo' -∗ ll_frag ll -∗
  ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
  ▷(prog_frag prog ∗ pc_frag pc' ∗ lo_frag (lo 0) ∗
      ll_frag ((ControlFlowLeak [pc'])
                 :: ll) ∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗ Φ NextIV) -∗
    WP (Instr Executable) @ E {{ v, Φ v }}.
Proof.
    iIntros (prpcHalt HcontrolFlow regs_subset) "Hprog Hpc Hlo Hll HlistOfRegs HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.   
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible.
    - iIntros (e2 σ2 efs) "%steps _".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite PCLO_is_PC_LO in prpcHalt.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.
      inversion HcontrolFlow; subst; clear HcontrolFlow.
      all: rewrite (inputs_are_enough _ Hregs) in H1; auto.
      all: destruct (f_condition (inputs_from_inputnatregs (reg φ) inputs)) as [|] eqn:Hcondition; try congruence.
      1: iPoseProof (trace_update _ (ControlFlowLeak [pc'] :: ll) with "[$Hauthtrace $Hll]") as "H1".
      2: iPoseProof (trace_update _ (ControlFlowLeak [PC (incr_PC φ)] :: ll) with "[$Hauthtrace $Hll]") as "H1".
      1: iPoseProof (trace_update _ pc' with "[$Hauthpc $Hpc]") as "H2".
      2: iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
      all: iPoseProof (trace_update _ (lo 0) with "[$Hauthlo $Hlo]") as "H3".
      all: iMod "H1"; iMod "H2"; iMod "H3"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]"; iDestruct "H3" as "[Hauthlo Hfraglo]"; iFrame.
      all: iModIntro; iNext; iModIntro.
      all: iSplitR; try (iPureIntro; reflexivity).
      all: iApply "HΦ".
      all: iFrame.
Qed.


Lemma twp_control_flow {n : nat} regs pc pc' lo' prog ll (inputs : vec (Word + Register) n) dst f_condition E Φ :
  prog (pc , lo') = ControlFlowL inputs dst f_condition ->
  Control_flow_spec inputs dst f_condition regs pc pc' ->
  regs_of (ControlFlowL inputs dst f_condition) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo' -∗ ll_frag ll -∗
  ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
  (prog_frag prog ∗ pc_frag pc' ∗ lo_frag (lo 0) ∗
     ll_frag (ControlFlowLeak [pc'] :: ll) ∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗ Φ NextIV) -∗
    twp NotStuck E (Instr Executable) Φ.
Proof.
    iIntros (prpcHalt HcontrolFlow regs_subset) "Hprog Hpc Hlo Hll HlistOfRegs HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.   
    iModIntro.
    iSplitR.
    - iPureIntro. apply normal_always_reducible_no_obs.
    - iIntros (κ e2 σ2 efs) "%steps".
      inversion steps; subst; simpl in *.
      inversion H; subst.
      simpl in *.
      rewrite PCLO_is_PC_LO in prpcHalt.
      rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.
      inversion HcontrolFlow; subst; clear HcontrolFlow.
      all: rewrite (inputs_are_enough _ Hregs) in H1; auto.
      all: destruct (f_condition (inputs_from_inputnatregs (reg φ) inputs)) as [|] eqn:Hcondition; try congruence.
      1: iPoseProof (trace_update _ (ControlFlowLeak [pc'] :: ll) with "[$Hauthtrace $Hll]") as "H1".
      2: iPoseProof (trace_update _ (ControlFlowLeak [PC (incr_PC φ)] :: ll) with "[$Hauthtrace $Hll]") as "H1".
      1: iPoseProof (trace_update _ pc' with "[$Hauthpc $Hpc]") as "H2".
      2: iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
      all: iPoseProof (trace_update _ (lo 0) with "[$Hauthlo $Hlo]") as "H3".
      all: iMod "H1"; iMod "H2"; iMod "H3"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]"; iDestruct "H3" as "[Hauthlo Hfraglo]"; iFrame.
      all: iModIntro.
      all: do 2 (iSplitR; try (iPureIntro; reflexivity)).
      all: iApply "HΦ".
      all: iFrame.
Qed.

Lemma wp_load {n : nat} pc lo prog ll regs rres rsrc v E Φ :
  prog (pc, lo) = LoadL rres rsrc ->
  regs_of (LoadL rres rsrc) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
      word_to_addr (regs !!! rsrc) ↦ₐlibra v -∗
  ▷(prog_frag prog ∗ pc_frag (incr_word pc) ∗ lo_frag lo ∗
      ll_frag (LoadLeak (word_to_addr (regs !!! rsrc)) :: ll) ∗
      ([∗ map] k↦y ∈ <[ rres := v ]>regs, k ↦ᵣlibra y) -∗ Φ NextIV) -∗
  WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hlo Hll HlistOfRegs Haddrv HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible. }
    iIntros (e2 σ2 efs) "%steps _".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite PCLO_is_PC_LO in prpcHalt.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update _ (LoadLeak (word_to_addr (reg φ !!! rsrc)) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite reg_is_updated_value.
    iMod ((gen_heap_update_inSepM _ _ rres) with "Hreg HlistOfRegs") as "[Hr Hmap]".
    { eapply @elem_of_dom with (D := gset Register). typeclasses eauto.
    eapply elem_of_subseteq; eauto. set_solver. }
    iPoseProof (gen_heap_valid (gen_heapGS0 := libra_memGS) with "Hmem Haddrv") as "%Hmem'".
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


Lemma twp_load {n : nat} pc lo prog ll regs rres rsrc v E Φ :
  prog (pc, lo) = LoadL rres rsrc ->
  regs_of (LoadL rres rsrc) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
      word_to_addr (regs !!! rsrc) ↦ₐlibra v -∗
  (prog_frag prog ∗ pc_frag (incr_word pc) ∗ lo_frag lo ∗
      ll_frag (LoadLeak (word_to_addr (regs !!! rsrc)) :: ll) ∗
      ([∗ map] k↦y ∈ <[ rres := v ]>regs, k ↦ᵣlibra y) -∗ Φ NextIV) -∗
  twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hlo Hll HlistOfRegs Haddrv HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible_no_obs. }
    iIntros (κ e2 σ2 efs) "%steps".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite PCLO_is_PC_LO in prpcHalt.
    rewrite prpcHalt in steps. rewrite prpcHalt. simpl in *.

    iPoseProof (trace_update _ (LoadLeak (word_to_addr (reg φ !!! rsrc)) :: ll) with "[$Hauthtrace $Hll]") as "H1".
    iPoseProof (trace_update _ (incr_word (PC φ)) with "[$Hauthpc $Hpc]") as "H2".
    iMod "H1"; iMod "H2"; iDestruct "H1" as "[Hauthll Hfragll]"; iDestruct "H2" as "[Hauthpc Hfragpc]".
    
    unfold incr_PC. rewrite -update_pc_no_change_reg. rewrite reg_is_updated_value.
    iMod ((gen_heap_update_inSepM _ _ rres) with "Hreg HlistOfRegs") as "[Hr Hmap]".
    { eapply @elem_of_dom with (D := gset Register). typeclasses eauto.
    eapply elem_of_subseteq; eauto. set_solver. }
    iPoseProof (gen_heap_valid (gen_heapGS0 := libra_memGS) with "Hmem Haddrv") as "%Hmem'".
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

Lemma wp_store pc lo prog ll regs rdst src v E Φ :
  prog (pc, lo) = StoreL rdst src ->
  regs_of (StoreL rdst src) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
      word_to_addr (regs !!! rdst) ↦ₐlibra v -∗
  ▷(prog_frag prog ∗ pc_frag (incr_word pc) ∗ lo_frag lo ∗
      ll_frag (StoreLeak (word_to_addr (wordreg_to_word regs src)) :: ll) ∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) ∗
      word_to_addr (regs !!! rdst) ↦ₐlibra wordreg_to_word regs src -∗
    Φ NextIV) -∗
     WP (Instr Executable) @ E {{ v, Φ v }}.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hlo Hll HlistOfRegs Haddrv HΦ".
    iApply wp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κ κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible. }
    iIntros (e2 σ2 efs) "%steps _".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite PCLO_is_PC_LO in prpcHalt.
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


Lemma twp_store pc lo prog ll regs rdst src v E Φ :
  prog (pc, lo) = StoreL rdst src ->
  regs_of (StoreL rdst src) ⊆ dom regs →
  prog_frag prog -∗ pc_frag pc -∗ lo_frag lo -∗ ll_frag ll -∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) -∗
      word_to_addr (regs !!! rdst) ↦ₐlibra v -∗
  (prog_frag prog ∗ pc_frag (incr_word pc) ∗ lo_frag lo ∗
      ll_frag (StoreLeak (word_to_addr (wordreg_to_word regs src)) :: ll) ∗
      ([∗ map] k↦y ∈ regs, k ↦ᵣlibra y) ∗
      word_to_addr (regs !!! rdst) ↦ₐlibra wordreg_to_word regs src -∗
    Φ NextIV) -∗
    twp NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (prpcHalt regs_subset) "Hprog Hpc Hlo Hll HlistOfRegs Haddrv HΦ".
    iApply twp_lift_atomic_step_no_fork_fupd; auto.
    iIntros (σ ns κs nt) "(Hreg & Hmem & Hauthtrace & Hauthpc & Hauthlo & Hauthprog)".
    destruct σ as [s ll'].
    simpl.
    iDestruct (@trace_full_frag_eq with "Hauthtrace Hll") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthpc Hpc") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthlo Hlo") as %?; subst; auto.
    iDestruct (@trace_full_frag_eq with "Hauthprog Hprog") as %?; subst; auto.
    iDestruct (gen_heap_valid_inclSepM with "Hreg HlistOfRegs") as %Hregs.
    iModIntro.

    iSplitR.
    { iPureIntro. apply normal_always_reducible_no_obs. }
    iIntros (κ e2 σ2 efs) "%steps".
    inversion steps; subst; simpl in *.
    inversion H; subst.
    simpl in *.
    rewrite PCLO_is_PC_LO in prpcHalt.
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

#[export] Instance language_ctx_loopify : @LanguageCtx libra_lang loopify.
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
      (Φ : language.val libra_lang → iProp Σ) :
      WP Instr Executable @ s; E {{ v, WP ((fun v' => loopify (language.of_val v')) v) @ s; E {{ v, Φ v }} }}
      ⊢ WP Loop Executable @ s; E {{ Φ }} :=
  wp_bind loopify s E (Instr Executable) Φ.


#[export] Instance inhabited_libra_state : Inhabited (language.state libra_lang).
Proof.
  constructor.
  exact (list_prog_to_prog_libra [[]], (word 0, lo 0, emptyReg, emptyMem), []).
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


Definition test_prog_not_constant_time_libra (high_input : nat) :=
    list_prog_to_prog_libra [[AddL (register 0) (inl (word high_input)) (inl (word high_input))]; [JnzL (inr (register 0)) (word 3)]].

Lemma wp_test :
  {{{ prog_frag (test_prog_not_constant_time_libra 2) ∗
      pc_frag (word 0) ∗ lo_frag (lo 0) ∗ ll_frag [] ∗
      register 0 ↦ᵣlibra word 0 }}}
      (Loop Executable)
  {{{ RET LoopHaltedV; prog_frag (test_prog_not_constant_time_libra 2)
      ∗ pc_frag (word 3) ∗ lo_frag (lo 0) ∗
      ll_frag ([HaltLeak; ControlFlowLeak [word 3]; AddLeak]) ∗
      register 0 ↦ᵣlibra word 4
     }}}.
Proof.
  iIntros (Φ) "(Hprog & Hpc & Hlo & Hll & Hr0) HΦ".
  iApply wp_bind_loop_executable.
  iApply (wp_computation (<[register 0 := word 0]> empty)
    with "Hprog Hpc Hlo Hll [Hr0]"); try reflexivity.
  { econstructor; try reflexivity. }
  { iApply big_sepM_insert. { constructor. }
    iFrame. by iApply big_sepM_empty. }
  iNext. iIntros "(Hprog & Hpc & Hlo & Hll & H)". simpl.
  iApply wp_loop_next.
  iApply wp_bind_loop_executable.
  iApply (wp_control_flow (<[register 0:= word 4]> ∅) with "[$Hprog] [$Hpc] [$Hlo] [$Hll] [$H]"); try reflexivity.
  { econstructor; reflexivity. }

  iNext. iIntros "(Hprog & Hpc & Hlo & Hll & Hmap)".
  simpl. iApply wp_loop_next.
  iApply wp_bind_loop_executable.
  iApply (wp_halt with "[$Hprog] [$Hpc] [$Hlo] [$Hll]"); try reflexivity.
  iNext. iIntros "(Hprog & Hpc & Hll)". simpl.
  iApply wp_loop_halted. iApply "HΦ". iFrame.
  iPoseProof (big_sepM_insert with "Hmap") as "[H1 H2]".
  { constructor. }
  iFrame.
Qed.



End libra_lang_rules.
