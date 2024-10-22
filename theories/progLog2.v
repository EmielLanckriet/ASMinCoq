From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting total_weakestpre.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.
From ASMinCoq Require Import CpdtTactics.
From ASMinCoq Require Import AsmGen progLog.

Class binDG Σ := BinDG {
  bin_invG :> invGS Σ;
  fst_memG :> gen_heapGS Addr Word Σ;
  snd_memG :> gen_heapGS Addr Word Σ;
  fst_regG :> gen_heapGS Register Word Σ;
  snd_regG :> gen_heapGS Register Word Σ;
  fst_traceG :: traceG (list leak) Σ;
  fst_pcG :: traceG Word Σ;
  fst_progG :: traceG program Σ;
  snd_traceG :: traceG (list leak) Σ;
  snd_pcG :: traceG Word Σ;
  snd_progG :: traceG program Σ;
}.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance irisG1 `{!binDG Σ} : irisGS asm_lang Σ := {
    iris_invGS := bin_invG;
    state_interp σ _ κs _ :=
      ((@gen_heap_interp _ _ _ _ _ fst_regG (reg σ.1.2)) ∗
         (@gen_heap_interp _ _ _ _ _ fst_memG (mem σ.1.2)) ∗
         @tr_auth _ _ fst_traceG σ.2 ∗
         @tr_auth _ _ fst_pcG (PC σ.1.2) ∗
         @tr_auth _ _ fst_progG σ.1.1)%I;
    fork_post _ := False%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.

Global Instance irisG2 `{!binDG Σ} : irisGS asm_lang Σ := {
    iris_invGS := bin_invG;
    state_interp σ _ κs _ :=
      ((@gen_heap_interp _ _ _ _ _ snd_regG (reg σ.1.2)) ∗
         (@gen_heap_interp _ _ _ _ _ snd_memG (mem σ.1.2)) ∗
         @tr_auth _ _ snd_traceG σ.2 ∗
         @tr_auth _ _ snd_pcG (PC σ.1.2) ∗
         @tr_auth _ _ snd_progG σ.1.1)%I;
    fork_post _ := False%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.

Definition TWP1 `{!binDG Σ} (e : expr) (E : coPset) (R : val → iProp Σ) :=
  @twp (iProp Σ) expr val stuckness
    (@twp' _ asm_lang Σ irisG1)
    NotStuck E e R.

Definition TWP2 `{!binDG Σ} (e : expr) (E : coPset) (R : val → iProp Σ) :=
  @twp (iProp Σ) expr val stuckness
    (@twp' _ asm_lang Σ irisG2)
    NotStuck E e R.

Section asm_lang_rules.
  Context `{!binDG Σ}.
  Context (γ ζ ξ : gname).
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


