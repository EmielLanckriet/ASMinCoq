From ASMinCoq Require Export dwp.
From iris.proofmode Require Import proofmode.
Set Default Proof Using "Type".

Section lifting.
Context `{!irisDG Λ Σ, !invGS Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → val Λ → iProp Σ.

Lemma dwp_lift_pure_step `{Inhabited (state Λ)} E1 E1' Φ e1 e2 :
  (∀ σ1, reducible e1 σ1) →
  (∀ κ σ1 e1' σ1' efs1, prim_step e1 σ1 κ e1' σ1' efs1 → κ = [] ∧ σ1' = σ1) →
  (∀ σ2, reducible e2 σ2) →
  (∀ κ σ2 e2' σ2' efs2, prim_step e2 σ2 κ e2' σ2' efs2 → κ = [] ∧ σ2' = σ2) →
  (|={E1}[E1']▷=> ∀ κ1 κ2 e1' σ1 efs1 e2' σ2 efs2,
    ⌜prim_step e1 σ1 κ1 e1' σ1 efs1⌝ →
    ⌜prim_step e2 σ2 κ2 e2' σ2 efs2⌝ →
    dwp E1 e1' e2' Φ ∗
    [∗ list] ef1;ef2 ∈ efs1;efs2, dwp ⊤ ef1 ef2 (λ _ _, True ))
  ⊢ dwp E1 e1 e2 Φ.
Proof.
  iIntros (Hsafe1 Hdet1 Hsafe2 Hdet2) "H".
  rewrite (dwp_unfold _ e1 e2) /dwp_pre.
  assert (language.to_val e1 = None) as ->.
  { destruct (Hsafe1 inhabitant) as (?&?&?&?&?).
    eapply val_stuck; eauto. }
  assert (language.to_val e2 = None) as ->.
  { destruct (Hsafe2 inhabitant) as (?&?&?&?&?).
    eapply val_stuck; eauto. }
  iIntros (σ1 σ2 κ1 κs1 κ2 κs2) "Hrel".
  iMod "H" as "H".
  iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first iPureIntro.
  { destruct (Hsafe1 σ1) as (xxx&?&?&?&Hst).
    assert (xxx = []) as ->. { by eapply Hdet1. }
    do 3 eexists. eauto. }
  iSplit; first iPureIntro.
  { destruct (Hsafe2 σ2) as (xxx&?&?&?&Hst).
    assert (xxx = []) as ->. { by eapply Hdet2. }
    do 3 eexists. eauto. }
  iIntros (e1' σ1' efs1 e2' σ2' efs2 Hstep1 Hstep2).
  iModIntro. iNext. iMod "Hclose" as "_".
  iMod "H" as "H".
  assert (σ1' = σ1) as ->.
  { eapply Hdet1. eauto. }
  assert (σ2' = σ2) as ->.
  { eapply Hdet2. eauto. }
  iSpecialize ("H" $! [] [] with "[//] [//]").
  iModIntro. iFrame.
Qed.


Lemma dwp_lift_pure_step_no_fork `{Inhabited (state Λ)} E1 E1' Φ e1 e2 :
  (∀ σ1, reducible e1 σ1) →
  (∀ κ σ1 e1' σ1' efs1, prim_step e1 σ1 κ e1' σ1' efs1 → κ = [] ∧ σ1' = σ1 ∧ efs1 = []) →
  (∀ σ2, reducible e2 σ2) →
  (∀ κ σ2 e2' σ2' efs2, prim_step e2 σ2 κ e2' σ2' efs2 → κ = [] ∧ σ2' = σ2 ∧ efs2 = []) →
  (|={E1}[E1']▷=> ∀ κ1 κ2 e1' σ1 efs1 e2' σ2 efs2,
    ⌜prim_step e1 σ1 κ1 e1' σ1 efs1⌝ →
    ⌜prim_step e2 σ2 κ2 e2' σ2 efs2⌝ →
    dwp E1 e1' e2' Φ)
  ⊢ dwp E1 e1 e2 Φ.
Proof.
  iIntros (redσ1 H1 redσ2 H2) "Hrest". iApply dwp_lift_pure_step; eauto.
  - intros κ σ1 e1' σ1' efs1 H1'. specialize (H1 κ σ1 e1' σ1' efs1 H1') as (Hκ & Hσ1 & _). auto.
  - intros κ σ2 e2' σ2' efs2 H2'. specialize (H2 κ σ2 e2' σ2' efs2 H2') as (Hκ & Hσ21 & _). auto.
  - iApply (fupd_mono with "Hrest"). iIntros "Hrest". iModIntro.
    iApply (fupd_mono with "Hrest").
    iIntros "Hdwp" (κ1 κ2 e1' σ1 efs1 e2' σ2 efs2 Hstep1 Hstep2).
    specialize (H1 κ1 σ1 e1' σ1 efs1 Hstep1) as (Hκ1 & Hσ1 & Hefs1).
    specialize (H2 κ2 σ2 e2' σ2 efs2 Hstep2) as (Hκ2 & Hσ2 & Hefs2).
    
    iSpecialize ("Hdwp" $! κ1 κ2 e1' σ1 efs1 e2' σ2 efs2 Hstep1 Hstep2).
    subst. iFrame "Hdwp".
    done.
Qed.

Lemma dwp_lift_pure_det_step `{!Inhabited (state Λ)} {E1 E1' Φ}
      e1 e1' e2 e2' efs1 efs2 :
  (∀ σ1, reducible e1 σ1) →
  (∀ κ σ1 e1'' σ1' efs1', prim_step e1 σ1 κ e1'' σ1' efs1' → κ = [] ∧ σ1' = σ1 ∧ e1'' = e1' ∧ efs1' = efs1) →
  (∀ σ2, reducible e2 σ2) →
  (∀ κ σ2 e2'' σ2' efs2', prim_step e2 σ2 κ e2'' σ2' efs2' → κ = [] ∧ σ2' = σ2 ∧ e2'' = e2' ∧ efs2' = efs2) →
  (|={E1}[E1']▷=> dwp E1 e1' e2' Φ ∗
    [∗ list] ef1;ef2 ∈ efs1;efs2, dwp ⊤ ef1 ef2 (λ _ _, True ))
  ⊢ dwp E1 e1 e2 Φ.
Proof.
  iIntros (? Hpuredet1 ? Hpuredet2) "H".
  iApply dwp_lift_pure_step; try done.
  { intros. split; by eapply Hpuredet1. }
  { intros. split; by eapply Hpuredet2. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (? ? ? ? ? ? ? ?).
  iIntros ((->&_&->&->)%Hpuredet1 (->&_&->&->)%Hpuredet2).
  iApply "H".
Qed.

Lemma dwp_pure_step_fupd `{!Inhabited (state Λ)} E1 E1' n
      e1 e1' e2 e2' φ1 φ2 Φ :
  PureExec φ1 n e1 e1' →
  PureExec φ2 n e2 e2' →
  φ1 →
  φ2 →
  Nat.iter n (λ P, |={E1}[E1']▷=> P) (dwp E1 e1' e2' Φ)
  ⊢ dwp E1 e1 e2 Φ.
Proof.
  iIntros (Hexec1 Hexec2 Hφ1 Hφ2) "H".
  specialize (Hexec1 Hφ1).
  specialize (Hexec2 Hφ2).
  iInduction Hexec1 as [e1|n e1 e1' e1'' [Hsafe1 ?]] "IH"
     forall (e2 e2' Hexec2); simpl; simpl in Hexec2.
  - by inversion Hexec2.
  - inversion Hexec2 as [|m t2 t2' e2'' [Hsafe2 ?]]. simplify_eq/=.
    iApply dwp_lift_pure_det_step.
    + eauto using reducible_no_obs_reducible.
    + intros σ1 κ e1_ σ1' efs1' Hstep.
      specialize (pure_step_det _ _ _ _ _ Hstep).
      naive_solver.
    + eauto using reducible_no_obs_reducible.
    + intros σ1 κ e1_ σ1' efs1' Hstep.
      specialize (pure_step_det0 _ _ _ _ _ Hstep).
      naive_solver.
    + iApply (step_fupd_wand with "H").
      rewrite big_sepL2_nil. iIntros "H". iSplitL; last done.
      by iApply "IH".
Qed.

Lemma dwp_pure_step_later `{!Inhabited (state Λ)} E1
      e1 e1' e2 e2' n φ1 φ2 Φ :
  PureExec φ1 n e1 e1' →
  PureExec φ2 n e2 e2' →
  φ1 →
  φ2 →
  ▷^n (dwp E1 e1' e2' Φ)
  ⊢ dwp E1 e1 e2 Φ.
Proof.
  intros Hexec1 Hexec2 ??.
  rewrite -(dwp_pure_step_fupd E1 E1) //. clear Hexec1 Hexec2.
  induction n=>// /=.
  by rewrite -(step_fupd_intro E1 E1)// IHn.
Qed.

End lifting.
