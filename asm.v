From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on Register *)
From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_maps relations.
From ASMinCoq Require Import CpdtTactics.

Definition Register := nat.

Global Instance reg_eq_dec : EqDecision Register.
Proof. intros r1 r2.
       destruct (Nat.eq_dec r1 r2).
       + subst. left. reflexivity.
       + right. congruence.
Defined.

Global Instance reg_countable : Countable Register.
Proof.
    refine {| encode r := encode (match r with
                               | n => n
                               end );
            decode n := match (decode n) with
                        | Some n => Some n
                        | _ => None
                        end ;
            decode_encode := _ |}.
    intro r. destruct r; auto.
    rewrite decode_encode.
    reflexivity.
Defined.

Definition Word := nat.

Inductive instr : Type :=
| Jmp (r: Register)
| Jnz (r1 r2: Register)
| Mov (dst: Register) (src: nat + Register)
| Load (dst src: Register)
| Store (dst: Register) (src : nat + Register)
| Add (dst: Register) (r1 r2: nat + Register)
| Sub (dst: Register) (r1 r2: nat + Register).

(**
| Fail
| Halt
| Lt (dst: Register) (r1 r2: nat + Register)
| Add (dst: Register) (r1 r2: nat + Register)
| Sub (dst: Register) (r1 r2: nat + Register)
*)


Definition Addr := nat.

Global Instance addr_countable : Countable Addr.
Proof.
    refine {| encode r := encode (match r with
                               | n => n
                               end );
            decode n := match (decode n) with
                        | Some n => Some n
                        | _ => None
                        end ;
            decode_encode := _ |}.
    intro r. destruct r; auto.
    rewrite decode_encode.
    reflexivity.
Defined.

Global Instance addr_eq_dec : EqDecision Addr.
Proof. intros r1 r2.
       destruct (Nat.eq_dec r1 r2).
       + subst. left. reflexivity.
       + right. congruence.
Defined.

Definition Reg := gmap Register Word.
Definition Mem := gmap Addr Word.

Definition ExecConf := (Word * Reg * Mem)%type.


Definition reg (ϕ : ExecConf) := snd (fst ϕ).

Definition mem (ϕ : ExecConf) := snd ϕ.

Definition PC (φ : ExecConf) := fst (fst φ).


Definition update_reg (φ : ExecConf) (r : Register) (w : Word): ExecConf :=
    (PC φ,<[r:=w]>(reg φ),mem φ).
Definition update_mem (φ : ExecConf) (a : Addr) (w : Word): ExecConf :=
    (PC φ,reg φ, <[a:=w]>(mem φ)).
Definition update_PC (φ : ExecConf) (w : Word) : ExecConf :=
    (w, reg φ, mem φ).

Definition incr_PC (φ : ExecConf) : ExecConf :=
    update_PC φ (PC φ + 1).

Definition nonZero (w: Word): bool :=
    negb (Nat.eqb w 0).
    
Definition zero  (w: Word): bool :=
    Nat.eqb w 0.

Definition word_from_argument (φ: ExecConf) (src : nat + Register) : option Word :=
    match src with
    | inl n => Some n
    | inr r => (reg φ) !! r
    end.

Definition exec_instr_opt (i: instr) (φ: ExecConf) : option ExecConf :=
    match i with
    | Jmp r =>
      wr ← (reg φ) !! r;
      Some (update_PC φ wr)
    | Jnz r1 r2 =>
      wr2 ← (reg φ) !! r2;
      wr1 ← (reg φ) !! r1;
      if nonZero wr2 then
        Some (update_PC φ wr1)
      else Some (incr_PC φ)
    | Load dst src =>
      wsrc ← (reg φ) !! src;
      asrc ← (mem φ) !! wsrc;
      Some (incr_PC (update_reg φ dst asrc))
    | Store dst ρ =>
        wdst ← (reg φ) !! dst;
        tostore ← word_from_argument φ ρ;
        Some (incr_PC (update_mem φ wdst tostore))
    | Mov dst ρ =>
        wdst ← (reg φ) !! dst;
        tomov ← word_from_argument φ ρ;
        Some (incr_PC (update_reg φ wdst tomov))
    | Add dst ρ1 ρ2 =>
        n1 ← word_from_argument φ ρ1;
        n2 ← word_from_argument φ ρ2;
        Some (incr_PC (update_reg φ dst (n1 + n2)))
    | Sub dst ρ1 ρ2 =>
        n1 ← word_from_argument φ ρ1;
        n2 ← word_from_argument φ ρ2;
        Some (incr_PC (update_reg φ dst (n1 - n2)))
    end.

Definition emptyReg : Reg := empty.
Definition emptyMem : Mem := empty.

Definition program : Type := Word -> option instr.

Definition list_prog_to_prog (li : list instr) : program :=
    fun (w : Word) => nth_error li w.

Definition exec_instr_at_PC (prog : program) (φ : ExecConf) : option ExecConf :=
    match (prog (PC φ)) with
    | None => None
    | Some i => exec_instr_opt i φ
    end.

Fixpoint exec_prog (prog : program) (φ : ExecConf) (time : nat) : ExecConf :=
    match time with
    | 0 => φ
    | S time' => match (exec_instr_at_PC prog φ) with
                 | None => φ
                 | Some φ' => exec_prog prog φ' time'
                 end
    end.

Inductive Exec_prog_one_step_ind (prog : program) (φ : ExecConf) : ExecConf -> Prop :=
| ExecJmp (w : Word) (r : Register) (PC_is_jmp : prog (PC φ) = Some (Jmp r))
    (reg_is_valid : (reg φ) !! r = Some w) :
    Exec_prog_one_step_ind prog φ (update_PC φ w)
| ExecJnzNonZero (w1 w2 : Word) (r1 r2 : Register)
    (PC_is_jnz : prog (PC φ) = Some (Jnz r1 r2))
    (reg1_is_valid : (reg φ) !! r1 = Some w1)
    (reg2_is_valid : (reg φ) !! r2 = Some w2)
    (nz2 : nonZero w2 = true) :
    Exec_prog_one_step_ind prog φ (update_PC φ w1)
| ExecJnzZero (w1 w2 : Word) (r1 r2 : Register)
    (PC_is_jnz : prog (PC φ) = Some (Jnz r1 r2))
    (reg1_is_valid : (reg φ) !! r1 = Some w1)
    (reg2_is_valid : (reg φ) !! r2 = Some w2)
    (nz2 : nonZero w2 = false) :
    Exec_prog_one_step_ind prog φ (incr_PC φ)
| ExecLoad (wsrc asrc : Word) (rdst rsrc : Register)
    (PC_is_load : prog (PC φ) = Some (Load rdst rsrc))
    (regsrc_is_valid : (reg φ) !! rsrc = Some wsrc)
    (memwsrc_is_valid : (mem φ) !! wsrc = Some asrc) :
    Exec_prog_one_step_ind prog φ (incr_PC (update_reg φ rdst asrc))
| ExecStore (wdst wsrc : Word) (rdst : Register) (ρ : nat + Register)
    (PC_is_store : prog (PC φ) = Some (Store rdst ρ))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq_ρ : word_from_argument φ ρ = Some wsrc) :
    Exec_prog_one_step_ind prog φ (incr_PC (update_mem φ wdst wsrc))
| ExecMoveReg (wdst wsrc : Word) (rdst : Register) (ρ : nat + Register)
    (PC_is_mov : prog (PC φ) = Some (Mov rdst ρ))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq : word_from_argument φ ρ = Some wsrc) :
    Exec_prog_one_step_ind prog φ (incr_PC (update_reg φ wdst wsrc))
| ExecAdd (wdst w1 w2 : Word) (rdst : Register) (ρ1 ρ2 : nat + Register)
    (PC_is_add : prog (PC φ) = Some (Add rdst ρ1 ρ2))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq_ρ1 : word_from_argument φ ρ1 = Some w1)
    (eq_ρ2 : word_from_argument φ ρ2 = Some w2) :
    Exec_prog_one_step_ind prog φ (incr_PC (update_reg φ rdst (w1 + w2)))
| ExecSub (wdst w1 w2 : Word) (rdst : Register) (ρ1 ρ2 : nat + Register)
    (PC_is_sub : prog (PC φ) = Some (Sub rdst ρ1 ρ2))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq_ρ1 : word_from_argument φ ρ1 = Some w1)
    (eq_ρ2 : word_from_argument φ ρ2 = Some w2) :
    Exec_prog_one_step_ind prog φ (incr_PC (update_reg φ rdst (w1 - w2)))
.

Definition Exec_prog_ind (prog : program) : relation ExecConf :=
    rtc (Exec_prog_one_step_ind prog).

Definition Exec_prog_n_steps_ind (prog : program) : nat -> relation ExecConf :=
    nsteps (Exec_prog_one_step_ind prog).

Lemma testExec_Prog : Exec_prog_one_step_ind (list_prog_to_prog [Add 0 (inl 1) (inr 0)]) (0, <[0:=0]>(emptyReg), emptyMem) (1, <[0:=1]>(emptyReg), emptyMem).
Proof.
    assert (incr_PC (update_reg (0, <[0:=0]>(emptyReg), emptyMem) 0 (1 + 0)) = (1, <[0:=1]>(emptyReg), emptyMem)) as H.
    { reflexivity. }
    rewrite -H.
    eapply ExecAdd; try reflexivity.
Qed.

(**
Lemma soundness_exec_one_step (prog : program) (φ φ' : ExecConf) :
    Exec_prog_one_step_ind prog φ φ' -> exec_prog prog φ 1 = φ'.
    (** The other direction doesn't hold because invalid operation do nothing (configuration stays the same) in exec_prog while in Exec_prog_one_step_ind there is no evaluation step. *)
    (** Find out how to automate this better, the few match statements should be given to crush *)
Proof.
    intro H.
    destruct (prog (PC φ)) as [i|] eqn:Hi.
    - induction i; inversion H; try congruence;
        simpl; unfold exec_instr_at_PC; rewrite Hi; simpl;
        match goal with
        | H1 : prog (PC φ) = _, H2 : prog (PC φ) = _ |- _ =>
            rewrite H1 in H2; injection H2; intros
        end;
        subst;
        do 2 try match goal with
        | H1 : word_from_argument _ _ = _ |- _ =>
            rewrite H1
        end; simpl;
        try match goal with
        | H1 : (reg φ) !! _ = _ |- _ =>
            rewrite H1
        end; simpl; try reflexivity;
        try match goal with
        | H1 : (reg φ) !! _ = _ |- _ =>
            rewrite H1
        end; simpl;
        try match goal with
        | H1 : nonZero _ = _ |- _ =>
            rewrite H1
        end; try reflexivity;
        try match goal with
        | H1 : (mem φ) !! _ = _ |- _ =>
            rewrite H1
        end; reflexivity.
    - inversion H; try congruence.
Qed.
*)

Ltac bind_rewrite :=
    match goal with
    | H : ?x = _ |- context[?x ≫= _] => rewrite H; cbn
    end.

Ltac bool_cond_if :=
    match goal with
    | H : ?x = true |- context[if ?x then _ else _] => rewrite H
    | H : ?x = false |- context[if ?x then _ else _] => rewrite H
    end.

Ltac subst_in_match :=
    match goal with
    | H : ?x = _ |- context[match ?x with
                        | _ => _
                        end] => rewrite H; cbn
    end.


Lemma soundness_exec_one_step (prog : program) (φ φ' : ExecConf) :
    Exec_prog_one_step_ind prog φ φ' -> exec_prog prog φ 1 = φ'.
    (** The other direction doesn't hold because invalid operation do nothing (configuration stays the same) in exec_prog while in Exec_prog_one_step_ind there is no evaluation step. *)
    (** Find out how to automate this better, the few match statements should be given to crush *)
Proof.
    intro H.
    destruct (prog (PC φ)) as [i|] eqn:Hi.
    - induction i; inversion H; try congruence;
        simpl; unfold exec_instr_at_PC; rewrite Hi; simpl;
        match goal with
        | H1 : prog (PC φ) = _, H2 : prog (PC φ) = _ |- _ =>
            rewrite H1 in H2; injection H2; intros
        end; subst;
        repeat bind_rewrite; try bool_cond_if; reflexivity.
    - inversion H; congruence.
Qed.

Hint Unfold exec_instr_at_PC : core.

Lemma soundness_exec_n_steps (prog : program) (n : nat) (φ φ' : ExecConf) :
    Exec_prog_n_steps_ind prog n φ φ' -> exec_prog prog φ n = φ'.
Proof.
    revert φ φ'.
    induction n; intros φ φ' H; inversion H; crush.
    unfold exec_instr_at_PC.
    apply IHn in H2.
    inversion H1; subst_in_match;
    repeat bind_rewrite;
    crush.
Qed.

Print gmap_lookup.

Ltac check_bounded_partial_map_for_match :=
    lazymatch goal with
    | H: context[match ?x !! ?y ≫= _ with
           | @Some z _ => match type_of z with
                          | ExecConf => _
                          | _ => _
                          end
           | None => _
        end] |- _
        => idtac x; idtac y; destruct (?x !! ?y)
    end.

Lemma soundness_exec_one_step' (prog : program) (φ φ' : ExecConf) :
    exec_prog prog φ 1 = φ' -> φ = φ' \/ Exec_prog_one_step_ind prog φ φ'.
Proof.
    simpl. unfold exec_instr_at_PC.
    destruct (prog (PC φ)) as [] eqn:PCφ.
    - destruct i as [] eqn:Hi.
        + unfold exec_instr_opt. intros.
        Set Printing Existential Instances. Set Printing Implicit. check_bounded_partial_map_for_match. destruct (reg φ !! r) as [|] eqn:Hr; crush.
          right. eapply ExecJmp; try eauto.
        


Lemma soundness_exec_n_steps' (prog : program) (n : nat) (φ φ' : ExecConf) :
    exec_prog prog φ n = φ' -> exists m, m <= n -> Exec_prog_n_steps_ind prog m φ φ'.
Proof.
    revert φ φ'.
    induction n; intros φ φ' H.
    - eexists 0. subst. constructor.
    - cbn in H. unfold exec_instr_at_PC in H. 
      destruct (prog (PC φ)); try destruct (exec_instr_opt i φ) as [|] eqn:Hi;
      try solve[subst; exists 0; constructor].
      apply IHn in H as [m H].
      exists (S m). intros HSmSn. apply le_S_n in HSmSn. apply H in HSmSn.
      econstructor; try exact HSmSn.

      
    unfold exec_instr_at_PC.
    apply IHn in H2.
    inversion H1; subst_in_match;
    repeat bind_rewrite;
    crush.
Qed.

    

    