From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on Register *)
From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_maps relations vector.
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

Locate vec.

(** Different constructor for instructions that change the control flow, then for instructions that don't
    TODO: I haven't worked this out yet further, because I don't have an idea of which general classes of instructions exist *)
Inductive gen_instr : Type :=
| CF (lr : list Register) (jump_result : list Register -> Register)
| NCF (n : nat) (lr : list Register) (resultReg : vec Register n) (f_result : list Register -> vec Word n).

Inductive instr : Type :=
| Jmp (r: Register)
| Jnz (r1 r2: Register)
| Mov (dst: Register) (src: nat + Register)
| Load (dst src: Register)
| Store (dst: Register) (src : nat + Register)
| Add (dst: Register) (r1 r2: nat + Register)
| Sub (dst: Register) (r1 r2: nat + Register)
| Fail
| Halt.

(**

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

Inductive ConfFlag : Type :=
(** | Executable  Because code is not part of the memory, we don't need this flag *)
| Halted
| Failed
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

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

Definition exec_instr_opt (i: instr) (φ: ExecConf) : option Conf :=
    match i with
    | Fail => Some (Failed, φ)
    | Halt => Some (Halted, φ)
    | Jmp r =>
      wr ← (reg φ) !! r;
      Some (NextI, update_PC φ wr)
    | Jnz r1 r2 =>
      wr2 ← (reg φ) !! r2;
      wr1 ← (reg φ) !! r1;
      if nonZero wr2 then
        Some (NextI, update_PC φ wr1)
      else Some (NextI, incr_PC φ)
    | Load dst src =>
      wsrc ← (reg φ) !! src;
      asrc ← (mem φ) !! wsrc;
      Some (NextI, incr_PC (update_reg φ dst asrc))
    | Store dst ρ =>
        wdst ← (reg φ) !! dst;
        tostore ← word_from_argument φ ρ;
        Some (NextI, incr_PC (update_mem φ wdst tostore))
    | Mov dst ρ =>
        wdst ← (reg φ) !! dst;
        tomov ← word_from_argument φ ρ;
        Some (NextI, incr_PC (update_reg φ wdst tomov))
    | Add dst ρ1 ρ2 =>
        n1 ← word_from_argument φ ρ1;
        n2 ← word_from_argument φ ρ2;
        Some (NextI, incr_PC (update_reg φ dst (n1 + n2)))
    | Sub dst ρ1 ρ2 =>
        n1 ← word_from_argument φ ρ1;
        n2 ← word_from_argument φ ρ2;
        Some (NextI, incr_PC (update_reg φ dst (n1 - n2)))
    end.

Definition exec_instr (i: instr) (φ: ExecConf) : Conf :=
    match exec_instr_opt i φ with
    | None => (Failed, φ)
    | Some conf => conf
    end.

Lemma exec_instr_opt_exec_instr_some :
    forall φ i c,
      exec_instr_opt i φ = Some c →
      exec_instr i φ = c.
Proof. unfold exec_instr. by intros * ->. Qed.

Lemma exec_instr_opt_exec_instr_none :
    forall φ i,
      exec_instr_opt i φ = None →
      exec_instr i φ = (Failed, φ).
  Proof. unfold exec_instr. by intros * ->. Qed.


Definition emptyReg : Reg := empty.
Definition emptyMem : Mem := empty.

(** Contrary to Cerise programs are not part of the memory in this model *)
Definition program : Type := Word -> option instr.

Definition list_prog_to_prog (li : list instr) : program :=
    fun (w : Word) => nth_error li w.

Definition exec_step_prog (prog : program) (φ : ExecConf) : Conf :=
    match (prog (PC φ)) with
    | None => (Failed, φ)
    | Some i => exec_instr i φ
    end.

Inductive step_prog (prog : program) : Conf -> Conf -> Prop :=
    | step_PC_fail (φ : ExecConf) (PC_invalid : prog (PC φ) = None) :
        step_prog prog (NextI, φ) (Failed, φ)
    | step_PC_succ (φ : ExecConf) (i : instr) (PC_valid : prog (PC φ) = Some i) :
        step_prog prog (NextI, φ) (exec_instr i φ).

Fixpoint exec_prog (prog : program) (φ : ExecConf) (time : nat) : Conf :=
    match time with
    | 0 => (NextI, φ)
    | S time' => match (exec_step_prog prog φ) with
                 | (NextI, φ') => exec_prog prog φ' time'
                 | x => x
                 end
    end.

Lemma step_prog_deterministic (prog : program):
    forall c1 c2 c2' σ1 σ2 σ2',
      step_prog prog (c1, σ1) (c2, σ2) →
      step_prog prog (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inversion H1; inversion H2; auto; try congruence.
  Qed.

(**
Inductive Exec_prog_step_ind (prog : program) (φ : Conf) : Conf -> Prop :=
| ExecJmp (w : Word) (r : Register) (PC_is_jmp : prog (PC φ) = Some (Jmp r))
    (reg_is_valid : (reg φ) !! r = Some w) :
    Exec_prog_step_ind prog φ (update_PC φ w)
| ExecJnzNonZero (w1 w2 : Word) (r1 r2 : Register)
    (PC_is_jnz : prog (PC φ) = Some (Jnz r1 r2))
    (reg1_is_valid : (reg φ) !! r1 = Some w1)
    (reg2_is_valid : (reg φ) !! r2 = Some w2)
    (nz2 : nonZero w2 = true) :
    Exec_prog_step_ind prog φ (update_PC φ w1)
| ExecJnzZero (w1 w2 : Word) (r1 r2 : Register)
    (PC_is_jnz : prog (PC φ) = Some (Jnz r1 r2))
    (reg1_is_valid : (reg φ) !! r1 = Some w1)
    (reg2_is_valid : (reg φ) !! r2 = Some w2)
    (nz2 : nonZero w2 = false) :
    Exec_prog_step_ind prog φ (incr_PC φ)
| ExecLoad (wsrc asrc : Word) (rdst rsrc : Register)
    (PC_is_load : prog (PC φ) = Some (Load rdst rsrc))
    (regsrc_is_valid : (reg φ) !! rsrc = Some wsrc)
    (memwsrc_is_valid : (mem φ) !! wsrc = Some asrc) :
    Exec_prog_step_ind prog φ (incr_PC (update_reg φ rdst asrc))
| ExecStore (wdst wsrc : Word) (rdst : Register) (ρ : nat + Register)
    (PC_is_store : prog (PC φ) = Some (Store rdst ρ))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq_ρ : word_from_argument φ ρ = Some wsrc) :
    Exec_prog_step_ind prog φ (incr_PC (update_mem φ wdst wsrc))
| ExecMoveReg (wdst wsrc : Word) (rdst : Register) (ρ : nat + Register)
    (PC_is_mov : prog (PC φ) = Some (Mov rdst ρ))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq : word_from_argument φ ρ = Some wsrc) :
    Exec_prog_step_ind prog φ (incr_PC (update_reg φ wdst wsrc))
| ExecAdd (wdst w1 w2 : Word) (rdst : Register) (ρ1 ρ2 : nat + Register)
    (PC_is_add : prog (PC φ) = Some (Add rdst ρ1 ρ2))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq_ρ1 : word_from_argument φ ρ1 = Some w1)
    (eq_ρ2 : word_from_argument φ ρ2 = Some w2) :
    Exec_prog_step_ind prog φ (incr_PC (update_reg φ rdst (w1 + w2)))
| ExecSub (wdst w1 w2 : Word) (rdst : Register) (ρ1 ρ2 : nat + Register)
    (PC_is_sub : prog (PC φ) = Some (Sub rdst ρ1 ρ2))
    (regdst_is_valid : (reg φ) !! rdst = Some wdst)
    (eq_ρ1 : word_from_argument φ ρ1 = Some w1)
    (eq_ρ2 : word_from_argument φ ρ2 = Some w2) :
    Exec_prog_step_ind prog φ (incr_PC (update_reg φ rdst (w1 - w2)))
.
*)

Definition steps_prog (prog : program) : relation Conf :=
    rtc (step_prog prog).

Definition n_steps_prog (prog : program) : nat -> relation Conf :=
    nsteps (step_prog prog).

Lemma testExec_Prog : step_prog (list_prog_to_prog [Add 0 (inl 1) (inr 0)]) (NextI, (0, <[0:=0]>(emptyReg), emptyMem)) (NextI, (1, <[0:=1]>(emptyReg), emptyMem)).
Proof.
    assert (exec_instr (Add 0 (inl 1) (inr 0)) (0, <[0:=0]> emptyReg,
emptyMem)  = (NextI, (1, <[0:=1]>(emptyReg), emptyMem))) as H.
    { reflexivity. }
    rewrite -H.
    apply step_PC_succ.
    reflexivity.
Qed.

(**
Lemma soundness_exec_step (prog : program) (φ φ' : ExecConf) :
    Exec_prog_step_ind prog φ φ' -> exec_prog prog φ 1 = φ'.
    (** The other direction doesn't hold because invalid operation do nothing (configuration stays the same) in exec_prog while in Exec_prog_step_ind there is no evaluation step. *)
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



Lemma soundness_exec_step (prog : program) (φ : ExecConf) :
    step_prog prog (NextI, φ) (exec_prog prog φ 1).
Proof.
    unfold exec_prog. unfold exec_step_prog.
    destruct (prog (PC φ)) as [] eqn:HPC.
    - (** A lot of work to demonstrate that something is actually an identity function *)
      destruct (exec_instr i φ) as [] eqn:Hexec.
      destruct c; rewrite -Hexec; constructor; assumption.
    - constructor. assumption.
Qed.

Lemma exec_step_prog_exec_prog_n_is_exec_prog_Sn (time : nat) (prog : program) (φ : ExecConf) :
        exec_prog prog φ (S time) =
        match exec_step_prog prog φ with
                    | (NextI, φ') => exec_prog prog φ' time
                    | x => x
                    end.
Proof.
    simpl. destruct (exec_step_prog prog φ) as [] eqn:Hexec.
      destruct c; reflexivity.
Qed. 

Lemma sum_time_exec_prog (time1 time2 : nat) (prog : program) (φ : ExecConf) :
    match exec_prog prog φ time1 with
                    | (NextI, φ') => exec_prog prog φ' time2
                    | x => x
                    end
        = exec_prog prog φ (time1 + time2).
Proof.
    revert φ.
    induction time1.
    - reflexivity.
    - simpl. intro φ. destruct (exec_step_prog prog φ) as [] eqn:Hexec.
      destruct c; auto.
Qed. 


Lemma soundness_exec_n_steps (prog : program) (m : nat) (φ : ExecConf) :
    exists n, n <= m -> n_steps_prog prog n (NextI, φ) (exec_prog prog φ m).
Proof.
    revert φ.
    induction m; intros φ.
    - exists 0. constructor.
    - simpl. destruct (exec_step_prog prog φ) as [] eqn:Hexec. specialize (IHm e) as [n H].
      destruct c; eexists; intro ineq; econstructor; try apply soundness_exec_step.
      + simpl. rewrite Hexec. constructor.
      + simpl. rewrite Hexec. constructor.
      + simpl. rewrite Hexec.
        apply le_S_n in ineq. apply H. assumption.
Qed.

    

    