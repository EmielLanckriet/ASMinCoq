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

Definition Addr := nat.

Locate vec.

(** Different constructor for instructions that only mention the general categories in which instructions are introduced in Waterman's thesis *)
Inductive instr : Type :=
(** Computational and control flow instructions can get their inputs from registers are words (called immediates) *)
| Computation {n : nat} (inputs : vec (Word + Register) n)
    (rres : Register) (f_result : vec Word n -> Word)
| ControlFlow {n : nat} (inputs : vec (Word + Register) n)
    (dst : Word + Register) (f_condition : vec Word n -> bool)
| Load (rdst rsrc: Register)
| Store (rdst : Register) (src : Word + Register)
| Halt.


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

(** Memory and registers are gmaps which are partials maps, but because we don't want failure when something has not been initialized, we always use (!!!) which gives 0 as a default value. *)
Definition Reg := gmap Register Word.
Definition Mem := gmap Addr Word.

Definition ExecConf := (Word * Reg * Mem)%type.

Inductive ConfFlag : Type :=
(** | Executable  Because code is not part of the memory, we don't need this flag *)
| Halted
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

Definition wordreg_to_word (rs : Reg) (input : Word + Register) : Word :=
    match input with
    | inl word => word
    | inr reg => rs !!! reg
    end.
    
Definition addrreg_to_addr (rs : Reg) (input : Addr + Register) : Addr :=
    match input with
    | inl addr => addr
    | inr reg => rs !!! reg
    end.

Definition inputs_from_inputnatregs {n : nat} (rs : Reg) (inputs : vec (Word + Register) n) := vmap (wordreg_to_word (rs : Reg)) inputs.
    

Definition exec_instr (i : instr) (φ : ExecConf) : Conf :=
    match i with
    | Halt => (Halted, φ)
    | Computation inputs rres f_result =>
        (NextI, incr_PC (
                update_reg φ rres (
                    f_result (inputs_from_inputnatregs (reg φ) inputs))))
    | ControlFlow inputs dst f_condition =>
        match (f_condition (inputs_from_inputnatregs (reg φ) inputs)) with
        | true => (NextI, update_PC φ (wordreg_to_word (reg φ) dst))
        | false => (NextI, incr_PC φ)
        end
    | Load rres rsrc =>
        let wsrc := (reg φ) !!! rsrc in
        let asrc := (mem φ) !!! wsrc in
        (NextI, incr_PC (update_reg φ rres asrc))
    | Store rdst src =>
        let wsrc := wordreg_to_word (reg φ) src in
        let wdst := (reg φ) !!! rdst in
        (NextI, incr_PC (update_mem φ wdst wsrc))
    end.


Definition emptyReg : Reg := empty.
Definition emptyMem : Mem := empty.

(** Contrary to Cerise programs are not part of the memory in this model *)
Definition program : Type := Word -> instr.

Definition list_prog_to_prog (li : list instr) : program :=
    fun (w : Word) => nth_default Halt li w.

Definition exec_step_prog (prog : program) (φ : ExecConf) : Conf :=
    let i := prog (PC φ) in exec_instr i φ.


Inductive step_prog (prog : program) : Conf -> Conf -> Prop :=
    | step_PC_i (φ : ExecConf) :
        step_prog prog (NextI, φ) (exec_instr (prog (PC φ)) φ).

Lemma estep_PC_i (prog : program) (φ : ExecConf) (c : Conf) (i : instr) (PC_i : prog (PC φ) = i) :
    c = exec_instr i φ -> step_prog prog (NextI, φ) c.
Proof.
    intros. subst. econstructor.
Qed.


Lemma step_prog_deterministic (prog : program):
    forall c1 c2 c2' σ1 σ2 σ2',
      step_prog prog (c1, σ1) (c2, σ2) →
      step_prog prog (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inversion H1; inversion H2; auto; try congruence.
  Qed.

Definition steps_prog (prog : program) : relation Conf :=
    rtc (step_prog prog).

Definition n_steps_prog (prog : program) : nat -> relation Conf :=
    nsteps (step_prog prog).

Inductive NilView : vec Word 0 -> Set :=
  nilView : NilView [#].

Inductive ConsView {n : nat} : (vec Word (S n)) -> Set :=
  consView : forall (w : Word) (v : vec Word n), ConsView (w ::: v).

Definition view {n : nat} (v : vec Word n) :
  match n with 
  | 0 => NilView
  | S n => @ConsView n
  end v := match v with
   | [#] => nilView
   | (v ::: vs) => consView v vs
end.

Definition binaryOn2Vec {B : Type} (f_bin : Word -> Word -> B) (v : vec Word 2) : B :=
    match view v with
    | consView w1 v' => 
      match view v' with
      | consView w2 v'' =>
        match view v'' with
        | nilView => f_bin w1 w2
        end
      end
    end.
    
Definition add_vec_2 := binaryOn2Vec (fun x y => x + y).
    

Definition Add (dst: Register) (r1 r2: Word + Register) : instr :=
    Computation [# r1; r2] dst add_vec_2.

Lemma testExec_Prog : step_prog (list_prog_to_prog [Add 0 (inl 1) (inr 0)]) (NextI, (0, <[0:=0]>(emptyReg), emptyMem)) (NextI, (1, <[0:=1]>(emptyReg), emptyMem)).
Proof.
    eapply estep_PC_i.
    { reflexivity. }
    reflexivity.
Qed.

(** Fixpoint exec_prog_output_time (prog : program) (φ : ExecConf) (time : nat) : Conf * {rest : nat | rest <= time}.
    refine (
        match time with
        | 0 => ((NextI, φ) , exist _ 0 _)
        | S time' => match (exec_step_prog prog φ) with
                    | (NextI, φ') => let (x, rest') := exec_prog_output_time prog φ' time' in (x, exist _ (proj1_sig rest') _)
                    | x => (x, exist _ time' _)
                    end
        end
    ); try lia.
    destruct rest'. simpl. apply Nat.le_le_succ_r. exact l.
Defined.


Definition exec_prog (prog : program) (φ : ExecConf) (time : nat) : Conf  :=
    fst (exec_prog_output_time prog φ time).
    *)

Fixpoint exec_prog (prog : program) (φ : ExecConf) (time : nat) : Conf :=
    match time with
        | 0 => (NextI, φ)
        | S time' => match (exec_step_prog prog φ) with
                    | (NextI, φ') => exec_prog prog φ' time'
                    | x => x
                    end
    end.  


Lemma soundness_exec_step (prog : program) (φ : ExecConf) :
    step_prog prog (NextI, φ) (exec_prog prog φ 1).
Proof.
    eapply estep_PC_i.
    { reflexivity. }
    unfold exec_prog. simpl. unfold exec_step_prog.
    destruct (prog (PC φ)) as [] eqn:HPC; try reflexivity.
    simpl.
    destruct (f_condition (inputs_from_inputnatregs (reg φ) inputs)); reflexivity.
Qed.

Lemma soundness_exec (prog : program) (φ : ExecConf) :
    forall time c, c = exec_prog prog φ time ->
    steps_prog prog (NextI, φ) c.
Proof.
    intro time.
    revert φ.    
    induction time; intros φ.
    - simpl. intros. subst. constructor.
    - simpl. destruct (exec_step_prog prog φ) as [] eqn:Hexec. intros.
      destruct c.
      + subst.
        econstructor.
        * constructor.
        * rewrite -Hexec. unfold exec_step_prog. constructor.
      + subst.
        econstructor.
        * constructor.
        * unfold exec_step_prog in Hexec. rewrite Hexec. apply IHtime. reflexivity.
Qed.

    

    