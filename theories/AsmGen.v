From Coq Require Import Eqdep_dec. (* Needed to prove decidable equality on Register *)
From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_maps relations vector.
From ASMinCoq Require Import CpdtTactics.
From iris.program_logic Require Import language ectx_language ectxi_language.

Inductive Register :=
  | register (n : nat) : Register.

Global Instance reg_eq_dec : EqDecision Register.
Proof. intros r1 r2.
       destruct r1 as [n1]; destruct r2 as [n2].
       destruct (Nat.eq_dec n1 n2).
       + subst. left. reflexivity.
       + right. congruence.
Defined.

Global Instance reg_countable : Countable Register.
Proof.
    refine {| encode r := encode (match r with
                               | register n => n
                               end );
            decode n := match (decode n) with
                        | Some n => Some (register n)
                        | _ => None
                        end ;
            decode_encode := _ |}.
    intro r. destruct r; auto.
    rewrite decode_encode.
    reflexivity.
Defined.

Inductive Word :=
  | word (n : nat) : Word.

#[export] Instance inhabited_word : Inhabited Word.
Proof.
  constructor.
  exact (word 0).
Qed.

Definition word_to_nat (w : Word) : nat :=
  match w with word n => n end.

Inductive Addr :=
  | addr (n : nat) : Addr.

Definition word_to_addr (w : Word) : Addr :=
  match w with
    | word n => addr n
  end.

Global Instance word_eq_dec : EqDecision Word.
Proof. intros w1 w2.
       destruct w1 as [n1]; destruct w2 as [n2].
       destruct (Nat.eq_dec n1 n2).
       + subst. left. reflexivity.
       + right. congruence.
Defined.

Global Instance word_countable : Countable Word.
Proof.
    refine {| encode r := encode (match r with
                               | word n => n
                               end );
            decode n := match (decode n) with
                        | Some n => Some (word n)
                        | _ => None
                        end ;
            decode_encode := _ |}.
    intro r. destruct r; auto.
    rewrite decode_encode.
    reflexivity.
Defined.

Global Instance addr_eq_dec : EqDecision Addr.
Proof. intros a1 a2.
       destruct a1 as [n1]; destruct a2 as [n2].
       destruct (Nat.eq_dec n1 n2).
       + subst. left. reflexivity.
       + right. congruence.
Defined.

Global Instance addr_countable : Countable Addr.
Proof.
    refine {| encode r := encode (match r with
                               | addr n => n
                               end );
            decode n := match (decode n) with
                        | Some n => Some (addr n)
                        | _ => None
                        end ;
            decode_encode := _ |}.
    intro r. destruct r; auto.
    rewrite decode_encode.
    reflexivity.
Defined.


(** Memory and registers are gmaps which are partials maps, but because we don't want failure when something has not been initialized, we always use (!!!) which gives 0 as a default value. *)
Definition Reg := gmap Register Word.

#[export] Instance lookup_total_register : LookupTotal Register Word Reg.
Proof.
  eapply map_lookup_total.  
Defined.

Definition Mem := gmap Addr Word.

#[export] Instance lookup_total_memory : LookupTotal Addr Word Mem.
Proof.
  eapply map_lookup_total.  
Defined.

Definition ExecConf := (Word * Reg * Mem)%type.

Inductive ConfFlag : Type :=
(** | Executable  Because code is not part of the memory, we don't need this flag *)
| Halted
| NextI
| Executable.

(* Definition Conf: Type := ConfFlag * ExecConf. *)

Definition reg (ϕ : ExecConf) := snd (fst ϕ).

Definition mem (ϕ : ExecConf) := snd ϕ.

Definition PC (φ : ExecConf) := fst (fst φ).


Definition update_reg (φ : ExecConf) (r : Register) (w : Word): ExecConf :=
    (PC φ,<[r:=w]>(reg φ),mem φ).
Definition update_mem (φ : ExecConf) (a : Addr) (w : Word): ExecConf :=
    (PC φ,reg φ, <[a:=w]>(mem φ)).
Definition update_PC (φ : ExecConf) (w : Word) : ExecConf :=
    (w, reg φ, mem φ).

Definition incr_word (w : Word) : Word :=
  match w with word n => word (n + 1) end.

Definition incr_PC (φ : ExecConf) : ExecConf :=
    update_PC φ (incr_word (PC φ)).

(* Some easy lemmas to easily let these things commute and stuff *)

Lemma PC_is_updated_value (φ : ExecConf) (pc : Word) : PC (update_PC φ pc) = pc.
Proof. reflexivity. Qed.

Lemma PC_is_incr (φ : ExecConf) : PC (incr_PC φ) = incr_word (PC φ).
Proof. reflexivity. Qed.

Lemma reg_is_updated_value (φ : ExecConf) (r : Register) (w : Word) :
    reg (update_reg φ r w) = <[r:=w]>(reg φ).
Proof. reflexivity. Qed.

Lemma mem_is_updated_value (φ : ExecConf) (a : Addr) (w : Word) :
    mem (update_mem φ a w) = <[a:=w]>(mem φ).
Proof. reflexivity. Qed.

Lemma update_reg_no_change_pc (φ : ExecConf) (r : Register) (w : Word) :
    PC φ = PC (update_reg φ r w).
Proof. reflexivity. Qed.

Lemma update_reg_no_change_mem (φ : ExecConf) (r : Register) (w : Word) :
    mem φ = mem (update_reg φ r w).
Proof. reflexivity. Qed.

Lemma update_pc_no_change_reg (φ : ExecConf) (w : Word) :
    reg φ = reg (update_PC φ w).
Proof. reflexivity. Qed.

Lemma update_pc_no_change_mem (φ : ExecConf) (w : Word) :
    mem φ = mem (update_PC φ w).
Proof. reflexivity. Qed.

Lemma update_mem_no_change_pc (φ : ExecConf) (a : Addr) (w : Word) :
    PC φ = PC (update_mem φ a w).
Proof. reflexivity. Qed.

Lemma update_mem_no_change_reg (φ : ExecConf) (a : Addr) (w : Word) :
    reg φ = reg (update_mem φ a w).
Proof. reflexivity. Qed.

Definition nonZero (w: Word): bool :=
  match w with
    | word n => negb (Nat.eqb n 0)
  end.
    
Definition zero  (w: Word): bool :=
  match w with
  | word n => Nat.eqb n 0
  end.

Definition word_from_argument (φ : ExecConf) (src : Word + Register) : Word :=
    match src with
    | inl w => w
    | inr r => (reg φ) !!! r
    end.

Definition wordreg_to_word (rs : Reg) (input : Word + Register) : Word :=
    match input with
    | inl w => w
    | inr reg => rs !!! reg
    end.
    
Definition addrreg_to_addr (rs : Reg) (input : Addr + Register) : Addr :=
    match input with
    | inl a => a
    | inr reg => (word_to_addr (rs !!! reg))
    end.

Inductive leak : Type :=
| NoLeak
| ControlFlowLeak (b : bool)
| LoadLeak (a : Addr)
| StoreLeak (a : Addr).

Hint Constructors leak : core.

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

Hint Constructors instr : core.

Definition inputs_from_inputnatregs {n : nat} (rs : Reg) (inputs : vec (Word + Register) n) :=
    vmap (wordreg_to_word (rs : Reg)) inputs.
    
Definition confflag_instr (i : instr) (φ : ExecConf) : ConfFlag :=
    match i with
    | Halt => Halted
    | _ => NextI
    end.

Definition exec_instr (i : instr) (φ : ExecConf) : ExecConf :=
    match i with
    | Halt => φ
    | Computation inputs rres f_result =>
        incr_PC (
                update_reg φ rres (
                    f_result (inputs_from_inputnatregs (reg φ) inputs)))
    | ControlFlow inputs dst f_condition =>
        match (f_condition (inputs_from_inputnatregs (reg φ) inputs)) with
        | true => update_PC φ (wordreg_to_word (reg φ) dst)
        | false => incr_PC φ
        end
    | Load rres rsrc => 
        let wsrc := (reg φ) !!! rsrc in
        let asrc := word_to_addr wsrc in
        let res := (mem φ) !!! asrc in
        incr_PC (update_reg φ rres res)
    | Store rdst src =>
        let wsrc := wordreg_to_word (reg φ) src in
        let wdst := (reg φ) !!! rdst in
        let adst := word_to_addr wdst in
        incr_PC (update_mem φ adst wsrc)
    end.

Definition leak_instr (i : instr) (φ : ExecConf) : leak :=
    match i with
    | Halt => NoLeak
    | Computation inputs rres f_result => NoLeak
    | ControlFlow inputs dst f_condition =>
        ControlFlowLeak (f_condition (inputs_from_inputnatregs (reg φ) inputs))
    | Load rres rsrc =>
        let wsrc := (reg φ) !!! rsrc in
        let asrc := word_to_addr wsrc in
        LoadLeak asrc
    | Store rdst src =>
        let asrc := (word_to_addr (wordreg_to_word (reg φ) src)) in StoreLeak asrc
    end.


Definition emptyReg : Reg := empty.
Definition emptyMem : Mem := empty.

(** Contrary to Cerise, programs are not part of the memory in this model *)
Definition program : Type := Word -> instr.

Definition state : Type := program * ExecConf.
Print nth_default.
Definition list_prog_to_prog (li : list instr) : program :=
    fun (w : Word) => nth_default Halt li (word_to_nat w).



Inductive step_prog : ConfFlag -> state * list leak -> ConfFlag -> state * list leak -> Prop :=
    | step_PC_i (prog : program) (φ : ExecConf) (ll : list leak) :
        step_prog Executable (prog, φ, ll) (confflag_instr (prog (PC φ)) φ) (prog, exec_instr (prog (PC φ)) φ, leak_instr (prog (PC φ)) φ :: ll).

Hint Constructors step_prog : core.

Lemma estep_PC_i (prog : program) (φ φ' : ExecConf) (ll ll' : list leak) (c' : ConfFlag) (i : instr) (PC_i : prog (PC φ) = i) (result : state * list leak) :
    c' = confflag_instr i φ ->
    φ' = exec_instr i φ  ->
    ll' = leak_instr i φ :: ll ->
    result = (prog, φ', ll') ->
    step_prog Executable (prog, φ, ll) c' result.
Proof.
    intros. subst. econstructor.
Qed.


Lemma step_prog_deterministic (prog : program):
    forall f1 f1' f2 f2' c1 c2 c2' σ1 σ2 σ2',
      step_prog f1 (c1, σ1) f2 (c2, σ2) →
      step_prog f1' (c1, σ1) f2' (c2', σ2') →
      f2 = f2' ∧ c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; try split; inversion H1; inversion H2; auto; try congruence.
  Qed.

(*
Definition steps_prog : relation (ConfFlag * state * list leak) :=
    rtc step_prog.

Definition n_steps_prog (prog : program) : nat -> relation  (Conf * list leak) :=
    nsteps (step_prog prog).
*)

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

Definition unaryOn1Vec {B : Type} (f_un : Word -> B) (v : vec Word 1) : B :=
    match view v with
    | consView w v' => 
      match view v' with
      | nilView => f_un w
      end
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
    
Definition add_vec_2 := binaryOn2Vec (fun x y => word (word_to_nat x + word_to_nat y)).
    

Definition Add (dst: Register) (r1 r2: Word + Register) : instr :=
    Computation [# r1; r2] dst add_vec_2.

Lemma testExec_Prog : step_prog Executable (list_prog_to_prog [Add (register 0) (inl (word 1)) (inr (register 0))], (word 0, <[register 0:=word 0]>(emptyReg), emptyMem), []) NextI (list_prog_to_prog [Add (register 0) (inl (word 1)) (inr (register 0))], (word 1, <[register 0:= word 1]>(emptyReg), emptyMem), [NoLeak]).
Proof.
    eapply estep_PC_i; try reflexivity.
Qed.

(*
Fixpoint exec_prog_ll (prog : program) (φ : ExecConf) (ll : list leak) (time : nat) : Conf * list leak :=
    match time with
        | 0 => (NextI, φ, ll)
        | S time' => match (exec_step_prog prog φ) with
                    | (NextI, φ', l) => exec_prog_ll prog φ' (l :: ll) time'
                    | (x, l) => (x, l :: ll)
                    end
    end.

Definition exec_prog (prog : program) (φ : ExecConf) (time : nat) : Conf * list leak :=
    exec_prog_ll prog φ [] time.


Lemma soundness_exec_step (prog : program) (φ : ExecConf) (ll : list leak) :
    step_prog prog (NextI, φ, []) (exec_prog prog φ 1).
Proof.
    eapply estep_PC_i; try reflexivity.
    unfold exec_prog. unfold exec_prog_ll. simpl.
    destruct (prog (PC φ)) as [] eqn:HPC; try reflexivity.
    simpl.
    destruct (f_condition (inputs_from_inputnatregs (reg φ) inputs)); reflexivity.
Qed.

Lemma soundness_exec_ll (prog : program) (φ : ExecConf) (ll : list leak) :
    forall time c, c = exec_prog_ll prog φ ll time ->
    steps_prog prog (NextI, φ, ll) c.
Proof.
    intro time.
    revert φ ll.    
    induction time; intros φ.
    - simpl. intros. subst. constructor.
    - simpl. destruct (exec_step_prog prog φ) as [] eqn:Hexec. intros.
      destruct c. destruct c.
      + subst.
        econstructor.
        * constructor.
        * unfold exec_step_prog in *. unfold exec_prog. simpl. injection Hexec as H0 H1. rewrite H0. rewrite H1. constructor.
      + subst.
        econstructor.
        * constructor.
        * unfold exec_step_prog in Hexec. unfold exec_prog. simpl. injection Hexec as H0 H1. rewrite H0. rewrite H1. apply IHtime. reflexivity.
Qed.

Lemma soundness_exec (prog : program) (φ : ExecConf) :
    forall time c, c = exec_prog prog φ time ->
    steps_prog prog (NextI, φ, []) c.
Proof.
    unfold exec_prog. apply soundness_exec_ll.
Qed.
*)

Definition notzero_vec_1 := unaryOn1Vec (fun w => nonZero w).
    
Definition Jnz (cond dst : Word + Register) : instr :=
    ControlFlow [# cond] dst notzero_vec_1.

Lemma test_constant_time_cond_true :
    step_prog Executable
    (list_prog_to_prog [Jnz (inr (register 0)) (inl (word 2)); Load (register 0) (register 0)],
    (word 0, <[register 0:= word 1]>(emptyReg), emptyMem),
    [])
    NextI
    (list_prog_to_prog [Jnz (inr (register 0)) (inl (word 2)); Load (register 0) (register 0)],
    (word 2, <[register 0:= word 1]>(emptyReg), emptyMem),
    [ControlFlowLeak true]).
Proof.
    eapply estep_PC_i; try reflexivity.
Qed.
    
Lemma test_constant_time_cond_false :
    step_prog Executable
    (list_prog_to_prog [Jnz (inr (register 0)) (inl (word 2)); Load (register 0) (register 0)],
    (word 0, <[register 0:= word 0]>(emptyReg), emptyMem),
    [])
    NextI
    (list_prog_to_prog [Jnz (inr (register 0)) (inl (word 2)); Load (register 0) (register 0)],
    (word 1, <[register 0:= word 0]>(emptyReg), emptyMem),
    [ControlFlowLeak false]).
Proof.
    eapply estep_PC_i; try reflexivity.
Qed.

(*
Definition halts_with (prog : program) (φ : ExecConf) (ll : list leak) :=
    steps_prog prog (NextI, (0, emptyReg, emptyMem), []) (Halted, φ, ll).


Definition non_interferent (prog : nat -> program) :=
    forall (n m : nat), ∃ φ1 φ2 ll, halts_with (prog n) φ1 ll ∧ halts_with (prog m) φ2 ll.

Definition test_prog_constant_time (high_input : nat) :=
    list_prog_to_prog [Add 0 (inl high_input) (inl high_input)].

Hint Resolve estep_PC_i : core.
Hint Constructors rtc : core.

Lemma test_prog_constant_time_non_interferent : non_interferent test_prog_constant_time.
Proof.
    intros n m.
    eexists. eexists. eexists.
    split.
    - econstructor.
        + eapply estep_PC_i; try reflexivity.
        + econstructor; try apply rtc_refl. simpl. eapply estep_PC_i; try reflexivity.
    - econstructor.
        + eapply estep_PC_i; try reflexivity.
        + econstructor; try apply rtc_refl. simpl. eapply estep_PC_i; try reflexivity.
Qed.

Definition test_prog_not_constant_time (high_input : nat) :=
    list_prog_to_prog [Add 0 (inl high_input) (inl high_input); Jnz (inr 0) (inl 2)].

Lemma test_prog_not_constant_time_not_non_interferent : ¬ non_interferent test_prog_not_constant_time.
Proof.
    intro contra.
    specialize (contra 0 1) as (φ1 & φ2 & ll & [Hinput0 Hinput1]).
    (** Hypothesis with input 0 is inverted until we reach halt and hence can find the leakage trace *)
    inversion Hinput0; subst; clear Hinput0.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H. simpl in H1.
    assert (reg (incr_PC (update_reg (0, emptyReg, emptyMem) 0 (add_vec_2 [#0; 0]))) !!! 0 = 0) as Hrew. { reflexivity. }
    rewrite Hrew in H1. clear Hrew.
    assert (notzero_vec_1 [#0] = false) as Hrew. { reflexivity. }
    rewrite Hrew in H1. clear Hrew.
    inversion H1; subst; clear H1.
    inversion H; subst; clear H.
    simpl in H0.
    inversion H0; subst; clear H0.
    2: inversion H.
    (** Now, we invert hypothesis with input 1 until we find that the wrong leakage trace is assumed. *)
    inversion Hinput1; subst; clear Hinput1.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H. simpl in H1.
    assert (reg (incr_PC (update_reg (0, emptyReg, emptyMem) 0 (add_vec_2 [#1; 1]))) !!! 0 = 2) as Hrew. { reflexivity. }
    rewrite Hrew in H1. clear Hrew.
    assert (notzero_vec_1 [#2] = true) as Hrew. { reflexivity. }
    rewrite Hrew in H1. clear Hrew.
    inversion H1; subst; clear H1.
    inversion H; subst; clear H.
    simpl in H0.
    unfold add_vec_2 in H0. unfold binaryOn2Vec in H0. simpl in H0.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
Qed.
*)

Inductive val : Type :=
  | HaltedV : val
  | NextIV : val
  | LoopHaltedV : val.

Hint Constructors val : core.

Inductive expr : Type :=
  | Instr (c : ConfFlag)
  | Loop (c : ConfFlag).

Hint Constructors expr : core.

Definition of_val (v : val) : expr :=
    match v with
    | HaltedV => Instr Halted
    | NextIV => Instr NextI
    | LoopHaltedV => Loop Halted
    end.

Definition to_val (e : expr): option val :=
    match e with
        | Instr f => match f with
                    | Halted => Some HaltedV
                    | NextI => Some NextIV
                    | Executable => None
                    end
      | Loop cf => match cf with
                   | Halted => Some LoopHaltedV
                   | _ => None
                   end
    end.

Lemma of_to_val:
    forall e v, to_val e = Some v →
           of_val v = e.
Proof.
    intros * HH. destruct e; try destruct c; simpl in HH; inversion HH; auto.
Qed.

Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
Proof. destruct v; reflexivity. Qed.

Inductive prim_step : expr → state * list leak → list Empty_set → expr → state * list leak → list expr → Prop :=
| PS_no_fork_instr σ cf σ' :
        step_prog Executable σ cf σ' -> prim_step (Instr Executable) σ [] (Instr cf) σ' []
| PS_no_fork_loop_ex σ cf σ' :
        step_prog Executable σ cf σ' -> prim_step (Loop Executable) σ [] (Loop cf) σ' []
| PS_no_fork_loop σ : prim_step (Loop NextI) σ [] (Loop  Executable) σ [].

Hint Constructors prim_step : core.

Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs →
      to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

Lemma asm_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
    constructor;
    apply _ || eauto using to_of_val, of_to_val, val_stuck.
Qed.

Canonical Structure asm_lang := Language asm_lang_mixin. 

Lemma normal_always_step:
    forall sll, exists cf sll', step_prog Executable sll cf sll'.
  Proof.
    destruct sll as [[prog φ] ll].
    intros. destruct (prog (PC φ)) as [] eqn:H.
    (* Resolve the Halt case *)
    all: try solve [exists Halted; eexists; eapply estep_PC_i; auto; rewrite H; auto].
    all: try (exists NextI; eexists; eapply estep_PC_i; auto; rewrite H; reflexivity).
  Qed.


Lemma reducible_from_step_prog σ1 f2 σ2 :
  step_prog Executable σ1 f2 σ2 →
  reducible (Instr Executable) σ1.
Proof. intros * HH. rewrite /reducible //=.
       eexists [], (Instr _), σ2, []. by constructor.
Qed.

Lemma normal_always_reducible σ :
  reducible (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply reducible_from_step_prog. eauto.
Qed.

Lemma loop_next_always_reducible σ :
  reducible (Loop NextI) σ.
Proof. rewrite /reducible //=.
       eexists [], _, σ, []. by constructor.
Qed.




(* Binary language for binary program logic *)

Definition val2 : Type := (val * val)%type.

Definition expr2 : Type := (expr * expr)%type.

Definition of_val2 (v : val2) : expr2 :=
    match v with
        (v1, v2) => (of_val v1, of_val v2)
    end.

Definition to_val2 (e : expr2): option val2 :=
    match e with
        (e1, e2) => e1' ← to_val e1; e2' ← to_val e2; Some (e1', e2')
    end.

Lemma of_to_val2:
    forall e v, to_val2 e = Some v →
           of_val2 v = e.
Proof.
    intros * HH. destruct e; destruct e; destruct e0; try destruct c; try destruct c0; simpl in HH; inversion HH; auto.
Qed.

Lemma to_of_val2:
    forall v, to_val2 (of_val2 v) = Some v.
Proof. destruct v; destruct v; destruct v0; reflexivity. Qed.

Inductive prim_step2 : expr2 → (state * list leak) * (state * list leak)
    → list Empty_set → expr2 → (state * list leak) * (state * list leak)
    → list expr2 → Prop :=
| PS_lockstep e1 e2 σ1 σ2 e1' e2' σ1' σ2' : prim_step e1 σ1 [] e1' σ1' [] ->
        prim_step e2 σ2 [] e2' σ2' [] ->
        prim_step2 (e1, e2) (σ1, σ2) [] (e1', e2') (σ1', σ2') [].


Hint Constructors prim_step2 : core.

Lemma val_stuck2:
    forall e σ o e' σ' efs,
      prim_step2 e σ o e' σ' efs →
      to_val2 e = None.
Proof. intros * HH. inversion HH; subst; inversion H; subst; try reflexivity. 
        all: destruct e1; destruct c; reflexivity.
Qed.

Lemma asm_lang_mixin2 : LanguageMixin of_val2 to_val2 prim_step2.
Proof.
    constructor;
    apply _ || eauto using to_of_val2, of_to_val2, val_stuck2.
Qed.

Canonical Structure asm_lang2 := Language asm_lang_mixin2.
