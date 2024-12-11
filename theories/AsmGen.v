From Coq Require Import Eqdep_dec.
(* Needed to prove decidable equality on Register *)
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
| HaltLeak
| ComputationLeak {n : nat} (f_result : vec Word n -> Word)
| ControlFlowLeak (next_pcs : list Word)
| LoadLeak (a : Addr)
| StoreLeak (a : Addr).

Hint Constructors leak : core.

(** Different constructor for instructions that only mention the general categories in which instructions are introduced in Waterman's thesis *)
Inductive instr : Type :=
(** Computational and control flow instructions can get their inputs from registers are words (called immediates) *)
| Computation {n : nat} (inputs : vec (Word + Register) n)
    (rres : Register) (f_result : vec Word n -> Word)
| ControlFlow {n : nat} (secret : bool) (inputs : vec (Word + Register) n)
    (dst : Word) (f_condition : vec Word n -> bool) (leakage : list Word)
| Jmp (secret : bool) (dst : Word) (leakage : list Word)
| Load (rdst rsrc: Register)
| Store (rdst : Register) (src : Word + Register)
| MimicLeak (i : instr)
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
    | ControlFlow secret inputs dst f_condition leakage =>
        match (f_condition (inputs_from_inputnatregs (reg φ) inputs)) with
        | true => update_PC φ dst
        | false => incr_PC φ
        end
    | Jmp _ dst _ => update_PC φ dst
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
    | MimicLeak i => φ
    end. 

Fixpoint leak_instr (i : instr) (φ : ExecConf) : leak :=
    match i with
    | Halt => HaltLeak
    | Computation inputs rres f_result => ComputationLeak f_result
    | ControlFlow secret inputs dst f_condition leakage =>
        match secret with
        | false => ControlFlowLeak ([if f_condition (inputs_from_inputnatregs (reg φ) inputs)
                         then dst
                         else PC (incr_PC φ)])
        | true => ControlFlowLeak leakage
        end
    | Jmp secret dst leakage => match secret with
                        | false => ControlFlowLeak [dst]
                        | true => ControlFlowLeak leakage
                        end
    | Load rres rsrc =>
        let wsrc := (reg φ) !!! rsrc in
        let asrc := word_to_addr wsrc in
        LoadLeak asrc
    | Store rdst src =>
        let asrc := (word_to_addr (wordreg_to_word (reg φ) src)) in StoreLeak asrc
    | MimicLeak i => leak_instr i φ
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

Definition AddLeak := ComputationLeak add_vec_2.

Lemma testExec_Prog : step_prog Executable (list_prog_to_prog [Add (register 0) (inl (word 1)) (inr (register 0))], (word 0, <[register 0:=word 0]>(emptyReg), emptyMem), []) NextI (list_prog_to_prog [Add (register 0) (inl (word 1)) (inr (register 0))], (word 1, <[register 0:= word 1]>(emptyReg), emptyMem), [AddLeak]).
Proof.
    eapply estep_PC_i; try reflexivity.
Qed.


Definition notzero_vec_1 := unaryOn1Vec (fun w => nonZero w).
    
Definition Jnz (cond : Word + Register) (dst : Word) : instr :=
    ControlFlow false [# cond] dst notzero_vec_1 [].

Definition JnzSecret (cond : Word + Register) (dst : Word) leakage : instr :=
  ControlFlow true [# cond] dst notzero_vec_1 leakage.

Lemma test_constant_time_cond_true :
    step_prog Executable
    (list_prog_to_prog [Jnz (inr (register 0)) (word 2); Load (register 0) (register 0)],
    (word 0, <[register 0:= word 1]>(emptyReg), emptyMem),
    [])
    NextI
    (list_prog_to_prog [Jnz (inr (register 0)) (word 2); Load (register 0) (register 0)],
    (word 2, <[register 0:= word 1]>(emptyReg), emptyMem),
    [ControlFlowLeak [word 2]]).
Proof.
    eapply estep_PC_i; try reflexivity.
Qed.
    
Lemma test_constant_time_cond_false :
    step_prog Executable
    (list_prog_to_prog [Jnz (inr (register 0)) (word 2); Load (register 0) (register 0)],
    (word 0, <[register 0:= word 0]>(emptyReg), emptyMem),
    [])
    NextI
    (list_prog_to_prog [Jnz (inr (register 0)) (word 2); Load (register 0) (register 0)],
    (word 1, <[register 0:= word 0]>(emptyReg), emptyMem),
    [ControlFlowLeak [word 1]]).
Proof.
    eapply estep_PC_i; try reflexivity.
Qed.


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

Module asm_lang.
Canonical Structure asm_lang := Language asm_lang_mixin.


Global Instance into_val_val {v : val} : @IntoVal asm_lang (of_val v) v.
Proof.
  destruct v; done.
Qed.

Class NotVal (e : expr) :=
  not_val : to_val e = None.

#[global] Hint Extern 1 (NotVal _) => fast_done : typeclass_instances.

Class NoFork (e1 : expr) :=
  nofork : (∀ σ1 κ σ1' e1' efs, prim_step e1 σ1 κ e1' σ1' efs → efs = []).

Class NoObs (e1 : expr) :=
  noobs : (∀ σ1 κ σ1' e1' efs, prim_step e1 σ1 κ e1' σ1' efs → κ = []).

#[export] Instance instrExAtomic : @Atomic asm_lang StronglyAtomic (Instr Executable).
Proof.
  unfold Atomic. intros.
  inversion H; subst.
  inversion H0; subst.
  destruct (prog (PC φ)); done.
Qed.

#[export] Instance no_fork_instr_ex : NoFork (Instr Executable).
Proof.
  unfold NoFork.
  intros.
  inversion H.
  reflexivity.
Qed.


Lemma normal_always_step:
    forall sll, exists cf sll', step_prog Executable sll cf sll'.
  Proof.
    destruct sll as [[prog φ] ll].
    intros.
    destruct (prog (PC φ)) as [] eqn:H.
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

Lemma reducible_no_obs_from_step_prog σ1 f2 σ2 :
  step_prog Executable σ1 f2 σ2 →
  reducible_no_obs (Instr Executable) σ1.
Proof. intros * HH. rewrite /reducible_no_obs //=.
       eexists (Instr _), σ2, []. by constructor.
Qed.

Lemma normal_always_reducible σ :
  reducible (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply reducible_from_step_prog. eauto.
Qed.

Lemma normal_always_reducible_no_obs σ :
  reducible_no_obs (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply reducible_no_obs_from_step_prog. eauto.
Qed.

Lemma loop_next_always_reducible σ :
  reducible (Loop NextI) σ.
Proof. rewrite /reducible //=.
       eexists [], _, σ, []. by constructor.
Qed.
End asm_lang.
