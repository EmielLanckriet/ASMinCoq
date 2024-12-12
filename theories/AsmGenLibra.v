From Coq Require Import Eqdep_dec.
(* Needed to prove decidable equality on Register *)
From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_maps relations vector.
From ASMinCoq Require Import CpdtTactics AsmGen.
From iris.program_logic Require Import language ectx_language ectxi_language.

Inductive LO : Type :=
  | lo (n : nat) : LO.

#[export] Instance inhabited_lo : Inhabited LO.
Proof.
  constructor.
  exact (lo 0).
Qed.

Definition lo_to_nat (offset : LO) : nat :=
  match offset with lo n => n end.

Definition ExecConfLibra := (Word * LO * Reg * Mem)%type.

(* Definition Conf: Type := ConfFlag * ExecConf. *)

Definition reg (ϕ : ExecConfLibra) : Reg := snd (fst ϕ).

Definition mem (ϕ : ExecConfLibra) : Mem := snd ϕ.

Definition PC (φ : ExecConfLibra) : Word := fst (fst (fst φ)).

Definition Lo (φ : ExecConfLibra) : LO := snd (fst (fst φ)).

Definition PCLO (φ : ExecConfLibra) : Word * LO := fst (fst φ).

Lemma PCLO_is_PC_LO (φ : ExecConfLibra) : (PC φ, Lo φ) = PCLO φ.
Proof.
  unfold PCLO, PC, Lo.
  rewrite -surjective_pairing.
  reflexivity.
Qed.

Definition update_reg (φ : ExecConfLibra) (r : Register) (w : Word): ExecConfLibra :=
  (PC φ, Lo φ, <[r:=w]>(reg φ),mem φ).
Definition update_mem (φ : ExecConfLibra) (a : Addr) (w : Word): ExecConfLibra :=
  (PC φ, Lo φ, reg φ, <[a:=w]>(mem φ)).
Definition update_PC (φ : ExecConfLibra) (w : Word) : ExecConfLibra :=
  (w, Lo φ, reg φ, mem φ).
Definition update_LO (φ : ExecConfLibra) (offset : LO) : ExecConfLibra :=
  (PC φ, offset, reg φ, mem φ).


Definition incr_PC (φ : ExecConfLibra) : ExecConfLibra :=
    update_PC φ (incr_word (PC φ)).

(* Some easy lemmas to easily let these things commute and stuff *)

Lemma PC_is_updated_value (φ : ExecConfLibra) (pc : Word) : PC (update_PC φ pc) = pc.
Proof. reflexivity. Qed.

Lemma PC_is_incr (φ : ExecConfLibra) : PC (incr_PC φ) = incr_word (PC φ).
Proof. reflexivity. Qed.

Lemma reg_is_updated_value (φ : ExecConfLibra) (r : Register) (w : Word) :
    reg (update_reg φ r w) = <[r:=w]>(reg φ).
Proof. reflexivity. Qed.

Lemma mem_is_updated_value (φ : ExecConfLibra) (a : Addr) (w : Word) :
    mem (update_mem φ a w) = <[a:=w]>(mem φ).
Proof. reflexivity. Qed.

Lemma update_reg_no_change_pc (φ : ExecConfLibra) (r : Register) (w : Word) :
    PC φ = PC (update_reg φ r w).
Proof. reflexivity. Qed.

Lemma update_reg_no_change_mem (φ : ExecConfLibra) (r : Register) (w : Word) :
    mem φ = mem (update_reg φ r w).
Proof. reflexivity. Qed.

Lemma update_pc_no_change_reg (φ : ExecConfLibra) (w : Word) :
    reg φ = reg (update_PC φ w).
Proof. reflexivity. Qed.

Lemma update_pc_no_change_mem (φ : ExecConfLibra) (w : Word) :
    mem φ = mem (update_PC φ w).
Proof. reflexivity. Qed.

Lemma update_mem_no_change_pc (φ : ExecConfLibra) (a : Addr) (w : Word) :
    PC φ = PC (update_mem φ a w).
Proof. reflexivity. Qed.

Lemma update_mem_no_change_reg (φ : ExecConfLibra) (a : Addr) (w : Word) :
    reg φ = reg (update_mem φ a w).
Proof. reflexivity. Qed.


Definition word_from_argument (φ : ExecConfLibra) (src : Word + Register) : Word :=
    match src with
    | inl w => w
    | inr r => (reg φ) !!! r
    end.


(** Different constructor for instructions that only mention the general categories in which instructions are introduced in Waterman's thesis *)
Inductive instrLibra : Type :=
(** Computational and control flow instructions can get their inputs from registers and words (called immediates) *)
| ComputationL {n : nat} (inputs : vec (Word + Register) n)
    (rres : Register) (f_result : vec Word n -> Word)
| ControlFlowL {n : nat} (inputs : vec (Word + Register) n)
    (dst : Word) (f_condition : vec Word n -> bool) (* No indirect branches *)
| LOControlFlowL {n : nat} (inputs : vec (Word + Register) n) (offset1 offset2 : LO) (f_condition : vec Word n -> bool)
| JmpL (dst : Word)
| LoadL (rdst rsrc: Register)
| StoreL (rdst : Register) (src : Word + Register)
| MimicLeakL (i : instrLibra)
| HaltL.

Hint Constructors instrLibra : core.

    
Definition confflag_instr (i : instrLibra) (φ : ExecConfLibra) : ConfFlag :=
    match i with
    | HaltL => Halted
    | _ => NextI
    end.

Definition exec_instr (i : instrLibra) (φ : ExecConfLibra) : ExecConfLibra :=
    match i with
    | HaltL => φ
    | ComputationL inputs rres f_result =>
        incr_PC (
                update_reg φ rres (
                    f_result (inputs_from_inputnatregs (reg φ) inputs)))
    | ControlFlowL inputs dst f_condition =>
        match (f_condition (inputs_from_inputnatregs (reg φ) inputs)) with
        | true => update_PC (update_LO φ (lo 0)) dst
        | false => incr_PC (update_LO φ (lo 0))
        end
    | LOControlFlowL inputs offset1 offset2 f_condition =>
        match (f_condition (inputs_from_inputnatregs (reg φ) inputs)) with
        | true => incr_PC (update_LO φ offset1)
        | false => incr_PC (update_LO φ offset2)
        end
    | JmpL dst => update_PC (update_LO φ (lo 0)) dst
    | LoadL rres rsrc => 
        let wsrc := (reg φ) !!! rsrc in
        let asrc := word_to_addr wsrc in
        let res := (mem φ) !!! asrc in
        incr_PC (update_reg φ rres res)
    | StoreL rdst src =>
        let wsrc := wordreg_to_word (reg φ) src in
        let wdst := (reg φ) !!! rdst in
        let adst := word_to_addr wdst in
        incr_PC (update_mem φ adst wsrc)
    | MimicLeakL i => φ
    end. 

Fixpoint leak_instr (i : instrLibra) (φ : ExecConfLibra) : leak :=
    match i with
    | HaltL => HaltLeak
    | ComputationL inputs rres f_result => ComputationLeak f_result
    | ControlFlowL inputs dst f_condition =>
        ControlFlowLeak (if f_condition (inputs_from_inputnatregs (reg φ) inputs)
                         then [dst]
                         else [PC (incr_PC φ)])
    | LOControlFlowL _ _ _ _ => ControlFlowLeak [PC (incr_PC φ)]
    | JmpL dst => ControlFlowLeak [dst]
    | LoadL rres rsrc =>
        let wsrc := (reg φ) !!! rsrc in
        let asrc := word_to_addr wsrc in
        LoadLeak asrc
    | StoreL rdst src =>
        let asrc := (word_to_addr (wordreg_to_word (reg φ) src)) in StoreLeak asrc
    | MimicLeakL i => leak_instr i φ
    end.


(** Contrary to Cerise, programs are not part of the memory in this model *)
Definition programLibra : Type := (Word * LO) -> instrLibra.

Definition stateLibra : Type := programLibra * ExecConfLibra.
Print nth_default.
Definition list_prog_to_prog_libra (li : list (list instrLibra)) : programLibra :=
    fun (w_and_offset : Word * LO) => match w_and_offset with
                                        | (w , offset) =>
                                            nth_default HaltL (nth_default [] li (word_to_nat w)) (lo_to_nat offset)
                                      end.



Inductive step_prog_libra : ConfFlag -> stateLibra * list leak -> ConfFlag -> stateLibra * list leak -> Prop :=
    | step_PC_i (prog : programLibra) (φ : ExecConfLibra) (ll : list leak) :
      step_prog_libra Executable (prog, φ, ll) (confflag_instr (prog (PCLO φ)) φ) (prog, exec_instr (prog (PCLO φ)) φ, leak_instr (prog (PCLO φ)) φ :: ll).

Hint Constructors step_prog : core.

Lemma estep_PC_i (prog : programLibra) (φ φ' : ExecConfLibra) (ll ll' : list leak) (c' : ConfFlag) (i : instrLibra) (PC_i : prog (PCLO φ) = i) (result : stateLibra * list leak) :
    c' = confflag_instr i φ ->
    φ' = exec_instr i φ  ->
    ll' = leak_instr i φ :: ll ->
    result = (prog, φ', ll') ->
    step_prog_libra Executable (prog, φ, ll) c' result.
Proof.
    intros. subst. econstructor.
Qed.


Lemma step_prog_deterministic (prog : programLibra):
    forall f1 f1' f2 f2' c1 c2 c2' σ1 σ2 σ2',
      step_prog_libra f1 (c1, σ1) f2 (c2, σ2) →
      step_prog_libra f1' (c1, σ1) f2' (c2', σ2') →
      f2 = f2' ∧ c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; try split; inversion H1; inversion H2; auto; try congruence.
  Qed.


Definition AddL (dst: Register) (r1 r2: Word + Register) : instrLibra :=
    ComputationL [# r1; r2] dst add_vec_2.

Definition JnzL (cond : Word + Register) (dst : Word) : instrLibra :=
    ControlFlowL [# cond] dst notzero_vec_1.

Inductive prim_step_libra : AsmGen.expr → stateLibra * list leak → list Empty_set → AsmGen.expr → stateLibra * list leak → list AsmGen.expr → Prop :=
| PS_no_fork_instr σ cf σ' :
        step_prog_libra Executable σ cf σ' -> prim_step_libra (Instr Executable) σ [] (Instr cf) σ' []
| PS_no_fork_loop_ex σ cf σ' :
        step_prog_libra Executable σ cf σ' -> prim_step_libra (Loop Executable) σ [] (Loop cf) σ' []
| PS_no_fork_loop σ : prim_step_libra (Loop NextI) σ [] (Loop  Executable) σ [].

Hint Constructors prim_step_libra : core.

Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step_libra e σ o e' σ' efs →
      AsmGen.to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

Lemma libra_lang_mixin : LanguageMixin AsmGen.of_val AsmGen.to_val prim_step_libra.
Proof.
    constructor;
    apply _ || eauto using AsmGen.to_of_val, AsmGen.of_to_val, val_stuck.
Qed.

Module libra_lang.
Canonical Structure libra_lang := Language libra_lang_mixin.


Global Instance into_val_val {v : AsmGen.val} : @IntoVal libra_lang (AsmGen.of_val v) v.
Proof.
  destruct v; done.
Qed.

Class NoForkLibra (e1 : AsmGen.expr) :=
  nofork : (∀ σ1 κ σ1' e1' efs, prim_step_libra e1 σ1 κ e1' σ1' efs → efs = []).

Class NoObsLibra (e1 : AsmGen.expr) :=
  noobs : (∀ σ1 κ σ1' e1' efs, prim_step_libra e1 σ1 κ e1' σ1' efs → κ = []).

#[export] Instance instrExAtomic : @Atomic libra_lang StronglyAtomic (Instr Executable).
Proof.
  unfold Atomic. intros.
  inversion H; subst.
  inversion H0; subst.
  destruct (prog (PCLO φ)); done.
Qed.

#[export] Instance no_fork_instr_ex_libra : NoForkLibra (Instr Executable).
Proof.
  unfold NoForkLibra.
  intros.
  inversion H.
  reflexivity.
Qed.


Lemma normal_always_step:
    forall (sll : stateLibra * list leak), exists cf sll', step_prog_libra Executable sll cf sll'.
  Proof.
    destruct sll as [[prog φ] ll].
    intros.
    destruct (prog (PCLO φ)) as [] eqn:H.
    (* Resolve the HaltL case *)
    all: try solve [exists Halted; eexists; eapply estep_PC_i; auto; rewrite H; auto].
    all: try (exists NextI; eexists; eapply estep_PC_i; auto; rewrite H; reflexivity).
  Qed.


  Lemma reducible_from_step_prog (σ1 : stateLibra * list leak) f2 σ2 :
  step_prog_libra Executable σ1 f2 σ2 →
  reducible (Instr Executable) σ1.
Proof. intros * HH. rewrite /reducible //=.
       eexists [], (Instr _), σ2, []. by constructor.
Qed.

Lemma reducible_no_obs_from_step_prog (σ1 : stateLibra * list leak) f2 σ2 :
  step_prog_libra Executable σ1 f2 σ2 →
  reducible_no_obs (Instr Executable) σ1.
Proof. intros * HH. rewrite /reducible_no_obs //=.
       eexists (Instr _), σ2, []. by constructor.
Qed.

Lemma normal_always_reducible (σ : stateLibra * list leak) :
  reducible (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply reducible_from_step_prog. eauto.
Qed.

Lemma normal_always_reducible_no_obs (σ : stateLibra * list leak)  :
  reducible_no_obs (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply reducible_no_obs_from_step_prog. eauto.
Qed.

Lemma loop_next_always_reducible (σ : stateLibra * list leak)  :
  reducible (Loop NextI) σ.
Proof. rewrite /reducible //=.
       eexists [], _, σ, []. by constructor.
Qed.
End libra_lang.
