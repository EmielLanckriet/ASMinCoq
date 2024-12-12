From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting total_lifting total_weakestpre.
From iris.algebra Require Import frac auth gmap excl.
From Coq.Lists Require Import List.
From ASMinCoq Require Import CpdtTactics progLogHelper AsmGen AsmGenLibra.
From Coq.Classes Require Import DecidableClass.
From Coq.Logic Require Import FinFun.

(* We try to make a criterion based on which we can judge compilability and determine the leakage of secret control flow branches *)
(* This criterion does not need to contain all the information to compile in an easy form because we will still require the Libra program to be provided as well *)


Inductive binTree (A : Type) : Type :=
| leaf (node : A)
| one_branch (node : A) (tree : binTree A)
| two_branch (node : A) (leftTree rightTree : binTree A).
Arguments leaf {A}.
Arguments one_branch {A}.
Arguments two_branch {A}.

Fixpoint leafs {A : Type} (tree : binTree A) :=
  match tree with
  | leaf a => [a]
  | one_branch a rest => leafs rest
  | two_branch a leftT rightT => leafs leftT ++ leafs rightT
  end.

Local Notation "node ;;; tree" := (one_branch node tree)
                                  (at level 75, tree at level 200, right associativity,
                                    format "'[v' node  ;;; '//' tree ']'").
Local Notation "node ;;;; { ( leftTree ) ||| ( rightTree ) }" := (two_branch node leftTree rightTree)
                                                          (at level 75, leftTree at level 200, rightTree at level 200, right associativity,
                                      format "'[v' node  ;;;; '//' '{' '(' leftTree ')' '|||' '(' rightTree ')' '}' ']'").


Record instructionTreeGraph : Type :=
  { (* [Block] is a datatype representing the labels of blocks. Each program
       can define its own way to represent these labels. *)
    Block       : Type;

    (* We require a way to decide equality between block labels. *)
    block_equal : forall (b1 b2 : Block), sumbool (b1 = b2) (b1 <> b2);

    (* The program has a designated start block, represented by the [Start]
       label. *)
    Start       : Block;

    (* Each block is associated with a sequence of instructions, defined
       by the [Instrs] function. *)
    Instrs      : Block -> binTree (nat * instr);

    Targets     : Block -> list Block;
  }.

Definition firstAddress (natInstrTree : binTree (nat * instr)) : nat :=
  match natInstrTree with
  | leaf (a, _) => a
  | one_branch (a, _) _ => a
  | two_branch (a, _) _ _ => a
  end.

Definition entryAddress (itg : instructionTreeGraph) (block : Block itg) :=
  firstAddress ((Instrs itg) block).

Inductive test_block := StartBlock | Unreachable | Rest.

Lemma test_block_equal (b1 b2 : test_block) :
  sumbool (b1 = b2) (b1 <> b2).
Proof.
  decide equality.
Defined.

Definition cfg_test_list (high_input : nat) : list instr :=
  [
    Add (register 0) (inl (word high_input)) (inl (word high_input));
    JnzSecret (inr (register 0)) (word 4) [word 1];
    Jmp false (word 5) [];
    Halt;
    Jmp false (word 5) [];
    Halt
  ].

Definition test_instrs (high_input : nat) (x : test_block) : binTree (nat * instr) :=
  match x with
  | StartBlock   => (0, Add (register 0) (inl (word high_input)) (inl (word high_input))) ;;;
              (1, JnzSecret (inr (register 0)) (word 4) [word 1]) ;;;;
              {
                (leaf (2, (Jmp false (word 5) [])))
                  |||
                (leaf (4, (Jmp false (word 5) [])))
              }
  | Unreachable => leaf (3, Halt)
  | Rest => leaf (5, Halt)
  end.

Definition targets_test (x : test_block) : list test_block :=
  match x with
  | StartBlock => [Rest]
  | Unreachable => []
  | Rest => []
  end.

Canonical instructionBlockTreeTest (high_input : nat) : instructionTreeGraph :=
  {|
    Block       := test_block;
    block_equal := test_block_equal;
    Start       := StartBlock;
    Instrs      := test_instrs high_input;
    Targets     := targets_test
  |}.

Inductive not_control_flow : instr -> Prop :=
| is_computation {n : nat} dst (inputs : vec (Word + Register) n) f_result : not_control_flow (Computation inputs dst f_result)
| is_load rdst rsrc : not_control_flow (Load rdst rsrc)
| is_store rdst src : not_control_flow (Store rdst src)
| is_mimicleak i : not_control_flow (MimicLeak i).


Fixpoint projectBintreeNatA {A : Type} (tree : binTree (nat * A)) :=
  match tree with
  | leaf (a, i) => gset_singleton a
  | one_branch (a, i) restTree => gset_union (gset_singleton a) (projectBintreeNatA restTree)
  | two_branch (a, i) leftTree rightTree => gset_union (gset_singleton a) (gset_union (projectBintreeNatA leftTree) (projectBintreeNatA rightTree))
  end.

Compute projectBintreeNatA ((Instrs (instructionBlockTreeTest 2)) StartBlock).

Definition blocksDontOverlap (itg : instructionTreeGraph) := forall (b1 b2 : Block itg), b1 = b2 \/ (projectBintreeNatA ((Instrs itg) b1)) ## (projectBintreeNatA ((Instrs itg) b2)).

Lemma testBDO : blocksDontOverlap (instructionBlockTreeTest 2).
Proof.
  intros b1 b2.
  destruct ((block_equal (instructionBlockTreeTest 2)) b1 b2).
  { left. assumption. }
  right.
  destruct b1; destruct b2; try congruence; simpl;
   by eapply bool_decide_eq_true_1.
Qed.

Definition jumpTargetInstr (ni : nat * instr) : list nat :=
  match ni with
  | (n, i) =>
      match i with
      | ControlFlow _ _ dst _ _ => [(word_to_nat dst); n + 1]
      | Halt => []
      | Jmp _ dst _ => [word_to_nat dst]
      | _ => [n + 1]
      end
  end.

Definition jumpTargetsTree (tree : binTree (nat * instr)) : list nat :=
  concat (map jumpTargetInstr (leafs tree)).

Definition addressIsStartOfTarget (itg : instructionTreeGraph) (block : Block itg) (a : nat) :=
  Exists (fun block' => a = entryAddress itg block') ((Targets itg) block).

Definition blockHasRightTarget (itg : instructionTreeGraph) (block : Block itg) :=
  Forall (fun n => addressIsStartOfTarget itg block n) (jumpTargetsTree ((Instrs itg) block)).

Definition blocksHaveRightTargets (itg : instructionTreeGraph) :=
  forall (block : Block itg), blockHasRightTarget itg block.

Lemma blocksHaveRightTargetsTest : blocksHaveRightTargets (instructionBlockTreeTest 2).
Proof.
  intro block.
  destruct block; by repeat constructor.
Qed.


Fixpoint treeToLevelsWithDups {A : Type} (tree : binTree A) : list (list A) :=
  match tree with
  | leaf a => [[a]]
  | one_branch a rest => [a] :: treeToLevelsWithDups rest
  | two_branch a leftT rightT => [a] :: zip_with (++) (treeToLevelsWithDups leftT) (treeToLevelsWithDups rightT)
  end.

Fixpoint removeDuplicateAddresses {A : Type} (l : list (nat * A)) : list (nat * A) :=
  match l with
  | [] => []
  | x :: l =>
      match x with
      | (n , i) => if decide_rel (∈) n (map fst l)  then removeDuplicateAddresses l else x :: removeDuplicateAddresses l
      end
  end.

Definition treeToLevels (tree : binTree (nat * instr)) : list (list (nat * instr)) :=
  map removeDuplicateAddresses (treeToLevelsWithDups tree).

Definition map_option {A B : Type} (f : A -> B) (a : option A) : option B :=
  match a with
  | None => None
  | Some a => Some (f a)
  end.

Definition compareLeakageAndLevels (leakage : list Word) (tree_levels : list (list (nat * instr))) : Prop :=
  Some (remove_dups (map word_to_nat leakage)) = map_option (map fst) (head tree_levels).

Definition ifSecretControlFlowCompareLeakageAndLevelse (i : instr) (tree_levels : list (list (nat * instr))) : Prop :=
  match i with
  | ControlFlow true _ _ _ leakage => compareLeakageAndLevels leakage tree_levels
  | Jmp true _ leakage => compareLeakageAndLevels leakage tree_levels
  | _ => True
  end.

Fixpoint secretBranchesHaveRightLeakageHelper (tree_levels : list (list (nat * instr))) (tree : binTree (nat * instr)) :=
  match tree with
  | leaf (a, i) => ifSecretControlFlowCompareLeakageAndLevelse i tree_levels
  | one_branch (a, i) rest => ifSecretControlFlowCompareLeakageAndLevelse i tree_levels /\ secretBranchesHaveRightLeakageHelper (tail tree_levels) rest
  | two_branch (a, i) leftT rightT => ifSecretControlFlowCompareLeakageAndLevelse i tree_levels /\ secretBranchesHaveRightLeakageHelper (tail tree_levels) leftT /\ secretBranchesHaveRightLeakageHelper (tail tree_levels) rightT
  end.

Definition secretBranchesHaveRightLeakage (tree : binTree (nat * instr)) :=
  secretBranchesHaveRightLeakageHelper (treeToLevels tree) tree.

Definition testSecretBranchesTree :=
  (0, Add (register 0) (inl (word 2)) (inl (word 2))) ;;;
    (1, JnzSecret (inr (register 0)) (word 4) [word 1]) ;;;;
    {
      (
        (2, Jmp true (word 5) [word 2; word 4]) ;;;
          (5, Jmp true (word 6) [word 5]) ;;;
          leaf (6, Halt)
      )
        |||
      (
        (4, Jmp true (word 5) [word 2; word 4]) ;;;
          (5, Jmp true (word 6) [word 5]) ;;;
          leaf (6, Halt)
      )
    }.

Lemma hehg : secretBranchesHaveRightLeakage testSecretBranchesTree.
Proof.
  unfold secretBranchesHaveRightLeakage.
  simpl. unfold compareLeakageAndLevels. simpl. tauto.
Qed.

Definition blocksSecretBranchesHaveRightLeakage (itg : instructionTreeGraph) :=
  forall (block : Block itg), secretBranchesHaveRightLeakage ((Instrs itg) block).


Inductive treeIsDepictionOfControlFlow : binTree (nat * instr) -> Prop :=
  (* Leafs *)
| tpcf_leaf_PCF {n : nat} (a : nat) (inputs : vec (Word + Register) n) dst f_condition leakage
  : treeIsDepictionOfControlFlow (leaf (a, ControlFlow false inputs dst f_condition leakage))
| tpcf_leaf_Halt (a : nat) : treeIsDepictionOfControlFlow (leaf (a, Halt))
| tpcf_leaf_Jmp (a : nat) (dst : Word) (leakage : list Word) : treeIsDepictionOfControlFlow (leaf (a, Jmp false dst leakage))
(* One branch *)
| tpcf_ComputationOneBranch  {n : nat} (a : nat) dst (inputs : vec (Word + Register) n) f_result
    (restTree : binTree (nat * instr)) (rest_right : treeIsDepictionOfControlFlow restTree)
    (fstAddrIsIncrA : a + 1 = firstAddress restTree)
  : treeIsDepictionOfControlFlow (one_branch (a, Computation inputs dst f_result) restTree)
| tpcf_LoadOneBranch (a : nat) rdst rsrc
    (restTree : binTree (nat * instr)) (rest_right : treeIsDepictionOfControlFlow restTree)
    (fstAddrIsIncrA : a + 1 = firstAddress restTree)
  : treeIsDepictionOfControlFlow (one_branch (a, Load rdst rsrc) restTree)
| tpcf_StoreOneBranch (a : nat) rdst src
    (restTree : binTree (nat * instr)) (rest_right : treeIsDepictionOfControlFlow restTree)
    (fstAddrIsIncrA : a + 1 = firstAddress restTree)
  : treeIsDepictionOfControlFlow (one_branch (a, Store rdst src) restTree)
| tpcf_MimicLeakOneBranch (a : nat) (i : instr)
    (restTree : binTree (nat * instr)) (rest_right : treeIsDepictionOfControlFlow restTree)
    (fstAddrIsIncrA : a + 1 = firstAddress restTree)
  : treeIsDepictionOfControlFlow (one_branch (a, MimicLeak i) restTree)
| tpcf_one_branch_SJmp (a : nat) dst leakage
    (restTree : binTree (nat * instr)) (rest_right : treeIsDepictionOfControlFlow restTree)
    (fstAddrIsDst : word_to_nat dst = firstAddress restTree):
  treeIsDepictionOfControlFlow (one_branch (a, Jmp true dst leakage) restTree)
(* Two branches *)
| tpcf_two_branch_SCF  {n : nat} (a : nat) (inputs : vec (Word + Register) n) dst f_condition leakage
    (leftTree rightTree : binTree (nat * instr)) (left_right_str : treeIsDepictionOfControlFlow leftTree) (right_right_str : treeIsDepictionOfControlFlow rightTree)
    (fstAddrLeftIsIncrA : a + 1 = firstAddress leftTree)
    (fstAddrRightIsDst : word_to_nat dst = firstAddress rightTree) :
  treeIsDepictionOfControlFlow (two_branch (a, ControlFlow true inputs dst f_condition leakage) leftTree rightTree).

Lemma test1 : treeIsDepictionOfControlFlow ((Instrs (instructionBlockTreeTest 2)) StartBlock).
Proof.
  repeat constructor.
Qed.
Lemma test2 : treeIsDepictionOfControlFlow testSecretBranchesTree.
Proof.
  repeat constructor.
Qed.

Definition blocksAreDepictionOfControlFlow (itg : instructionTreeGraph) :=
  forall (block : Block itg), treeIsDepictionOfControlFlow ((Instrs itg) block).


(* Now, I want to write a compiler where the input is an asmGen program (a list of instructions) and an instructionTreeGraph, such that the address correspoding to each instruction in the instruction tree graph actually points to the same instruction in the list.
Furthermore, the instructionTreeGraph should satisfy that all the blocks are disjoint (because we didn't use DAG but trees, the same address can appear twice in a binTrees), that the control flow depicted by the graph corresponds the control flow that is possible based on the instructions and that the leakage proclaimed by the secret branches is actually the set of addresses where secret branches of the same level could be executed instead.  *)

Definition treeIsWellBehaved (itg : instructionTreeGraph) :=
  blocksDontOverlap itg /\
    blocksAreDepictionOfControlFlow itg /\
    blocksSecretBranchesHaveRightLeakage itg /\
    blocksHaveRightTargets itg.

Fixpoint treeIsRelatedToCode (tree : binTree (nat * instr)) (prog : list instr) : Prop :=
  match tree with
  | leaf (a, i) => nth a prog Halt = i
  | one_branch (a, i) restTree => nth a prog Halt = i /\ treeIsRelatedToCode restTree prog
  | two_branch (a, i) leftTree rightTree =>
      nth a prog Halt = i /\ treeIsRelatedToCode leftTree prog /\ treeIsRelatedToCode rightTree prog
  end.

Lemma test1' : treeIsRelatedToCode (test_instrs 2 StartBlock) (cfg_test_list 2).
Proof.
  simpl. tauto.
Qed.

Definition itgRelatedToCode (itg : instructionTreeGraph) (prog : list instr) :=
  forall (block : Block itg), treeIsRelatedToCode ((Instrs itg) block) prog.

Lemma test1'' : itgRelatedToCode (instructionBlockTreeTest 2) (cfg_test_list 2).
Proof.
  intro block.
  destruct block; simpl; tauto.
Qed.


(* To easily translate jump targets, we need a preprocessing that tells where each of the basic blocks end up in memory and specifically where each of the addresses from the tree get mapped to.
Because this preprocessing is not a vital part of the security proof, we just write a compiler given this mapping.
 *)


(* First a test case, the asmgen and related libra version *)

Definition JnzL (cond : Word + Register) (dst : Word) : instrLibra :=
  ControlFlowL [# cond] dst notzero_vec_1.


Definition validBlockOrder (itg : instructionTreeGraph) (lb : list (Block itg)) : Prop :=
  head lb = Some (Start itg) /\
    forall (block : Block itg), In block lb /\
    lb = nodup (block_equal itg) lb.

Definition testBlockOrder := [StartBlock; Unreachable; Rest].

Lemma testBlockOrderIsValid : validBlockOrder (instructionBlockTreeTest 2) testBlockOrder.
Proof.
  split.
  { reflexivity. }
  intro block.
  destruct block; crush.
Qed.

(* Create code based on block list *)
Definition blockListToConcatTreeLevels (itg : instructionTreeGraph) (lb : list (Block itg)) : list (list (nat * instr)) :=
  concat (map treeToLevels (map (Instrs itg) lb)).

Compute map (map fst) (blockListToConcatTreeLevels (instructionBlockTreeTest 2) testBlockOrder).

Fixpoint findNewCoordinateInList (l : list (nat * instr)) (a : nat) : option nat :=
  map_option fst (list_find (fun x => a = fst x) l).


Fixpoint findNewCoordinateHelper (l : list (list (nat * instr))) (a : nat) (acc : nat) : nat * nat :=
  match l with
  | [] => (acc, 0)
  | x :: l' =>
      match findNewCoordinateInList x a with
      | Some index => (acc, index)
      | None => findNewCoordinateHelper l' a (S acc)
      end
  end.

Definition findNewCoordinate (l : list (list (nat * instr))) (a : nat) : nat * nat :=
  findNewCoordinateHelper l a 0.

Compute findNewCoordinate (blockListToConcatTreeLevels (instructionBlockTreeTest 2) testBlockOrder) 6.

Fixpoint compilerHelperInstruction (full_list : list (list (nat * instr))) (a : nat) (i : instr) : instrLibra :=
  match i with
  | Halt => HaltL
  | Computation inputs rres f_result =>
      ComputationL inputs rres f_result
  | ControlFlow secret inputs dst f_condition leakage =>
      match secret with
      | false => ControlFlowL inputs dst f_condition
      | true => LOControlFlowL inputs (lo (snd (findNewCoordinate full_list (a + 1)))) (lo (snd (findNewCoordinate full_list (word_to_nat dst)))) f_condition
      end
  | Jmp secret dst leakage =>
      match secret with
      | false => JmpL (word (fst (findNewCoordinate full_list (word_to_nat dst))))
      | true => LOControlFlowL [#] (lo (snd (findNewCoordinate full_list (word_to_nat dst)))) (lo (snd (findNewCoordinate full_list (word_to_nat dst)))) (fun _ => true)
      end
  | Load rres rsrc => LoadL rres rsrc          
  | Store rdst src => StoreL rdst src
  | MimicLeak i => MimicLeakL (compilerHelperInstruction full_list a i)
  end.

Definition compiler (itg : instructionTreeGraph) (lb : list (Block itg))
  : list (list instrLibra) :=
  map
    (map
       (fun x =>
          compilerHelperInstruction (blockListToConcatTreeLevels itg lb) x.1 x.2))
    (blockListToConcatTreeLevels itg lb).

Lemma h : [[ComputationL [#inl (word 2); inl (word 2)] (register 0) add_vec_2];
           [LOControlFlowL [#inr (register 0)] (lo 0) (lo 1) notzero_vec_1];
           [JmpL (word 4); JmpL (word 4)]; [HaltL]; [HaltL]]
          = compiler (instructionBlockTreeTest 2) testBlockOrder.
Proof.
  reflexivity.
Qed.


(* Now, we test the compiler for an example with recombination *)

Definition cfg_test_list_recombination  : list instr :=
  [
    Add (register 0) (inl (word 2)) (inl (word 2));
    JnzSecret (inr (register 0)) (word 4) [word 1];
    Jmp true (word 5) [word 2; word 4];
    Halt;
    Jmp true (word 5) [word 2; word 4];
    Jmp false (word 6) [word 5] ;
    Halt
  ].

Definition test_instrs_recombination (x : test_block) : binTree (nat * instr) :=
  match x with
  | StartBlock   => (0, Add (register 0) (inl (word 2)) (inl (word 2))) ;;;
                      (1, JnzSecret (inr (register 0)) (word 4) [word 1]) ;;;;
                      {
                        (
                          (2, Jmp true (word 5) [word 2; word 4]) ;;;
                            leaf (5, Jmp false (word 6) [word 5])
                        )
                          |||
                          (
                            (4, Jmp true (word 5) [word 2; word 4]) ;;;
                              leaf (5, Jmp false (word 6) [word 5])
                          )
                      }
  | Unreachable => leaf (3, Halt)
  | Rest => leaf (6, Halt)
  end.


Canonical instructionBlockTreeTestRecombination : instructionTreeGraph :=
  {|
    Block       := test_block;
    block_equal := test_block_equal;
    Start       := StartBlock;
    Instrs      := test_instrs_recombination;
    Targets     := targets_test
  |}.

Lemma h'' : itgRelatedToCode instructionBlockTreeTestRecombination
              cfg_test_list_recombination.
Proof.
  intro block.
  destruct block; simpl; tauto.
Qed.

Lemma h' : [[ComputationL [#inl (word 2); inl (word 2)] (register 0) add_vec_2];
            [LOControlFlowL [#inr (register 0)] (lo 0) (lo 1) notzero_vec_1];
            [LOControlFlowL [# ] (lo 0) (lo 0) (fun x => true);
             LOControlFlowL [# ] (lo 0) (lo 0) (fun x => true)];
            [JmpL (word 5)]; [HaltL]; [HaltL]]
          = compiler instructionBlockTreeTestRecombination testBlockOrder.
Proof.
  reflexivity.
Qed.

