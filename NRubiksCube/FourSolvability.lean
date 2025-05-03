import Mathlib.GroupTheory.Perm.Sign -- For Equiv.Perm.sign
import Mathlib.Data.Fintype.Basic    -- For Fintype instances
--import Mathlib.Algebra.BigOperators.Basic -- For Finset.sum
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating -- For AlternatingGroup definition Aₙ
--import Mathlib.GroupTheory.SpecificGroups.Symmetric -- For SymmetricGroup definition Sₙ
import Mathlib.Data.List.Induction
import NRubiksCube.FourRubik -- Assuming your main file is named FourRubik.lean

#check Equiv.Perm.sign

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-!
# Solvability Conditions for the 4x4x4 Rubik's Revenge

This file defines the conditions for a 4x4x4 cube state to be solvable,
based on Theorem 3.1 from "The First Law of Cubology for the Rubik's Revenge"
(arXiv:1611.07437v1 [math.CO]).

We aim to state the theorem:
A configuration `s : CubeState` is solvable if and only if:
1. `sgn(σ) = sgn(ρ)` (Corner and Center permutation signs match)
2. `∑ xᵢ ≡ 0 (mod 3)` (Corner orientation sum is 0)
3. `yᵢ = 1 - δ_{t,s}` (Edge orientation condition based on slot type 't' and piece type 's')

-/

namespace FourRubik -- Continue in the same namespace

open BigOperators -- For Finset.sum notation
open Equiv -- For Equiv.Perm

open FourRubik
open MoveImpl
open Indexing
-- ## Solvability Definition

/-- A CubeState `s` is solvable if it can be reached from the initial state
    by applying a sequence of basic moves. -/
def IsSolvable (s : CubeState) : Prop :=
  ∃ (moves : List BasicMove), s = apply_move_list moves 1

-- ## Condition 1: Permutation Signs

/-- Condition 1: The sign of the corner permutation must equal the sign
    of the center permutation. -/
def checkPermSigns (s : CubeState) : Prop :=
  Perm.sign s.corner_perm = Perm.sign s.center_perm

-- ## Condition 2: Corner Twist Sum

/-- The sume of corner orientations modulo 3. -/
def cornerTwist (s : CubeState) : ZMod 3 :=
  Finset.sum Finset.univ (s.corner_ori)

/-- Condition 2: The sum of corner orientation values must be 0 modulo 3. -/
def checkCornerTwist (s : CubeState) : Prop :=
  cornerTwist s = 0

-- ## Condition 3: Edge Flip Condition (Requires Helpers)

-- Helper function to get the EdgeType (A or B) associated with an EdgeSlot index
-- Based on our convention: even index = A, odd index = B
def getSlotType (slot : EdgeSlot) : Orientation.EdgeType :=
  if slot % 2 = 0 then Orientation.EdgeType.A else Orientation.EdgeType.B

-- Helper function to get the EdgeType (A or B) associated with the *original* piece
-- that currently resides in the given slot 'i' in state 's'.
-- This requires looking at the inverse permutation.
def getPieceTypeInSlot (s : CubeState) (slot : EdgeSlot) : Orientation.EdgeType :=
  let origin_slot : EdgeSlot := s.edge_perm⁻¹ slot
  -- The type depends on the origin slot's index (even/odd)
  getSlotType origin_slot

-- The delta function from the paper: δ_{t,s} = 1 if t=s, 0 otherwise
def edgeDelta (t s : Orientation.EdgeType) : ZMod 2 :=
  if t = s then 1 else 0

/-- Condition 3: The edge orientation `yᵢ` must match the formula `1 - δ_{t,s}`,
    where `t` is the type of slot `i` and `s` is the type of the piece in slot `i`. -/
def checkEdgeFlip (s : CubeState) : Prop :=
  ∀ (i : EdgeSlot), s.edge_ori i = 1 - edgeDelta (getSlotType i) (getPieceTypeInSlot s i)


-- ## key lemmas

-- Step 1: Show the initial state satisfies the condition.
theorem lemma1_step1_initial_state : checkCornerTwist 1 := by
  rw [checkCornerTwist]
  rfl

def get_move_corner_ori_delta (m : BasicMove) : CornerSlot → ZMod 3 :=
  match m with
  | .R => r_move_corner_ori_delta | .L => l_move_corner_ori_delta
  | .U => u_move_corner_ori_delta | .D => fun _ => 0
  | .F => f_move_corner_ori_delta | .B => b_move_corner_ori_delta
  | .CR => fun _ => 0 | .CL => fun _ => 0
  | .CU => fun _ => 0 | .CD => fun _ => 0
  | .CF => fun _ => 0 | .CB => fun _ => 0

def get_move_corner_perm (m : BasicMove) : Perm CornerSlot :=
  match m with
  | .R => r_move_corner_perm | .L => l_move_corner_perm
  | .U => u_move_corner_perm | .D => d_move_corner_perm -- Assuming d_move defined
  | .F => f_move_corner_perm | .B => b_move_corner_perm -- Assuming f_move/b_move defined
  | .CR => cr_move_corner_perm | .CL => cl_move_corner_perm -- Assuming cl_move defined
  | .CU => cu_move_corner_perm | .CD => cd_move_corner_perm -- Assuming cu/cd defined
  | .CF => cf_move_corner_perm | .CB => cb_move_corner_perm -- Assuming cf/cb defined

theorem sum_corner_ori_delta_eq_zero (m : BasicMove) :
    ∑ (i : CornerSlot), (get_move_corner_ori_delta m) i = 0 := by
  cases m with
  | R => rfl
  | L => rfl
  | U => rfl
  | D => rfl
  | F => rfl
  | B => rfl
  | CR => rfl
  | CL => rfl
  | CU => rfl
  | CD => rfl
  | CF => rfl
  | CB => rfl

theorem moveCornerTwist (m : BasicMove) (s : CubeState) :
  cornerTwist (apply_move m s) = cornerTwist s:= by
  unfold cornerTwist
  cases m with
  | R =>
    dsimp [apply_move]
    rw [Finset.sum_add_distrib]
    have h : ∑ x, s.corner_ori (r_move_corner_perm⁻¹ x) = cornerTwist s := by
      rw [r_move_corner_perm, cornerTwist]
      rw [Equiv.sum_comp]
    rw [h, cornerTwist, Equiv.sum_comp]
    simp only [add_eq_left]
    rfl
  | L =>
    dsimp [apply_move]
    rw [Finset.sum_add_distrib]
    have h : ∑ x, s.corner_ori (l_move_corner_perm⁻¹ x) = cornerTwist s := by
      rw [l_move_corner_perm, cornerTwist]
      rw [Equiv.sum_comp]
    rw [h, cornerTwist, Equiv.sum_comp]
    simp only [add_eq_left]
    rfl
  | U =>
    dsimp [apply_move]
    rw [u_move_corner_perm]
    rw [Equiv.sum_comp]
  | D =>
    dsimp [apply_move]
    rw [d_move_corner_perm]
    rw [Equiv.sum_comp]
  | F =>
    dsimp [apply_move]
    rw [Finset.sum_add_distrib]
    have h : ∑ x, s.corner_ori (f_move_corner_perm⁻¹ x) = cornerTwist s := by
      rw [f_move_corner_perm, cornerTwist]
      rw [Equiv.sum_comp]
    rw [h, cornerTwist, Equiv.sum_comp]
    simp only [add_eq_left]
    rfl
  | B =>
    dsimp [apply_move]
    rw [Finset.sum_add_distrib]
    have h : ∑ x, s.corner_ori (b_move_corner_perm⁻¹ x) = cornerTwist s := by
      rw [b_move_corner_perm, cornerTwist]
      rw [Equiv.sum_comp]
    rw [h, cornerTwist, Equiv.sum_comp]
    simp only [add_eq_left]
    rfl
  | CR =>
    dsimp [apply_move]
    rw [cr_move_corner_perm]
    rfl
  | CL =>
    dsimp [apply_move]
    rw [cl_move_corner_perm]
    rw [Equiv.sum_comp]
  | CU =>
    dsimp [apply_move]
    rw [cu_move_corner_perm]
    rfl
  | CD =>
    dsimp [apply_move]
    rw [cd_move_corner_perm]
    rfl
  | CF =>
    dsimp [apply_move]
    rw [cf_move_corner_perm]
    rfl
  | CB =>
    dsimp [apply_move]
    rw [cb_move_corner_perm]
    rw [Equiv.sum_comp]

-- Step 3: Show that applying any move preserves the sum-zero property.
theorem lemma1_step2_move_invariance (m : BasicMove) (s : CubeState) :
    checkCornerTwist s → checkCornerTwist (apply_move m s) := by
  intro h
  unfold checkCornerTwist at *
  simp [moveCornerTwist]
  exact h

theorem moves_check_corner_twist (moves : List BasicMove) (s : CubeState) :
    checkCornerTwist s → checkCornerTwist (apply_move_list moves s) := by
  induction moves using List.reverseRecOn with
  | nil => intro h; exact h
  | append_singleton ms m ih =>
    intro h
    rw [apply_move_list, List.foldl_append]
    simp_all only [forall_const, List.foldl_cons, List.foldl_nil]
    apply lemma1_step2_move_invariance
    exact ih

/-- Lemma 1 (Ref. Lemma 3.2): Corner twist sum is invariant under solvable moves.
    If a state `s` is solvable, its corner twist sum must be 0 (mod 3),
    since the initial state has sum 0. -/
theorem lemma1_corner_twist_invariant (s : CubeState) (hs : IsSolvable s) :
    checkCornerTwist s := by
  let ⟨moves, h⟩ := hs
  simp only [h, moves_check_corner_twist, lemma1_step1_initial_state]


-- Note: The following state the *consequences* of the isomorphism theorems
-- from the paper (Theorems 4.1, 4.2, 4.3) needed for the main proof.

theorem one_corner_center_sign_invariant :
    Perm.sign (CubeState.corner_perm 1) * Perm.sign (CubeState.center_perm 1) = 1 := by
  rfl

theorem move_corner_center_sign_invariant (m : BasicMove) (s : CubeState) :
    Perm.sign s.corner_perm * Perm.sign s.center_perm =
    Perm.sign (apply_move m s).corner_perm * Perm.sign (apply_move m s).center_perm := by
  cases m with
  | R =>
    dsimp [apply_move]
    unfold r_move_corner_perm
    unfold r_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | L =>
    dsimp [apply_move]
    unfold l_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_corner_perm
    unfold rotY_corner_perm
    unfold r_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    unfold l_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_center_perm
    unfold rotY_center_perm
    unfold r_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | U =>
    dsimp [apply_move]
    unfold u_move_corner_perm
    unfold u_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | D =>
    dsimp [apply_move]
    unfold d_move_corner_perm
    unfold d_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | F =>
    dsimp [apply_move]
    unfold f_move_corner_perm
    unfold f_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | B =>
    dsimp [apply_move]
    unfold b_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_corner_perm
    unfold rotY_corner_perm
    unfold f_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap]
    unfold b_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_center_perm
    unfold rotY_center_perm
    unfold f_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | CR =>
    dsimp [apply_move]
    unfold cr_move_corner_perm
    unfold cr_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | CL =>
    dsimp [apply_move]
    unfold cl_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_corner_perm
    unfold rotY_corner_perm
    unfold cr_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    unfold cl_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_center_perm
    unfold rotY_center_perm
    unfold cr_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | CU =>
    dsimp [apply_move]
    unfold cu_move_corner_perm
    unfold cu_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | CD =>
    dsimp [apply_move]
    unfold cd_move_corner_perm
    unfold cd_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | CF =>
    dsimp [apply_move]
    unfold cf_move_corner_perm
    unfold cf_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide
  | CB =>
    dsimp [apply_move]
    unfold cb_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_corner_perm
    unfold rotY_corner_perm
    unfold cf_move_corner_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    unfold cb_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_inv]
    unfold rotY2_center_perm
    unfold rotY_center_perm
    unfold cf_move_center_perm
    simp_rw [Perm.sign_mul]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    rw [Perm.sign_swap, Perm.sign_swap, Perm.sign_swap]
    · simp
    all_goals try decide

theorem moves_corner_center_sign_invariant (moves : List BasicMove) (s : CubeState) :
    Perm.sign s.corner_perm * Perm.sign s.center_perm =
    Perm.sign (apply_move_list moves s).corner_perm *
    Perm.sign (apply_move_list moves s).center_perm := by
  induction moves using List.reverseRecOn with
  | nil => rw [apply_move_list]; rfl
  | append_singleton ms  ih =>
    rw [apply_move_list, List.foldl_append]
    simp_all only [forall_const, List.foldl_cons, List.foldl_nil]
    apply move_corner_center_sign_invariant

/-- Lemma 2 (Ref. Lemma 3.1): The product of corner and center permutation signs
    is invariant under solvable moves. -/
theorem lemma2_sign_invariant (s : CubeState) (hs : IsSolvable s) :
    Perm.sign s.corner_perm * Perm.sign s.center_perm = 1 := by
  let ⟨moves, h⟩ := hs
  rw [h, ← moves_corner_center_sign_invariant, one_corner_center_sign_invariant]


open BasicMove -- For BasicMove notation

def fixed_corner_3_cycle_seq : List BasicMove :=
  r' ++ d' ++ r ++ u' ++ r' ++ d ++ r ++ u

-- 2. Define the target permutation
-- Cycle URF(1) -> URB(2) -> ULB(3) -> URF(1)
-- This is swap 1 3 * swap 1 2
def target_corner_perm : Perm CornerSlot :=
  Equiv.cycle c_urf c_ufl c_drf

-- 3. State and try to prove the corner permutation equality using decide
-- This requires apply_move to be fully defined for R, U, D without sorry
example : (apply_move_list fixed_corner_3_cycle_seq initialState).corner_perm = target_corner_perm := by
  native_decide -- Use native_decide for potentially faster computation

-- 4. State the full lemma (still likely needs sorry for other parts)
theorem fixed_corner_3_cycle_seq_effect :
    ∃ (s : CubeState), s = apply_move_list fixed_corner_3_cycle_seq 1 ∧
                       IsSolvable s ∧
                       s.corner_perm = target_corner_perm ∧
                       s.edge_perm = 1 ∧
                       s.center_perm = 1 ∧
                       s.edge_ori = fun _ => 0 := by
  -- Define the state
  let s := apply_move_list fixed_corner_3_cycle_seq initialState
  use s
  -- Prove the properties
  constructor
  · -- Proof of s = apply_move_list ...
    rfl
  · constructor
    · -- Proof of IsSolvable s
      use fixed_corner_3_cycle_seq; rfl
    · constructor
      · -- Proof of s.corner_perm = target_corner_perm
        -- Try to compute and check equality
        native_decide -- If this works, the corner perm is correct
        -- If native_decide fails, replace with sorry
        -- sorry
      · constructor
        · -- Proof of s.edge_perm = 1
          -- Requires computing the edge permutation product
          native_decide --might work here too if apply_move is complete
        · constructor
          · -- Proof of s.center_perm = 1
            -- Requires computing the center permutation product
            native_decide --might work here too
          · -- Proof of s.edge_ori = fun _ => 0
            -- Requires computing the final edge_ori function
            native_decide -- Needs funext and calculation based on apply_move


-- Lemma asserting the existence of setup moves 'g' such that the conjugate g*m*g⁻¹
-- performs the desired 3-cycle (i j k) while preserving other piece types / edge orientations.
-- This relies on the properties of the Rubik's group G₄.
theorem corner_conjugation_works (i j k : CornerSlot)
    (h_distinct : i ≠ j ∧ i ≠ k ∧ j ≠ k) :
    ∃ (g : Moves), -- The setup moves 'g'
      ∃ (s_conj : CubeState), -- The state after applying g * m * g⁻¹
         s_conj = apply_move_list (g ++ fixed_corner_3_cycle_seq ++ inv_move_list g) 1 ∧
         IsSolvable s_conj ∧
         s_conj.corner_perm = (Equiv.cycle i j k) ∧ -- The desired 3-cycle
         s_conj.edge_perm = 1 ∧
         s_conj.center_perm = 1 ∧
         s_conj.edge_ori = fun _ => 0 :=
  sorry -- This axiom encapsulates the conjugation principle for pure corner 3-cycles


/-- Consequence of Lemma 3 (C ≅ A₈): Any even permutation of corners can be achieved
    by a solvable state that doesn't permute other pieces or affect edge orientation. -/
theorem lemma3_corner_perm_achievability (σ_target : Perm CornerSlot)
    (h_even : Perm.sign σ_target = 1) :
    ∃ (s : CubeState), IsSolvable s ∧
                       s.corner_perm = σ_target ∧
                       s.edge_perm = 1 ∧
                       s.center_perm = 1 ∧
                       s.edge_ori = fun _ => 0 :=
  sorry -- Proof relies on group theory and commutators generating A₈.

/-- Consequence of Lemma 4 (Z ≅ A₂₄): Any even permutation of centers can be achieved
    by a solvable state that doesn't permute other pieces or affect edge orientation. -/
theorem lemma4_center_perm_achievability (ρ_target : Perm CenterSlot)
    (h_even : Perm.sign ρ_target = 1) :
    ∃ (s : CubeState), IsSolvable s ∧
                       s.center_perm = ρ_target ∧
                       s.corner_perm = 1 ∧
                       s.edge_perm = 1 ∧
                       s.edge_ori = fun _ => 0 :=
  sorry -- Proof relies on group theory and commutators generating A₂₄.

/-- Consequence of Lemma 5 (E ≅ S₂₄): Any permutation of edges can be achieved
    by a solvable state that doesn't permute other pieces.
    (Note: This state *will* generally affect edge orientations according to Condition 3). -/
theorem lemma5_edge_perm_achievability (τ_target : Perm EdgeSlot) :
    ∃ (s : CubeState), IsSolvable s ∧
                       s.edge_perm = τ_target ∧
                       s.corner_perm = 1 ∧
                       s.center_perm = 1 :=
  sorry -- Proof relies on group theory and commutators generating S₂₄.

/-- Lemma 6 (Implied by paper): A state with identity permutations and zero edge
    orientation, satisfying the corner twist condition, is solvable. -/
theorem lemma6_corner_twist_solvability (s : CubeState)
    (h_perm : s.corner_perm = 1 ∧ s.edge_perm = 1 ∧ s.center_perm = 1)
    (h_edge_ori : s.edge_ori = fun _ => 0)
    (h_twist : checkCornerTwist s) :
    IsSolvable s :=
  sorry -- Proof relies on existence of pure corner twist algorithms.

/-!
## Proof of Edge Flip Invariance (Condition 3)
-/

-- Step 1: Show the initial state satisfies the condition.
theorem lemma7_step1_initial_state : checkEdgeFlip 1 := by
  show checkEdgeFlip initialState
  intro i
  -- Add Perm.one_apply (or just one_apply if Equiv is open) to the simp list
  simp only [initialState, getPieceTypeInSlot, checkEdgeFlip, edgeDelta, inv_one, Perm.one_apply]
  -- Goal should now be: 0 = 1 - if getSlotType i = getSlotType i then 1 else 0
  -- Now this simp call should work
  simp only [eq_self, if_true, sub_self]

theorem r_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move R s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem l_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move L s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem u_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move U s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem d_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move D s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem f_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move F s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : f_move_edge_perm⁻¹ i ∈ f_slice_edges
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem b_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move B s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : rotY2_edge_perm⁻¹ i ∈ f_slice_edges
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem cr_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move CR s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : cr_move_edge_perm⁻¹ i ∈ cr_slice_edges_a || cr_move_edge_perm⁻¹ i ∈ cr_slice_edges_b
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem cl_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move CL s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : rotY2_edge_perm⁻¹ i ∈ cr_slice_edges_a || rotY2_edge_perm⁻¹ i ∈ cr_slice_edges_b
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem cu_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move CU s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : cu_move_edge_perm⁻¹ i ∈ cu_slice_edges_a || cu_move_edge_perm⁻¹ i ∈ cu_slice_edges_b
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem cd_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move CD s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : cd_move_edge_perm⁻¹ i ∈ cd_slice_edges
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem cf_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move CF s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : cf_move_edge_perm⁻¹ i ∈ cf_slice_edges
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

theorem cb_move_check_edge_flip (s: CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move CB s) := by
  intro he i
  rw [getSlotType, getPieceTypeInSlot, getSlotType]
  by_cases p : rotY2_edge_perm⁻¹ i ∈ cf_slice_edges
  <;> split_ifs with h₁ h₂ h₃
  <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
  <;> simp_all [apply_move]
  <;> rw [he]
  <;> fin_cases i
  <;> simp_all [edgeDelta, getPieceTypeInSlot, getSlotType]
  <;> decide

-- Step 2: Show that applying any move preserves the edge flip condition.
-- This is the most complex invariance proof.
theorem lemma7_step2_move_invariance (m : BasicMove) (s : CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move m s) := by
  match m with
  | R => exact r_move_check_edge_flip s
  | L => exact l_move_check_edge_flip s
  | U => exact u_move_check_edge_flip s
  | D => exact d_move_check_edge_flip s
  | F => exact f_move_check_edge_flip s
  | B => exact b_move_check_edge_flip s
  | CR => exact cr_move_check_edge_flip s
  | CL => exact cl_move_check_edge_flip s
  | CU => exact cu_move_check_edge_flip s
  | CD => exact cd_move_check_edge_flip s
  | CF => exact cf_move_check_edge_flip s
  | CB => exact cb_move_check_edge_flip s



/-- Lemma 7: The edge flip condition `checkEdgeFlip` is invariant under solvable moves. -/
theorem moves_preserves_checkEdgeFlip (moves : List BasicMove) (s : CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move_list moves s) := by
  induction moves using List.reverseRecOn with
  | nil => intro h; exact h
  | append_singleton ms m ih =>
    intro h
    rw [apply_move_list, List.foldl_append]
    simp_all only [forall_const, List.foldl_cons, List.foldl_nil]
    apply move_check_edge_flip
    exact ih

/-- Lemma 7: The edge flip condition `checkEdgeFlip` is invariant under solvable moves. -/
theorem lemma7_edge_flip_invariant (s : CubeState) (hs : IsSolvable s) :
    checkEdgeFlip s := by
  obtain ⟨moves, hm⟩ := hs
  rw [hm]
  exact moves_preserves_checkEdgeFlip moves 1 (one_check_edge_flip)


lemma apply_move_list_inv_move_cancel (m : BasicMove) (s : CubeState) :
    apply_move_list (inv_move m) (apply_move m s) = s := by
  simp only [inv_move, apply_move_list, List.foldl_cons, List.foldl_nil]
  -- Goal: apply_move m (apply_move m (apply_move m (apply_move m s))) = s
  -- This requires proving that (apply_move m)^4 = id
  sorry -- Placeholder for proof that apply_move^4 = id

-- Lemma: apply_move_list distributes over concatenation (from right)
lemma apply_move_list_append (L1 L2 : List BasicMove) (s : CubeState) :
    apply_move_list (L1 ++ L2) s = apply_move_list L2 (apply_move_list L1 s) := by
  -- Proof by induction on L1, using properties of foldl
  induction L1 generalizing s with
  | nil => -- Base case: L1 = []
    -- Goal: apply_move_list ([] ++ L2) s = apply_move_list L2 (apply_move_list [] s)
    simp only [
        List.nil_append, -- Simplifies LHS: [] ++ L2 = L2
        apply_move_list, -- Unfolds apply_move_list on RHS
        List.foldl_nil   -- Simplifies apply_move_list [] s = s
      ]
    -- Goal after simp: apply_move_list L2 s = apply_move_list L2 s

  | cons m ms ih => -- Inductive step for move 'm' and remaining list 'ms'
    -- Goal: apply_move_list (m :: (ms ++ L2)) s = apply_move_list L2 (apply_move_list (m :: ms) s)
    -- Simplify both sides using the definition and foldl properties
    simp only [apply_move_list, List.foldl_cons, List.cons_append]
    -- Goal is now:
    -- apply_move_list (ms ++ L2) (apply_move m s) = apply_move_list L2 (apply_move_list ms (apply_move m s))
    -- This matches the inductive hypothesis applied to the state (apply_move m s)
    exact ih (apply_move m s)

theorem isSolvable_of_apply_move_solvable (m : BasicMove) (s : CubeState) :
    IsSolvable (apply_move m s) → IsSolvable s := by
  intro h_solv_ms
  obtain ⟨M, h_eq⟩ := h_solv_ms
  -- Propose the sequence derived from the calculation
  use (M ++ inv_move m) -- Changed order here!
  -- Goal: s = apply_move_list (M ++ inv_move m) initialState

  -- Start with the cancellation property for s
  have h_cancel : s = apply_move_list (inv_move m) (apply_move m s) :=
    (apply_move_list_inv_move_cancel m s).symm

  -- Substitute the assumption h_eq into h_cancel
  rw [h_eq] at h_cancel
  -- h_cancel is now: s = apply_move_list (inv_move m) (apply_move_list M initialState)

  -- Apply the append lemma BACKWARDS to the RHS of h_cancel
  rw [← apply_move_list_append] at h_cancel
  -- h_cancel is now: s = apply_move_list (M ++ inv_move m) initialState

  -- This is exactly the goal
  exact h_cancel

-- Need helper lemma: apply_move_list [m] s = apply_move m s
lemma apply_move_list_singleton (m : BasicMove) (s : CubeState) :
  apply_move_list [m] s = apply_move m s := by
  simp [apply_move_list, List.foldl_cons, List.foldl_nil]


theorem solvability_iff_apply_move (m : BasicMove) (s : CubeState) :
    IsSolvable (apply_move m s) ↔ IsSolvable s := by
  constructor
  · exact isSolvable_of_apply_move_solvable m s
  · -- Proof for IsSolvable s → IsSolvable (apply_move m s)
    intro h_solv_s
    obtain ⟨M, h_s_eq⟩ := h_solv_s
    use (M ++ [m]) -- Propose new move list
    rw [apply_move_list_append, h_s_eq, apply_move_list_singleton]



-- ## Main Solvability Theorem Statement
#check Equiv.Perm.sign
#check ℤˣ

theorem solvability_iff (s : CubeState) :
    IsSolvable s ↔ checkPermSigns s ∧ checkCornerTwist s ∧ checkEdgeFlip s := by
  constructor
  · -- Direction "=>": If a state is solvable, it must satisfy the conditions.
    intro h_solv -- Assume s is solvable: ∃ moves, s = apply_move_list moves initialState

    -- Prove Condition 1: checkPermSigns s
    -- We use Lemma 2 (sign product invariant)
    have h_sign_prod : Perm.sign s.corner_perm * Perm.sign s.center_perm = 1 :=
      lemma2_sign_invariant s h_solv
    -- We need to show permSign s.corner_perm = permSign s.center_perm
    -- This follows because for a, b ∈ {-1, 1}, a*b=1 implies a=b
    have h_sign_eq : checkPermSigns s := by
      sorry
      -- Prove Condition 2: checkCornerTwist s
    have h_twist : checkCornerTwist s :=
      lemma1_corner_twist_invariant s h_solv -- Use Lemma 1

    -- Prove Condition 3: checkEdgeFlip s
    have h_edge : checkEdgeFlip s :=
      lemma7_edge_flip_invariant s h_solv -- Use Lemma 7

    -- Combine the three proven conditions
    exact ⟨h_sign_eq, h_twist, h_edge⟩






  · -- Direction "<=": If a state satisfies the conditions, it is solvable.
    intro h_conditions
    let ⟨h_sign_s, h_twist_s, h_edge_s⟩ := h_conditions

    -- Step 1: Ensure center permutation ρ is even
    -- Define s₁ based on the sign of s.center_perm
    let s₁ : CubeState := if h_center_even : Perm.sign s.center_perm = 1 then s else apply_move BasicMove.R s
    -- We split the proof based on this 'if' statement using 'dite' (dependent if-then-else)

    -- Prove properties about s₁
    have h_s₁_solvable_rel : IsSolvable s → IsSolvable s₁ := by
      intro hs_solv -- Assume IsSolvable s
      -- Case split on the condition used to define s₁
      by_cases h_center_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: Center permutation is even
        -- We need to show IsSolvable s₁
        -- Use the definition of s₁ in this case
        have h_s₁_def : s₁ = s := if_pos h_center_even
        rw [h_s₁_def] -- Replace s₁ with s in the goal
        exact hs_solv -- The goal is now IsSolvable s, which we assumed
      · -- Case 2: Center permutation is odd
        -- We need to show IsSolvable s₁
        -- Use the definition of s₁ in this case
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_center_even
        rw [h_s₁_def] -- Replace s₁ with apply_move R s in the goal
        -- Goal is IsSolvable (apply_move R s)
        -- Use the forward direction of solvability_iff_apply_move
        apply (solvability_iff_apply_move BasicMove.R s).mpr
        exact hs_solv -- We assumed IsSolvable s

    have h_center_perm_even₁ : Perm.sign s₁.center_perm = 1 := by
      -- Use by_cases to split on the condition used to define s₁
      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true
        -- In this case, s₁ was defined as s
        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def] -- Substitute s₁ with s
        exact h_rho_even -- The goal is now permSign s.center_perm = 1, which is h_rho_even
      · -- Case 2: permSign s.center_perm = 1 is false (so sign must be -1)
        -- In this case, s₁ was defined as apply_move R s
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def] -- Substitute s₁
        simp only [apply_move, MoveImpl.apply_move] -- Unfold apply_move for R case
        -- Goal: permSign (r_move_center_perm * s.center_perm) = 1
        rw [Perm.sign_mul] -- sign(p*q) = sign(p)*sign(q)
        have h_r_sign : Perm.sign r_move_center_perm = -1 := by
             native_decide -- Or sorry
        rw [h_r_sign]
        -- Goal: -1 * permSign s.center_perm = 1
        -- Prove that permSign s.center_perm must be -1
        have h_s_sign : Perm.sign s.center_perm = -1 := by
          -- Use the lemma stating sign is a unit (1 or -1)
          -- Perm.sign_mem_units returns a proof that sign p ∈ ({1, -1} : Set (Multiplicative ℤ))
          -- We can use this membership proof with the fact it's not 1
          have h_mem := Perm.sign_mem_units s.center_perm
          -- Unfold the definition of the set {1, -1}
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_mem
          -- h_mem is now: permSign s.center_perm = 1 ∨ permSign s.center_perm = -1
          -- We know it's not 1 from h_rho_even
          exact Or.resolve_left h_mem h_rho_even -- Conclude it must be -1
        rw [h_s_sign]
        -- Goal: -1 * -1 = 1
        simp -- Should solve this
        -- rfl -- Alternative


    have h_sign₁ : checkPermSigns s₁ := by
      split_ifs with h_rho_even
      · -- Case 1: s₁ = s
        exact h_sign_s -- Use original assumption
      · -- Case 2: s₁ = apply_move R s
        simp only [s₁, checkPermSigns, apply_move] -- Unfold definitions
        simp only -- Access components
        -- Goal: sign(r_p_c * s_p_c) = sign(r_p_z * s_p_z)
        rw [Perm.sign_mul, Perm.sign_mul]
        have h_r_c_sign : permSign r_move_corner_perm = -1 := by sorry -- Sign of 4-cycle
        have h_r_z_sign : permSign r_move_center_perm = -1 := by sorry -- Sign of 4-cycle
        rw [h_r_c_sign, h_r_z_sign]
        -- Goal: -1 * sign(s_p_c) = -1 * sign(s_p_z)
        -- We know sign(s_p_c) = sign(s_p_z) from h_sign_s
        rw [h_sign_s]

    have h_twist₁ : checkCornerTwist s₁ := by
      split_ifs with h_rho_even
      · -- Case 1: s₁ = s
        exact h_twist_s -- Use original assumption
      · -- Case 2: s₁ = apply_move R s
        simp only [s₁]
        exact lemma1_step2_move_invariance BasicMove.R s h_twist_s -- Use Lemma 1 invariance

    have h_edge₁ : checkEdgeFlip s₁ := by
      split_ifs with h_rho_even
      · -- Case 1: s₁ = s
        exact h_edge_s -- Use original assumption
      · -- Case 2: s₁ = apply_move R s
        simp only [s₁]
        exact lemma7_step2_move_invariance BasicMove.R s h_edge_s -- Use Lemma 7 invariance

    -- Now continue with Step 2 using s₁, h_center_perm_even₁, h_sign₁, h_twist₁, h_edge₁
    -- ... rest of the proof ...
    sorry

end FourRubik
