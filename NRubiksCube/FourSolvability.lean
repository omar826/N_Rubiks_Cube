import Mathlib.GroupTheory.Perm.Sign -- For Equiv.Perm.sign
import Mathlib.Data.Fintype.Basic    -- For Fintype instances
--import Mathlib.Algebra.BigOperators.Basic -- For Finset.sum
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating -- For AlternatingGroup definition Aₙ
--import Mathlib.GroupTheory.SpecificGroups.Symmetric -- For SymmetricGroup definition Sₙ
import Mathlib.Data.List.Induction
import NRubiksCube.FourRubik -- Assuming your main file is named FourRubik.lean

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
  if slot.val % 2 = 0 then Orientation.EdgeType.A else Orientation.EdgeType.B

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


-- ## Main Solvability Theorem Statement

theorem solvability_iff (s : CubeState) :
    IsSolvable s ↔ checkPermSigns s ∧ checkCornerTwist s ∧ checkEdgeFlip s := by
  -- Proof is substantial and relies on group theory, commutators, and invariants.
  sorry

end FourRubik
