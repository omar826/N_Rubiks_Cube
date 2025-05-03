import Mathlib.GroupTheory.Perm.Sign -- For Equiv.Perm.sign
import Mathlib.Data.Fintype.Basic    -- For Fintype instances
--import Mathlib.Algebra.BigOperators.Basic -- For Finset.sum
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating -- For AlternatingGroup definition Aₙ
--import Mathlib.GroupTheory.SpecificGroups.Symmetric -- For SymmetricGroup definition Sₙ
import Mathlib.Data.List.Induction
import NRubiksCube.FourRubik -- Assuming your main file is named FourRubik.lean

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

-- Lemma stating the effect of the fixed 3-cycle sequence 'm'
-- NOTE: The specific cycle (c_urf c_urb c_ulb) needs to be verified for this sequence!
theorem fixed_corner_3_cycle_seq_effect :
    ∃ (s : CubeState), s = apply_move_list fixed_corner_3_cycle_seq 1 ∧
                       IsSolvable s ∧
                       s.corner_perm = Equiv.cycle c_urf c_urb c_ulb ∧ -- Assumed cycle
                       s.edge_perm = 1 ∧
                       s.center_perm = 1 ∧
                       s.edge_ori = fun _ => 0 :=
  sorry -- Requires proving the effect of the specific sequence 'm'

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
theorem one_check_edge_flip : checkEdgeFlip 1 := by
  show checkEdgeFlip initialState
  intro i
  -- Add Perm.one_apply (or just one_apply if Equiv is open) to the simp list
  simp only [initialState, getPieceTypeInSlot, checkEdgeFlip, edgeDelta, inv_one, Perm.one_apply]
  -- Goal should now be: 0 = 1 - if getSlotType i = getSlotType i then 1 else 0
  -- Now this simp call should work
  simp only [eq_self, if_true, sub_self]

-- Step 2: Show that applying any move preserves the edge flip condition.
-- This is the most complex invariance proof.
theorem move_check_edge_flip (m : BasicMove) (s : CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move m s) := by
  intro h_edge_flip -- Assume ∀ (j : EdgeSlot), s.edge_ori j = 1 - edgeDelta (getSlotType j) (getPieceTypeInSlot s j)
  intro i -- Goal: (apply_move m s).edge_ori i = 1 - edgeDelta (getSlotType i) (getPieceTypeInSlot (apply_move m s) i)
  -- Unfold the definition of s'.edge_ori from apply_move
  -- Need to use cases on m or the apply_move_internal structure
  -- Let p_e be the edge permutation for move m, d_e be the edge delta for move m
  -- s'.edge_ori i = s.edge_ori (p_e⁻¹ i) + d_e (p_e⁻¹ i)
  -- Goal: s.edge_ori (p_e⁻¹ i) + d_e (p_e⁻¹ i) = 1 - edgeDelta (getSlotType i) (getPieceTypeInSlot s' i)

  -- This requires relating getPieceTypeInSlot s' i to getPieceTypeInSlot s (p_e⁻¹ i)
  -- and analyzing how d_e interacts with the edgeDelta formula.
  -- This proof is highly non-trivial and depends heavily on the exact permutations
  -- and the definition of edge flip delta for slice moves.
  match m with
  | R =>
    rw [getSlotType, getPieceTypeInSlot, getSlotType]
    split_ifs with h₁ h₂ h₃
    <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
    <;> simp_all [apply_move]
    · rw [h_edge_flip (r_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (r_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (r_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₂]
      apply if_pos
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (r_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (r_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (r_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₂]
      simp only [Fin.isValue, ite_eq_right_iff, reduceCtorEq, imp_false, Decidable.not_not]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (r_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (r_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (r_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₃]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (r_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (r_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (r_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₃]
      fin_cases i
      <;> simp_all <;> decide
  | L =>
    rw [getSlotType, getPieceTypeInSlot, getSlotType]
    split_ifs with h₁ h₂ h₃
    <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
    <;> simp_all [apply_move]
    · rw [h_edge_flip (l_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (l_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (l_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₂]
      apply if_pos
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (l_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (l_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (l_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₂]
      simp only [Fin.isValue, ite_eq_right_iff, reduceCtorEq, imp_false, Decidable.not_not]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (l_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (l_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (l_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₃]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (l_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (l_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (l_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₃]
      fin_cases i
      <;> simp_all <;> decide
  | U =>
    rw [getSlotType, getPieceTypeInSlot, getSlotType]
    split_ifs with h₁ h₂ h₃
    <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
    <;> simp_all [apply_move]
    · rw [h_edge_flip (u_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (u_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (u_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₂]
      apply if_pos
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (u_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (u_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (u_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₂]
      simp only [Fin.isValue, ite_eq_right_iff, reduceCtorEq, imp_false, Decidable.not_not]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (u_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (u_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (u_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₃]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (u_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (u_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (u_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₃]
      fin_cases i
      <;> simp_all <;> decide
  | D =>
    rw [getSlotType, getPieceTypeInSlot, getSlotType]
    split_ifs with h₁ h₂ h₃
    <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
    <;> simp_all [apply_move]
    · rw [h_edge_flip (d_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (d_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (d_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₂]
      apply if_pos
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (d_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (d_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (d_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₂]
      simp only [Fin.isValue, ite_eq_right_iff, reduceCtorEq, imp_false, Decidable.not_not]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (d_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (d_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (d_move_edge_perm⁻¹ i)) = 0 by
        rw [this]
        simp
      rw [edgeDelta, if_neg]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_pos h₃]
      fin_cases i
      <;> simp_all <;> decide
    · rw [h_edge_flip (d_move_edge_perm⁻¹ i)]
      suffices edgeDelta (getSlotType (d_move_edge_perm⁻¹ i))
          (getPieceTypeInSlot s (d_move_edge_perm⁻¹ i)) = 1 by
        rw [this]
        simp
      rw [edgeDelta, if_pos]
      rw [getPieceTypeInSlot]
      rw [getSlotType, getSlotType]
      rw [if_neg h₃]
      fin_cases i
      <;> simp_all <;> decide
  | F =>
    rw [getSlotType, getPieceTypeInSlot, getSlotType]
    split_ifs with h₁ h₂ h₃
    <;> simp only [edgeDelta, reduceCtorEq, ↓reduceIte, sub_zero, sub_self]
    <;> simp_all [apply_move]
    · rw [h_edge_flip (f_move_edge_perm⁻¹ i)]
      by_cases p : f_move_edge_perm⁻¹ i ∈ f_slice_edges
      · sorry
      · rw [f_move_edge_ori_delta, if_neg p]
        suffices edgeDelta (getSlotType (f_move_edge_perm⁻¹ i))
            (getPieceTypeInSlot s (f_move_edge_perm⁻¹ i)) = 1 by
          rw [this]
          simp
        rw [edgeDelta, if_pos]
        rw [getPieceTypeInSlot]
        rw [getSlotType, getSlotType]
        rw [if_pos h₂]
        apply if_pos
        fin_cases i
        <;> simp_all <;> try decide
        · exfalso
          simp [f_slice_edges] at p
          rcases p with ⟨_, _, _, _, _, _, _, h_ne_9⟩
          apply h_ne_9
          decide
        · sorry
        · sorry
        · sorry
    · sorry
    · sorry
  | B => sorry
  | CR => sorry
  | CL => sorry
  | CU => sorry


/-- Lemma 7: The edge flip condition `checkEdgeFlip` is invariant under solvable moves. -/

theorem moves_preserves_checkEdgeFlip (moves : List BasicMove) (s : CubeState) :
    checkEdgeFlip s → checkEdgeFlip (apply_move_list moves s) := by
  induction moves generalizing s with
  | nil => -- Base case
    intro h
    simp only [apply_move_list, List.foldl_nil]
    exact h
  | cons m ms ih => -- Inductive step
    intro h
    -- Use List.foldl_cons to unfold apply_move_list for the cons case
    simp only [apply_move_list, List.foldl_cons]
    -- Goal is now: checkEdgeFlip (List.foldl (fun s m' => apply_move m' s) (apply_move m s) ms)
    -- which is definitionally checkEdgeFlip (apply_move_list ms (apply_move m s))
    -- We need to show checkEdgeFlip holds for the state *after* move m
    apply ih -- Apply the inductive hypothesis to the remaining list 'ms'
    -- The goal for ih is checkEdgeFlip (apply_move m s)
    -- This requires the single-move invariance lemma
    apply lemma7_step2_move_invariance m s
    -- The final goal is checkEdgeFlip s, which is our assumption
    exact h

/-- Lemma 7: The edge flip condition `checkEdgeFlip` is invariant under solvable moves. -/
theorem lemma7_edge_flip_invariant (s : CubeState) (h_solv : IsSolvable s) :
    checkEdgeFlip s := by
  obtain ⟨moves, h_s_eq⟩ := h_solv -- Get the move list from the IsSolvable definition
  rw [h_s_eq] -- Substitute s with apply_move_list moves initialState
  -- Apply the helper lemma, starting from initialState
  apply moves_preserves_checkEdgeFlip moves 1
  -- The remaining goal is checkEdgeFlip initialState
  exact lemma7_step1_initial_state -- Use the base case proof


-- ## Main Solvability Theorem Statement

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
      simp only [checkPermSigns] -- Goal: Perm.sign s.corner_perm = Perm.sign s.center_perm
      -- Let a := Perm.sign s.corner_perm
      -- Let b := Perm.sign s.center_perm
      -- h_sign_prod : a * b = 1
      -- We want a = b
      -- Apply `a` (Perm.sign s.corner_perm) to both sides of `h_sign_prod`
      have h_sign_eq : checkPermSigns s := by
        simp only [checkPermSigns] -- Goal: Perm.sign s.corner_perm = Perm.sign s.center_perm
        -- h_sign_prod : Perm.sign s.corner_perm * Perm.sign s.center_perm = 1
        -- Use a * b = 1 ↔ a = b⁻¹
        rw [← mul_eq_one_iff_eq_inv] at h_sign_prod
        -- Goal is now Perm.sign s.corner_perm = Perm.sign s.center_perm
        -- h_sign_prod is now Perm.sign s.corner_perm = (Perm.sign s.center_perm)⁻¹
        -- We need to show (Perm.sign s.center_perm)⁻¹ = Perm.sign s.center_perm
        rw [h_sign_prod] -- Substitute a = b⁻¹ into the goal a = b
        -- Goal is now: (Perm.sign s.center_perm)⁻¹ = Perm.sign s.center_perm
        apply Units.inv_eq_self_iff.mpr -- Use the lemma for units {+1, -1}
        -- The remaining goal is to show Perm.sign s.center_perm is either 1 or -1
        exact Perm.sign_eq_one_or_neg_one _
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
    -- Proof outline using lemmas 3, 4, 5, 6...
    sorry

end FourRubik
