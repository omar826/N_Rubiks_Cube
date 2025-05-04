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

theorem one_check_perm_signs : checkPermSigns 1 := by
  unfold checkPermSigns
  decide

theorem move_check_perm_signs (m : BasicMove) (s : CubeState) :
    checkPermSigns s → checkPermSigns (apply_move m s) := by
  intro h
  unfold checkPermSigns at *
  cases m with
  | R =>
    dsimp [apply_move, r_move_corner_perm, r_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | L =>
    dsimp [apply_move, l_move_corner_perm, l_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [r_move_corner_perm, r_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | U =>
    dsimp [apply_move, u_move_corner_perm, u_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | D =>
    dsimp [apply_move, d_move_corner_perm, d_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | F =>
    dsimp [apply_move, f_move_corner_perm, f_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | B =>
    dsimp [apply_move, b_move_corner_perm, b_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [f_move_corner_perm, f_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | CR =>
    dsimp [apply_move, cr_move_corner_perm, cr_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | CL =>
    dsimp [apply_move, cl_move_corner_perm, cl_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [cr_move_corner_perm, cr_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | CU =>
    dsimp [apply_move, cu_move_corner_perm, cu_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | CD =>
    dsimp [apply_move, cd_move_corner_perm, cd_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | CF =>
    dsimp [apply_move, cf_move_corner_perm, cf_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]
  | CB =>
    dsimp [apply_move, cb_move_corner_perm, cb_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [cf_move_corner_perm, cf_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp [h]

theorem moves_check_perm_signs (moves : List BasicMove) (s : CubeState) :
    checkPermSigns s → checkPermSigns (apply_move_list moves s) := by
  induction moves using List.reverseRecOn with
  | nil => intro h; exact h
  | append_singleton ms m ih =>
    intro h
    rw [apply_move_list, List.foldl_append]
    simp_all only [forall_const, List.foldl_cons, List.foldl_nil]
    apply move_check_perm_signs
    exact ih

theorem is_solvable_check_perm_signs (s : CubeState) (hs : IsSolvable s) :
    checkPermSigns s := by
  let ⟨moves, h⟩ := hs
  rw [h]
  exact moves_check_perm_signs moves 1 one_check_perm_signs

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
    dsimp [apply_move, r_move_corner_perm, r_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | L =>
    dsimp [apply_move, l_move_corner_perm, l_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [r_move_corner_perm, r_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | U =>
    dsimp [apply_move, u_move_corner_perm, u_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | D =>
    dsimp [apply_move, d_move_corner_perm, d_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | F =>
    dsimp [apply_move, f_move_corner_perm, f_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | B =>
    dsimp [apply_move, b_move_corner_perm, b_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [f_move_corner_perm, f_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | CR =>
    dsimp [apply_move, cr_move_corner_perm, cr_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | CL =>
    dsimp [apply_move, cl_move_corner_perm, cl_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [cr_move_corner_perm, cr_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | CU =>
    dsimp [apply_move, cu_move_corner_perm, cu_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | CD =>
    dsimp [apply_move, cd_move_corner_perm, cd_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | CF =>
    dsimp [apply_move, cf_move_corner_perm, cf_move_center_perm]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp
  | CB =>
    dsimp [apply_move, cb_move_corner_perm, cb_move_center_perm]
    dsimp [rotY2_corner_perm, rotY_corner_perm, rotY2_center_perm, rotY_center_perm]
    dsimp [cf_move_corner_perm, cf_move_center_perm]
    simp_rw [Perm.sign_mul, Perm.sign_inv]
    simp_rw [Perm.sign_mul]
    repeat (rw [Perm.sign_swap] <;> try decide)
    simp


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
    IsSolvable s := by
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
    apply lemma7_step2_move_invariance
    exact ih

/-- Lemma 7: The edge flip condition `checkEdgeFlip` is invariant under solvable moves. -/
theorem lemma7_edge_flip_invariant (s : CubeState) (hs : IsSolvable s) :
    checkEdgeFlip s := by
  obtain ⟨moves, hm⟩ := hs
  rw [hm]
  exact moves_preserves_checkEdgeFlip moves 1 lemma7_step1_initial_state

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

lemma apply_move_list_inv_move_cancel (m : BasicMove) (s : CubeState) :
    apply_move_list (inv_move m) (apply_move m s) = s := by
  simp only [inv_move, apply_move_list, List.foldl_cons, List.foldl_nil]
  -- Goal: apply_move m (apply_move m (apply_move m (apply_move m s))) = s
  -- This requires proving that (apply_move m)^4 = id
  sorry -- Placeholder for proof that apply_move^4 = id

lemma apply_move_list_inv_move_list_cancel (M : List BasicMove) (s : CubeState) :
    apply_move_list (inv_move_list M) (apply_move_list M s) = s := by
  induction M generalizing s with
  | nil =>
    simp only [inv_move_list, List.reverse_nil, List.map_nil, List.flatten_nil, apply_move_list, List.foldl_nil]
  | cons m ms ih =>
    -- ih : ∀ (s' : CubeState), apply_move_list (inv_move_list ms) (apply_move_list ms s') = s'

    -- Goal: apply_move_list (inv_move_list (m :: ms)) (apply_move_list (m :: ms) s) = s
    have h_inv_list_cons : inv_move_list (m :: ms) = inv_move_list ms ++ inv_move m := by
      simp [inv_move_list, List.reverse_cons, List.map_append, List.flatten_append]
    rw [h_inv_list_cons]
    -- Goal: apply_move_list (inv_move_list ms ++ inv_move m) (apply_move_list (m :: ms) s) = s

    -- Unfold the target state definition
    simp only [apply_move_list, List.foldl_cons]
    -- Goal: apply_move_list (inv_move_list ms ++ inv_move m) (apply_move_list ms (apply_move m s)) = s

    -- Apply append lemma (make sure it's defined *before* this lemma)
    -- Using: apply_move_list (L1 ++ L2) s' = apply_move_list L2 (apply_move_list L1 s')
    -- Let L1 = inv_move_list ms, L2 = inv_move m, s' = apply_move_list ms (apply_move m s)
    rw [List.foldl_append]
    -- Goal: apply_move_list (inv_move m) (apply_move_list (inv_move_list ms) (apply_move_list ms (apply_move m s))) = s

    -- *** Here is the change ***
    -- Define the intermediate state explicitly
    let s' := apply_move m s
    -- Specialize the inductive hypothesis to this state s'
    specialize ih s'
    -- Now ih : apply_move_list (inv_move_list ms) (apply_move_list ms s') = s'
    simp only [apply_move_list] at ih
    -- Rewrite the inner part using the specialized hypothesis 'ih'
    -- The term `apply_move_list (inv_move_list ms) (apply_move_list ms (apply_move m s))`
    -- is `apply_move_list (inv_move_list ms) (apply_move_list ms s')` which is the LHS of ih.
    rw [ih] -- Use the specialized equality ih
    -- Goal: apply_move_list (inv_move m) s' = s
    -- If the goal doesn't immediately simplify, substitute s' back
    -- change apply_move_list (inv_move m) (apply_move m s) = s -- This might not be needed

    -- The goal is now exactly the single-move cancellation lemma
    exact apply_move_list_inv_move_cancel m s


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

/-- Applying a sequence of moves to a solvable state results in a solvable state. -/
theorem isSolvable_apply_move_list (M : List BasicMove) (s : CubeState) :
    IsSolvable s → IsSolvable (apply_move_list M s) := by
  intro h_s_solv              -- Assume `s` is solvable
  obtain ⟨M_s, h_s_eq⟩ := h_s_solv -- Get the move list `M_s` such that `s = apply_move_list M_s 1`
  use (M_s ++ M)              -- Propose the combined move list `M_s ++ M` for the new state
  -- The goal is: `apply_move_list M s = apply_move_list (M_s ++ M) 1`

  -- Rewrite the RHS using the append lemma to match the structure of the LHS
  dsimp -- Add this before the rewrite
  rw [apply_move_list_append]
  -- The goal is now: `apply_move_list M s = apply_move_list M (apply_move_list M_s 1)`

  -- Substitute `s` on the LHS using its definition `h_s_eq`
  rw [h_s_eq]
  -- The goal becomes: `apply_move_list M (apply_move_list M_s 1) = apply_move_list M (apply_move_list M_s 1)`
  -- This is true by reflexivity, so the proof is complete.

lemma apply_move_list_center_perm_comp (M : List BasicMove) (s : CubeState) :
  (apply_move_list M s).center_perm = (apply_move_list M 1).center_perm * s.center_perm := by
  induction M generalizing s with
  | nil =>
    simp [apply_move_list, CubeState.center_perm, initialState, One.one, mul_one]
    decide
  | cons m ms ih =>
    simp only [apply_move_list, List.foldl_cons] at * -- Unfold apply_move_list using foldl everywhere
    rw [ih (apply_move m s)] -- Apply IH to the state after move m
    rw [ih (apply_move m 1)] -- Apply IH to the state after move m starting from 1
    -- Need to show (apply_move m s).center_perm = (apply_move m 1).center_perm * s.center_perm
    have h_step : (apply_move m s).center_perm = (apply_move m 1).center_perm * s.center_perm := by
      -- Proof relies on apply_move definition: new_perm = move_perm * old_perm
      -- and initialState.center_perm = 1
      cases m <;> simp [apply_move, CubeState.center_perm, initialState, One.one, mul_one]<;> decide
    rw [h_step, mul_assoc] -- Apply the single-step property and associativity

lemma apply_move_list_corner_perm_comp (M : List BasicMove) (s : CubeState) :
  (apply_move_list M s).corner_perm = (apply_move_list M 1).corner_perm * s.corner_perm := by
  have h : CubeState.corner_perm 1 = 1 := by decide
  induction M generalizing s with
  | nil =>
    simp only [apply_move_list, List.foldl_nil, CubeState.corner_perm, initialState, One.one, mul_one]
     -- This is trivial, but needed for the proof
    rw [h]
    rfl -- This should be true by reflexivity
  | cons m ms ih =>
    simp only [apply_move_list, List.foldl_cons] at * -- Unfold definitions everywhere
    rw [ih (apply_move m s)] -- Apply IH to state after move m
    rw [ih (apply_move m 1)] -- Apply IH to state after move m from initial
    -- Need: (apply_move m s).corner_perm = (apply_move m 1).corner_perm * s.corner_perm
    have h_step : (apply_move m s).corner_perm = (apply_move m 1).corner_perm * s.corner_perm := by
      -- Relies on apply_move definition: new_perm = move_perm * old_perm
      cases m <;> simp only [apply_move, CubeState.corner_perm, initialState, One.one, mul_one, mul_assoc] -- Use simp (or decide)
      <;> rw [h] -- This is needed for the initial state
      <;> rfl
      -- Or potentially: cases m <;> decide
    rw [h_step, mul_assoc]


-- Specific composition lemma for edge permutations
lemma apply_move_list_edge_perm_comp (M : List BasicMove) (s : CubeState) :
  (apply_move_list M s).edge_perm = (apply_move_list M 1).edge_perm * s.edge_perm := by
  have h : CubeState.edge_perm 1 = 1 := by decide
  induction M generalizing s with
  | nil =>
    simp only [apply_move_list, List.foldl_nil, CubeState.edge_perm, initialState, One.one, mul_one]
    rw [h]; rfl
 -- This is trivial, but needed for the proof
  | cons m ms ih =>
    simp only [apply_move_list, List.foldl_cons] at * -- Unfold definitions everywhere
    rw [ih (apply_move m s)] -- Apply IH to state after move m
    rw [ih (apply_move m 1)] -- Apply IH to state after move m from initial
    -- Need: (apply_move m s).edge_perm = (apply_move m 1).edge_perm * s.edge_perm
    have h_step : (apply_move m s).edge_perm = (apply_move m 1).edge_perm * s.edge_perm := by
      -- Relies on apply_move definition: new_perm = move_perm * old_perm
      cases m <;> simp only [apply_move, CubeState.edge_perm, initialState, One.one, mul_one, mul_assoc] -- Use simp (or decide)
      -- Or potentially: cases m <;> decide
      <;> rw [h] -- This is needed for the initial state
      <;> rfl
    rw [h_step, mul_assoc]
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
    have h_sign_eq : checkPermSigns s := is_solvable_check_perm_signs s h_solv
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
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def]
        simp only [apply_move, MoveImpl.apply_move]
        rw [Perm.sign_mul]
        have h_r_sign : Perm.sign r_move_center_perm = -1 := by native_decide -- Or sorry
        rw [h_r_sign]
        -- Goal: -1 * permSign s.center_perm = 1
        have h_s_sign : Perm.sign s.center_perm = (-1 : ℤˣ) := by -- Target type is ℤˣ
          -- Let a be the sign, which has type ℤˣ
          let a : ℤˣ := Perm.sign s.center_perm
          -- Use the lemma stating that elements of ℤˣ are 1 or -1
          have h_one_or_neg_one : a = (1 : ℤˣ) ∨ a = (-1 : ℤˣ) := Int.units_eq_one_or a
          -- We know a ≠ 1 from h_rho_even (which is ¬ (a = 1))
          exact Or.resolve_left h_one_or_neg_one h_rho_even
        rw [h_s_sign]
        -- Goal: -1 * -1 = 1 (in ℤˣ)
        simp -- Should solve this using Units.neg_one_mul_neg_one or similar
        -- rfl -- Alternative


    have h_sign₁ : checkPermSigns s₁ := by
      -- Use by_cases to split on the condition used to define s₁
      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true
        -- In this case, s₁ was defined as s
        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def] -- Substitute s₁ with s in the goal
        -- Goal is now checkPermSigns s
        exact h_sign_s -- Use the original assumption h_sign_s
      · -- Case 2: permSign s.center_perm = 1 is false
        -- In this case, s₁ was defined as apply_move R s
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def] -- Substitute s₁ in the goal
        -- Goal is now checkPermSigns (apply_move R s)
        simp only [checkPermSigns, apply_move, MoveImpl.apply_move] -- Unfold definitions
        -- Goal: sign(r_p_c * s_p_c) = sign(r_p_z * s_p_z)
        rw [Perm.sign_mul, Perm.sign_mul] -- Apply sign multiplication rule
        have h_r_c_sign : Perm.sign r_move_corner_perm = -1 := by native_decide -- Or sorry
        have h_r_z_sign : Perm.sign r_move_center_perm = -1 := by native_decide -- Or sorry
        rw [h_r_c_sign, h_r_z_sign]
        -- Goal: -1 * sign(s_p_c) = -1 * sign(s_p_z)
        -- Use the original assumption h_sign_s (which is sign(s_p_c) = sign(s_p_z))
        rw [h_sign_s]
        -- Goal is now -1 * sign = -1 * sign, which is true by reflexivity
        -- rfl -- Often not needed after the last rw
    have h_twist₁ : checkCornerTwist s₁ := by
      -- Use by_cases to split on the condition used to define s₁
      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true
        -- In this case, s₁ was defined as s
        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def] -- Substitute s₁ with s in the goal
        -- Goal is now checkCornerTwist s
        exact h_twist_s -- Use the original assumption h_twist_s
      · -- Case 2: permSign s.center_perm = 1 is false
        -- In this case, s₁ was defined as apply_move R s
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def] -- Substitute s₁ in the goal
        -- Goal is now checkCornerTwist (apply_move R s)
        -- Use the invariance lemma for the R move
        exact lemma1_step2_move_invariance BasicMove.R s h_twist_s
    have h_edge₁ : checkEdgeFlip s₁ := by
      -- Use by_cases to split on the condition used to define s₁
      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true
        -- In this case, s₁ was defined as s
        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def] -- Substitute s₁ with s in the goal
        -- Goal is now checkEdgeFlip s
        exact h_edge_s -- Use the original assumption h_edge_s
      · -- Case 2: permSign s.center_perm = 1 is false
        -- In this case, s₁ was defined as apply_move R s
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def] -- Substitute s₁ in the goal
        -- Goal is now checkEdgeFlip (apply_move R s)
        -- Use the invariance lemma for the R move (Lemma 7)
        exact lemma7_step2_move_invariance BasicMove.R s h_edge_s
    -- Now continue with Step 2 using s₁, h_center_perm_even₁, h_sign₁, h_twist₁, h_edge₁
    -- ... rest of the proof ...
        -- Step 2: Find solvable state z₁ to cancel center permutation
    -- Since s₁.center_perm is even, its inverse is also even

    -- Step 2: Find solvable state z₁ to cancel center permutation
    have h_center_perm_inv_even : Equiv.Perm.sign s₁.center_perm⁻¹ = 1 := by
      rw [Perm.sign_inv]; exact h_center_perm_even₁
    -- Apply Lemma 4
    obtain ⟨z₁, h_z₁_solv, h_z₁_zperm_eq, h_z₁_cperm_id, h_z₁_eperm_id, h_z₁_eori_zero⟩ :=
      lemma4_center_perm_achievability (s₁.center_perm⁻¹) h_center_perm_inv_even
    -- Extract the move list M_z1 from the solvability proof for z₁
    obtain ⟨M_z1, h_z1_moves⟩ := h_z₁_solv

    -- Apply the moves M_z1 to s₁
    let s₂ := apply_move_list M_z1 s₁

    -- Prove properties about the resulting state s₂
    have h_center_perm₂ : s₂.center_perm = 1 := by
      -- State goal explicitly in terms of definitions
      change (apply_move_list M_z1 s₁).center_perm = 1
      -- Apply the composition lemma proven above
      rw [apply_move_list_center_perm_comp M_z1 s₁]
      -- Goal: (apply_move_list M_z1 1).center_perm * s₁.center_perm = 1
      -- Substitute z₁ for (apply_move_list M_z1 1) using the hypothesis from IsSolvable z₁
      rw [← h_z1_moves]
      -- Goal: z₁.center_perm * s₁.center_perm = 1
      -- Substitute the property of z₁ (it achieves the inverse permutation)
      rw [h_z₁_zperm_eq]
      -- Goal: s₁.center_perm⁻¹ * s₁.center_perm = 1
      -- Use the group theory lemma
      aesop

    have h_corner_perm₂ : s₂.corner_perm = s₁.corner_perm := by
      -- State goal explicitly using definition of s₂
      change (apply_move_list M_z1 s₁).corner_perm = s₁.corner_perm
      -- Apply the composition lemma for corners (requires Step 1)
      rw [apply_move_list_corner_perm_comp M_z1 s₁]
      -- Goal: (apply_move_list M_z1 1).corner_perm * s₁.corner_perm = s₁.corner_perm
      -- Substitute z₁ using h_z1_moves
      rw [← h_z1_moves]
      -- Goal: z₁.corner_perm * s₁.corner_perm = s₁.corner_perm
      -- Substitute the property of z₁ (corner_perm = 1)
      rw [h_z₁_cperm_id]
      -- Goal: 1 * s₁.corner_perm = s₁.corner_perm
      -- Use the group identity property
      simp only [one_mul]-- Since z₁ only affects centers

    have h_edge_perm₂ : s₂.edge_perm = s₁.edge_perm := by
      -- State goal explicitly using definition of s₂
      change (apply_move_list M_z1 s₁).edge_perm = s₁.edge_perm
      -- Apply the composition lemma for edges (requires Step 1)
      rw [apply_move_list_edge_perm_comp M_z1 s₁]
      -- Goal: (apply_move_list M_z1 1).edge_perm * s₁.edge_perm = s₁.edge_perm
      -- Substitute z₁ using h_z1_moves
      rw [← h_z1_moves]
      -- Goal: z₁.edge_perm * s₁.edge_perm = s₁.edge_perm
      -- Substitute the property of z₁ (edge_perm = 1)
      rw [h_z₁_eperm_id]
      -- Goal: 1 * s₁.edge_perm = s₁.edge_perm
      -- Use the group identity property
      simp only [one_mul] -- Since z₁ only affects centers
    have h_twist₂ : checkCornerTwist s₂ := by
      -- Expand the definition of s₂
      change checkCornerTwist (apply_move_list M_z1 s₁)
      -- Apply the lemma stating that move sequences preserve checkCornerTwist
      -- `moves_check_corner_twist M_z1 s₁` has type `checkCornerTwist s₁ → checkCornerTwist (apply_move_list M_z1 s₁)`
      apply moves_check_corner_twist M_z1 s₁
      -- The goal now is the premise of the lemma: `checkCornerTwist s₁`
      -- Use the fact that we already established checkCornerTwist holds for s₁
      exact h_twist₁ -- Since z₁ doesn't affect corner ori
    have h_edge₂ : checkEdgeFlip s₂ := by
      -- Goal: checkEdgeFlip s₂
      -- Unfold definition of s₂
      change checkEdgeFlip (apply_move_list M_z1 s₁)
      -- Apply the lemma that states applying moves preserves the edge flip property
      -- This assumes `moves_preserves_checkEdgeFlip` has been proven.
      apply moves_preserves_checkEdgeFlip M_z1 s₁
      -- The goal is now the required input condition for the lemma: `checkEdgeFlip s₁`
      -- Use the hypothesis h_edge₁ which was proven earlier in this proof direction
      exact h_edge₁-- Since z₁ doesn't affect edges

    -- Now continue with Step 3 using s₂, h_center_perm₂, etc.
    -- Step 3: Fix corner permutation σ
    -- Need to show s₂ corner perm is even
    have h_corner_perm_even₂ : Perm.sign s₂.corner_perm = 1 := sorry -- From h_sign₁ and h_center_perm₂ = 1
    -- Since s₂.corner_perm is even, its inverse is also even
    have h_corner_perm_inv_even₂ : Perm.sign s₂.corner_perm⁻¹ = 1 := by -- Added this step
      rw [Perm.sign_inv]
      exact h_corner_perm_even₂
    -- Apply Lemma 3 using the correct hypothesis
    obtain ⟨c₁, h_c₁_solv, h_c₁_cperm_eq, h_c₁_eperm_id, h_c₁_zperm_id, h_c₁_eori_zero⟩ :=
      lemma3_corner_perm_achievability (s₂.corner_perm⁻¹) h_corner_perm_inv_even₂ -- Use the sign of the inverse
    -- Extract the move list M_c1
    obtain ⟨M_c1, h_c1_moves⟩ := h_c₁_solv

    -- Apply the moves M_c1 to s₂
    let s₃ := apply_move_list M_c1 s₂
    -- Need proofs about state s₃
    have h_corner_perm₃ : s₃.corner_perm = 1 := sorry
    have h_center_perm₃ : s₃.center_perm = 1 := sorry
    have h_edge_perm₃ : s₃.edge_perm = s₂.edge_perm := sorry
    have h_twist₃ : checkCornerTwist s₃ := sorry
    have h_edge₃ : checkEdgeFlip s₃ := sorry

    -- Step 4: Fix edge permutation τ
    -- ... rest of the proof ...
    -- Apply Lemma 5 to find moves e₁ that achieve s₃.edge_perm⁻¹
    obtain ⟨e₁, h_e₁_solv, h_e₁_eperm_eq, h_e₁_cperm_id, h_e₁_zperm_id⟩ :=
      lemma5_edge_perm_achievability (s₃.edge_perm⁻¹)
    -- Extract the move list M_e1
    obtain ⟨M_e1, h_e1_moves⟩ := h_e₁_solv

    -- Apply the moves M_e1 to s₃
    let s₄ := apply_move_list M_e1 s₃

    -- Prove properties about state s₄
    have h_perm₄ : s₄.corner_perm = 1 ∧ s₄.edge_perm = 1 ∧ s₄.center_perm = 1 := by
      constructor
      · -- Prove s₄.corner_perm = 1
        -- Requires lemma: (apply_move_list M s).corner_perm = (apply_move_list M initialState).corner_perm * s.corner_perm
        sorry -- Apply composition lemma, h_e₁_cperm_id, h_corner_perm₃, one_mul
      · constructor
        · -- Prove s₄.edge_perm = 1
          -- Requires lemma: (apply_move_list M s).edge_perm = (apply_move_list M initialState).edge_perm * s.edge_perm
          sorry -- Apply composition lemma, h_e₁_eperm_eq, h_edge_perm₃ (relative to s₂?), mul_inv_self
        · -- Prove s₄.center_perm = 1
          -- Requires lemma: (apply_move_list M s).center_perm = (apply_move_list M initialState).center_perm * s.center_perm
          sorry -- Apply composition lemma, h_e₁_zperm_id, h_center_perm₃, one_mul

    -- Now continue with Step 5 using s₄ and h_perm₄
    -- ... rest of the proof ...
    -- Step 5: Check orientations of s₄
    have h_twist₄ : checkCornerTwist s₄ := by
      -- Argument: s -> s₁ preserves twist (by lemma1_step2_move_invariance R s h_twist_s if R was used, else trivial)
      -- s₁ -> s₂ preserves twist (because z₁ is solvable, use lemma1_corner_twist_invariant)
      -- s₂ -> s₃ preserves twist (because c₁ is solvable, use lemma1_corner_twist_invariant)
      -- s₃ -> s₄ preserves twist (because e₁ is solvable, use lemma1_corner_twist_invariant)
      -- This requires proving how IsSolvable composes and relates state transformations.
      sorry -- Placeholder for detailed proof showing preservation through z₁, c₁, e₁ moves

    -- First, show checkEdgeFlip holds for s₄
    have h_edge₄_holds : checkEdgeFlip s₄ := by
      -- Argument: s -> s₁ preserves edge flip (by lemma7_step2_move_invariance R s h_edge_s if R was used, else trivial)
      -- s₁ -> s₂ preserves edge flip (because z₁ has edge_perm=1, edge_ori=0)
      -- s₂ -> s₃ preserves edge flip (because c₁ has edge_perm=1, edge_ori=0)
      -- s₃ -> s₄ preserves edge flip (because e₁ has corner/center_perm=1, need lemma on its edge effect)
      -- This requires detailed proofs or lemmas about preservation for z₁, c₁, e₁.
      sorry -- Placeholder for detailed proof showing preservation through z₁, c₁, e₁ moves

    -- Now, deduce edge_ori = 0 from checkEdgeFlip s₄ and s₄.edge_perm = 1
    have h_edge₄_zero : s₄.edge_ori = fun _ => 0 := by
      -- Use function extensionality: show s₄.edge_ori i = 0 for all i
      funext i
      -- Apply the definition of checkEdgeFlip s₄
      have h_flip_i := h_edge₄_holds i
      -- Substitute s₄.edge_perm = 1 into the definition of getPieceTypeInSlot
      simp only [getPieceTypeInSlot, h_perm₄.2.1, inv_one, Perm.one_apply] at h_flip_i
      -- h_flip_i is now: s₄.edge_ori i = 1 - edgeDelta (getSlotType i) (getSlotType i)

      -- Unfold edgeDelta
      rw [edgeDelta] at h_flip_i
      -- h_flip_i is now: s₄.edge_ori i = 1 - if getSlotType i = getSlotType i then 1 else 0

      -- Simplify the condition using eq_self with simp
      simp only [eq_self] at h_flip_i -- Use simp instead of rw
      -- h_flip_i should now be: s₄.edge_ori i = 1 - if True then 1 else 0

      -- Simplify the if statement
      rw [if_true] at h_flip_i
      -- h_flip_i is now: s₄.edge_ori i = 1 - 1

      -- Simplify the subtraction
      rw [sub_self] at h_flip_i
      -- h_flip_i is now: s₄.edge_ori i = 0

      -- Use this hypothesis to prove the goal
      exact h_flip_i

    -- Step 6 concluded:
    have h_s₄_solvable_final : IsSolvable s₄ := lemma6_corner_twist_solvability s₄ h_perm₄ h_edge₄_zero h_twist₄

    -- Step 7: Combine solvability
    -- We know s₄ is solvable. Let M_s4 be the moves to reach s₄ from initialState.
    obtain ⟨M_s4, h_s4_eq_moves⟩ := h_s₄_solvable_final

    -- Define the sequence M_fix_total transforming s to s₄
    let M_fix_intermediate := M_z1 ++ M_c1 ++ M_e1
    let M_fix_total := if h_center_even : Perm.sign s.center_perm = 1 then M_fix_intermediate else [BasicMove.R] ++ M_fix_intermediate
    have h_s4_from_s : s₄ = apply_move_list M_fix_total s := sorry -- Proof needed

    -- We need to show ∃ M', s = apply_move_list M' initialState
    -- We will show s = apply_move_list (M_s4 ++ inv_move_list M_fix_total) initialState
    use (M_s4 ++ inv_move_list M_fix_total)

    -- Start from cancellation lemma applied to s₄ and M_fix_total
    have h_cancel_s4 : s = apply_move_list (inv_move_list M_fix_total) s₄ := by
      -- Need h_s4_from_s : s₄ = apply_move_list M_fix_total s (defined earlier in proof)
      -- Apply the list cancellation lemma to state s
      have h_list_cancel := apply_move_list_inv_move_list_cancel M_fix_total s
      -- h_list_cancel : apply_move_list (inv_move_list M_fix_total) (apply_move_list M_fix_total s) = s
      -- Substitute s₄ using h_s4_from_s in h_list_cancel
      rw [← h_s4_from_s] at h_list_cancel
      -- h_list_cancel : apply_move_list (inv_move_list M_fix_total) s₄ = s
      -- Now use symmetry to match the goal
      exact Eq.symm h_list_cancel
    -- Substitute s₄ using h_s4_eq_moves
    rw [h_s4_eq_moves] at h_cancel_s4
    -- h_cancel_s4 is now: s = apply_move_list (inv_move_list M_fix_total) (apply_move_list M_s4 initialState)

    -- Apply append lemma (backwards)
    rw [← apply_move_list_append] at h_cancel_s4
    -- h_cancel_s4 is now: s = apply_move_list (M_s4 ++ inv_move_list M_fix_total) initialState

    -- This matches the goal derived from the 'use' statement
    exact h_cancel_s4

end FourRubik
