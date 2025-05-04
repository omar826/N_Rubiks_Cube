import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.List.Induction
import NRubiksCube.FourRubik
import Mathlib.Order.WellFounded

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

namespace FourRubik

open BigOperators
open Equiv

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


-- even index = A, odd index = B
def getSlotType (slot : EdgeSlot) : Orientation.EdgeType :=
  if slot % 2 = 0 then Orientation.EdgeType.A else Orientation.EdgeType.B

-- Helper function to get the EdgeType (A or B) associated with the *original* piece
def getPieceTypeInSlot (s : CubeState) (slot : EdgeSlot) : Orientation.EdgeType :=
  let origin_slot : EdgeSlot := s.edge_perm⁻¹ slot
  getSlotType origin_slot

-- The delta function from the paper: δ_{t,s} = 1 if t=s, 0 otherwise
def edgeDelta (t s : Orientation.EdgeType) : ZMod 2 :=
  if t = s then 1 else 0

/-- Condition 3: The edge orientation `yᵢ` must match the formula `1 - δ_{t,s}`,
    where `t` is the type of slot `i` and `s` is the type of the piece in slot `i`. -/
def checkEdgeFlip (s : CubeState) : Prop :=
  ∀ (i : EdgeSlot), s.edge_ori i = 1 - edgeDelta (getSlotType i) (getPieceTypeInSlot s i)


-- ## key lemmas

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
  | .U => u_move_corner_perm | .D => d_move_corner_perm
  | .F => f_move_corner_perm | .B => b_move_corner_perm
  | .CR => cr_move_corner_perm | .CL => cl_move_corner_perm
  | .CU => cu_move_corner_perm | .CD => cd_move_corner_perm
  | .CF => cf_move_corner_perm | .CB => cb_move_corner_perm

def get_move_edge_perm (m : BasicMove) : Perm EdgeSlot :=
  match m with
  | .R => r_move_edge_perm | .L => l_move_edge_perm
  | .U => u_move_edge_perm | .D => d_move_edge_perm
  | .F => f_move_edge_perm | .B => b_move_edge_perm
  | .CR => cr_move_edge_perm | .CL => cl_move_edge_perm
  | .CU => cu_move_edge_perm | .CD => cd_move_edge_perm
  | .CF => cf_move_edge_perm | .CB => cb_move_edge_perm

def get_move_center_perm (m : BasicMove) : Perm CenterSlot :=
  match m with
  | .R => r_move_center_perm | .L => l_move_center_perm
  | .U => u_move_center_perm | .D => d_move_center_perm
  | .F => f_move_center_perm | .B => b_move_center_perm
  | .CR => cr_move_center_perm | .CL => cl_move_center_perm
  | .CU => cu_move_center_perm | .CD => cd_move_center_perm
  | .CF => cf_move_center_perm | .CB => cb_move_center_perm

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


open BasicMove

def fixed_corner_3_cycle_seq : List BasicMove :=
  r' ++ d' ++ r ++ u' ++ r' ++ d ++ r ++ u

-- target permutation
def target_corner_perm : Perm CornerSlot :=
  Equiv.cycle c_urf c_ufl c_drf

example : (apply_move_list fixed_corner_3_cycle_seq initialState).corner_perm = target_corner_perm := by
  native_decide

/--
Showing that fixed_corner_3_cycle_seq is a 3 cycle
-/
theorem fixed_corner_3_cycle_seq_effect :
    ∃ (s : CubeState), s = apply_move_list fixed_corner_3_cycle_seq 1 ∧
                       IsSolvable s ∧
                       s.corner_perm = target_corner_perm ∧
                       s.edge_perm = 1 ∧
                       s.center_perm = 1 ∧
                       s.edge_ori = fun _ => 0 := by

  let s := apply_move_list fixed_corner_3_cycle_seq initialState
  use s

  constructor
  ·
    rfl
  · constructor
    · -- Proof of IsSolvable s
      use fixed_corner_3_cycle_seq; rfl
    · constructor
      · -- Proof of s.corner_perm = target_corner_perm

        native_decide
      · constructor
        · -- Proof of s.edge_perm = 1
          native_decide
        · constructor
          · -- Proof of s.center_perm = 1
            native_decide
          ·
            native_decide


-- Lemma asserting the existence of setup moves 'g' such that the conjugate g*m*g⁻¹
-- performs the desired 3-cycle (i j k) while preserving other piece types / edge orientations.
theorem corner_conjugation_works (i j k : CornerSlot)
    (h_distinct : i ≠ j ∧ i ≠ k ∧ j ≠ k) :
    ∃ (g : Moves),
      ∃ (s_conj : CubeState), -- The state after applying g * m * g⁻¹
         s_conj = apply_move_list (g ++ fixed_corner_3_cycle_seq ++ inv_move_list g) 1 ∧
         IsSolvable s_conj ∧
         s_conj.corner_perm = (Equiv.cycle i j k) ∧ -- The desired 3-cycle
         s_conj.edge_perm = 1 ∧
         s_conj.center_perm = 1 ∧
         s_conj.edge_ori = fun _ => 0 :=
  sorry


/-- Consequence of Lemma 3 (C ≅ A₈): Any even permutation of corners can be achieved
    by a solvable state that doesn't permute other pieces or affect edge orientation. -/
theorem lemma3_corner_perm_achievability (σ_target : Perm CornerSlot)
    (h_even : Perm.sign σ_target = 1) :
    ∃ (s : CubeState), IsSolvable s ∧
                       s.corner_perm = σ_target ∧
                       s.edge_perm = 1 ∧
                       s.center_perm = 1 ∧
                       s.edge_ori = fun _ => 0 :=
  sorry

-- Sequence: CF, CD, CF⁻¹, CD⁻¹, U⁻¹, CD, CF, CD⁻¹, CF⁻¹, U
def center_3_cycle_seq : List BasicMove :=
  cf ++ cd ++ cf' ++ cd' ++ u' ++ cd ++ cf ++ cd' ++ cf' ++ u

def target_center_perm : Perm CenterSlot :=
  Equiv.cycle z_u_dr z_u_dl z_f_dl

theorem center_3_cycle_seq_effect :
    ∃ (s : CubeState), s = apply_move_list center_3_cycle_seq 1 ∧
                        IsSolvable s ∧
                        s.center_perm = target_center_perm ∧
                        s.corner_perm = 1 ∧
                        s.edge_perm = 1 ∧
                        s.corner_ori = fun _ => 0
                        := by

  let s := apply_move_list center_3_cycle_seq initialState -- initialState is 1
  use s

  constructor
  · -- Proof of s = apply_move_list ...
    rfl
  · constructor
    · -- Proof of IsSolvable s
      use center_3_cycle_seq
      rfl
    · constructor
      · -- Proof of s.center_perm = target_center_perm
        native_decide

      · constructor
        · -- Proof of s.corner_perm = 1
          native_decide
        · constructor
          · -- Proof of s.edge_perm = 1
            native_decide
          · -- Proof of s.corner_ori = fun _ => 0
            native_decide
/-- Consequence of Lemma 4 (Z ≅ A₂₄): Any even permutation of centers can be achieved
    by a solvable state that doesn't permute other pieces or affect edge orientation. -/
theorem lemma4_center_perm_achievability (ρ_target : Perm CenterSlot)
    (h_even : Perm.sign ρ_target = 1) :
    ∃ (s : CubeState), IsSolvable s ∧
                       s.center_perm = ρ_target ∧
                       s.corner_perm = 1 ∧
                       s.edge_perm = 1 ∧
                       s.edge_ori = fun _ => 0 :=
  sorry
-- Sequence: CL⁻¹, L, U⁻¹, L⁻¹, U, CL, U⁻¹, L, U, L⁻¹
def edge_3_cycle_seq : List BasicMove :=
  cl' ++ l ++ u' ++ l' ++ u ++ cl ++ u' ++ l ++ u ++ l'

def target_edge_perm : Perm EdgeSlot :=
  Equiv.cycle e_ul_a e_uf_b e_ub_a

theorem edge_3_cycle_seq_effect :
    ∃ (s : CubeState), s = apply_move_list edge_3_cycle_seq 1 ∧
                        IsSolvable s ∧
                        s.edge_perm = target_edge_perm ∧
                        s.corner_perm = 1 ∧
                        s.center_perm = 1 ∧
                        s.corner_ori = fun _ => 0
                        := by
  -- Define the state resulting from the sequence
  let s := apply_move_list edge_3_cycle_seq initialState -- initialState is 1
  use s

  constructor; rfl
  constructor; exact ⟨edge_3_cycle_seq, rfl⟩
  constructor
  · -- Proof of s.edge_perm = target_edge_perm
    native_decide
  · constructor
    · -- Proof of s.corner_perm = 1
      native_decide
    · constructor
      · -- Proof of s.center_perm = 1
        native_decide
      · -- Proof of s.corner_ori = fun _ => 0
        native_decide

/-- Consequence of Lemma 5 (E ≅ S₂₄): Any permutation of edges can be achieved
    by a solvable state that doesn't permute other pieces.
    (Note: This state *will* generally affect edge orientations according to Condition 3). -/
theorem lemma5_edge_perm_achievability (τ_target : Perm EdgeSlot) :
    ∃ (s : CubeState), IsSolvable s ∧
                       s.edge_perm = τ_target ∧
                       s.corner_perm = 1 ∧
                       s.center_perm = 1 :=
  sorry

def M : List BasicMove :=
  r' ++ d ++ r ++ f ++ d ++ f' ++ u' ++ f ++ d' ++ f' ++ r' ++ d' ++ r ++ u

/-- Lemma 6 (Implied by paper): A state with identity permutations and zero edge
    orientation, satisfying the corner twist condition, is solvable. -/
theorem lemma6_corner_twist_solvability (s : CubeState)
    (h_perm : s.corner_perm = 1 ∧ s.edge_perm = 1 ∧ s.center_perm = 1)
    (h_edge_ori : s.edge_ori = fun _ => 0)
    (h_twist : checkCornerTwist s) :
    IsSolvable s := by
  sorry

end FourRubik
