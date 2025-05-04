import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.List.Induction
import NRubiksCube.FourRubik
import NRubiksCube.FourLemmas

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-!
# Solvability Conditions for the 4x4x4 Rubik's Revenge

In this file, we prove the theorem:
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
open BasicMove
-- ## Solvability Definition


/-!
## Proof of Edge Flip Invariance (Condition 3)
-/

-- Step 1: Show the initial state satisfies the condition.
theorem lemma7_step1_initial_state : checkEdgeFlip 1 := by
  show checkEdgeFlip initialState
  intro i

  simp only [initialState, getPieceTypeInSlot, checkEdgeFlip, edgeDelta, inv_one, Perm.one_apply]

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

  induction L1 generalizing s with
  | nil => -- Base case: L1 = []

    simp only [
        List.nil_append,
        apply_move_list,
        List.foldl_nil
      ]


  | cons m ms ih =>

    simp only [apply_move_list, List.foldl_cons, List.cons_append]

    exact ih (apply_move m s)

lemma apply_move_list_corner_perm_comp (M : List BasicMove) (s : CubeState) :
  (apply_move_list M s).corner_perm = (apply_move_list M 1).corner_perm * s.corner_perm := by
  have h : CubeState.corner_perm 1 = 1 := by decide
  induction M generalizing s with
  | nil =>
    simp only [apply_move_list, List.foldl_nil, CubeState.corner_perm, initialState, One.one, mul_one]

    rw [h]
    rfl
  | cons m ms ih =>
    simp only [apply_move_list, List.foldl_cons] at *
    rw [ih (apply_move m s)]
    rw [ih (apply_move m 1)]

    have h_step : (apply_move m s).corner_perm = (apply_move m 1).corner_perm * s.corner_perm := by

      cases m <;> simp only [apply_move, CubeState.corner_perm, initialState, One.one, mul_one, mul_assoc] -- Use simp (or decide)
      <;> rw [h]
      <;> rfl

    rw [h_step, mul_assoc]


-- composition lemma for edge permutations
lemma apply_move_list_edge_perm_comp (M : List BasicMove) (s : CubeState) :
  (apply_move_list M s).edge_perm = (apply_move_list M 1).edge_perm * s.edge_perm := by
  have h : CubeState.edge_perm 1 = 1 := by decide
  induction M generalizing s with
  | nil =>
    simp only [apply_move_list, List.foldl_nil, CubeState.edge_perm, initialState, One.one, mul_one]
    rw [h]; rfl

  | cons m ms ih =>
    simp only [apply_move_list, List.foldl_cons] at *
    rw [ih (apply_move m s)]
    rw [ih (apply_move m 1)]

    have h_step : (apply_move m s).edge_perm = (apply_move m 1).edge_perm * s.edge_perm := by

      cases m <;> simp only [apply_move, CubeState.edge_perm, initialState, One.one, mul_one, mul_assoc]

      <;> rw [h]
      <;> rfl
    rw [h_step, mul_assoc]

lemma apply_move_list_center_perm_comp (M : List BasicMove) (s : CubeState) :
  (apply_move_list M s).center_perm = (apply_move_list M 1).center_perm * s.center_perm := by
  induction M generalizing s with
  | nil =>
    simp [apply_move_list, CubeState.center_perm, initialState, One.one, mul_one]
  | cons m ms ih =>
    simp only [apply_move_list, List.foldl_cons] at *
    rw [ih (apply_move m s)]
    rw [ih (apply_move m 1)]

    have h_step : (apply_move m s).center_perm = (apply_move m 1).center_perm * s.center_perm := by

      cases m <;> simp [apply_move, CubeState.center_perm, initialState, One.one, mul_one]
    rw [h_step, mul_assoc]

lemma apply_move_corner_perm_comp (m : BasicMove) (s : CubeState) :
    (apply_move m s).corner_perm = (get_move_corner_perm m) * s.corner_perm := by
  cases m <;> simp [apply_move, get_move_corner_perm, CubeState.corner_perm, initialState, One.one, mul_one]

lemma apply_move_edge_perm_comp (m : BasicMove) (s : CubeState) :
    (apply_move m s).edge_perm = (get_move_edge_perm m) * s.edge_perm := by
  cases m <;> simp [apply_move, get_move_edge_perm, CubeState.edge_perm, initialState, One.one, mul_one]

lemma apply_move_center_perm_comp (m : BasicMove) (s : CubeState) :
    (apply_move m s).center_perm = (get_move_center_perm m) * s.center_perm := by
  cases m <;> simp [apply_move, get_move_center_perm]

lemma apply_move_corner_ori_comp (m : BasicMove) (s : CubeState) (i : CornerSlot) :
    (apply_move m s).corner_ori i =
    s.corner_ori ((apply_move m 1).corner_perm⁻¹ i) + (apply_move m 1).corner_ori i := by
    cases m <;> simp [apply_move]

lemma apply_move_edge_ori_comp (m : BasicMove) (s : CubeState) (i : EdgeSlot) :
    (apply_move m s).edge_ori i =
    s.edge_ori ((apply_move m 1).edge_perm⁻¹ i) + (apply_move m 1).edge_ori i := by
    cases m <;> simp [apply_move]

lemma apply_move_list_corner_ori_comp (M : List BasicMove) (s : CubeState) :
    ∀i, (apply_move_list M s).corner_ori i =
    s.corner_ori ((apply_move_list M 1).corner_perm⁻¹ i) + (apply_move_list M 1).corner_ori i := by
  induction M using List.reverseRecOn with
  | nil =>
    simp [apply_move_list]
  | append_singleton ms m ih =>
    intro i
    simp only [apply_move_list, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← apply_move_list, ← apply_move_list]
    rw [apply_move_corner_ori_comp m (apply_move_list ms 1)]
    rw [apply_move_corner_ori_comp m (apply_move_list ms s)]
    rw [ih ((apply_move m 1).corner_perm⁻¹ i)]
    rw [apply_move_corner_perm_comp m (apply_move_list ms 1)]
    have h : s.corner_ori ((apply_move_list ms 1).corner_perm⁻¹ ((apply_move m 1).corner_perm⁻¹ i))
        = s.corner_ori ((get_move_corner_perm m * (apply_move_list ms 1).corner_perm)⁻¹ i) := by
      simp only [mul_inv_rev, Perm.coe_mul, Function.comp_apply]
      cases m <;> unfold apply_move <;> unfold get_move_corner_perm <;> simp
    rw [h, add_assoc]

lemma apply_move_list_edge_ori_comp (M : List BasicMove) (s : CubeState) :
    ∀i, (apply_move_list M s).edge_ori i =
    s.edge_ori ((apply_move_list M 1).edge_perm⁻¹ i) + (apply_move_list M 1).edge_ori i := by
  induction M using List.reverseRecOn with
  | nil =>
    simp [apply_move_list]
  | append_singleton ms m ih =>
    intro i
    simp only [apply_move_list, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← apply_move_list, ← apply_move_list]
    rw [apply_move_edge_ori_comp m (apply_move_list ms 1)]
    rw [apply_move_edge_ori_comp m (apply_move_list ms s)]
    rw [ih ((apply_move m 1).edge_perm⁻¹ i)]
    rw [apply_move_edge_perm_comp m (apply_move_list ms 1)]
    have h : s.edge_ori ((apply_move_list ms 1).edge_perm⁻¹ ((apply_move m 1).edge_perm⁻¹ i))
        = s.edge_ori ((get_move_edge_perm m * (apply_move_list ms 1).edge_perm)⁻¹ i) := by
      simp only [mul_inv_rev, Perm.coe_mul, Function.comp_apply]
      cases m <;> unfold apply_move <;> unfold get_move_edge_perm <;> simp
    rw [h, add_assoc]

lemma apply_move_inv_move_one_corner_perm (m : BasicMove) :
    (apply_move_list (inv_move m) (apply_move m 1)).corner_perm = 1 := by
  ext i
  dsimp [inv_move, apply_move_list]
  cases m
  <;> simp [apply_move_list, apply_move]
  <;> fin_cases i <;> decide

lemma apply_move_inv_move_one_edge_perm (m : BasicMove) :
    (apply_move_list (inv_move m) (apply_move m 1)).edge_perm = 1 := by
  ext i
  cases m
  <;> simp [apply_move_list, apply_move]
  <;> fin_cases i <;> decide

lemma apply_move_inv_move_one_center_perm (m : BasicMove) :
    (apply_move_list (inv_move m) (apply_move m 1)).center_perm = 1 := by
  ext i
  cases m
  <;> simp [apply_move_list, apply_move]
  <;> fin_cases i <;> decide

lemma apply_move_inv_move_one_corner_ori (m : BasicMove) (i : CornerSlot):
    (apply_move_list (inv_move m) (apply_move m 1)).corner_ori i = 0 := by
  cases m
  <;> simp [apply_move_list, apply_move]
  <;> fin_cases i <;> decide

lemma apply_move_inv_move_one_edge_ori (m : BasicMove) (i : EdgeSlot):
    (apply_move_list (inv_move m) (apply_move m 1)).edge_ori i = 0 := by
  cases m
  <;> simp [apply_move_list, apply_move]
  <;> fin_cases i <;> decide

lemma apply_move_list_inv_move_cancel (m : BasicMove) (s : CubeState) :
    apply_move_list (inv_move m) (apply_move m s) = s := by
  dsimp
  ext i
  · rw [apply_move_list_corner_perm_comp]
    have h : (apply_move m s).corner_perm = (apply_move m 1).corner_perm * s.corner_perm := by
      rw [apply_move_corner_perm_comp]
      cases m <;> simp [apply_move, get_move_corner_perm]
    rw [h, ← mul_assoc]
    rw [← apply_move_list_corner_perm_comp]
    rw [← inv_move, apply_move_inv_move_one_corner_perm]
    simp
  · rw [apply_move_list_edge_perm_comp]
    have h : (apply_move m s).edge_perm = (apply_move m 1).edge_perm * s.edge_perm := by
      rw [apply_move_edge_perm_comp]
      cases m <;> simp [apply_move, get_move_edge_perm]
    rw [h, ← mul_assoc]
    rw [← apply_move_list_edge_perm_comp]
    rw [← inv_move, apply_move_inv_move_one_edge_perm]
    simp
  · rw [apply_move_list_center_perm_comp]
    have h : (apply_move m s).center_perm = (apply_move m 1).center_perm * s.center_perm := by
      rw [apply_move_center_perm_comp]
      cases m <;> simp [apply_move, get_move_center_perm]
    rw [h, ← mul_assoc]
    rw [← apply_move_list_center_perm_comp]
    rw [← inv_move, apply_move_inv_move_one_center_perm]
    simp
  · rw [apply_move_list_corner_ori_comp]
    rw [apply_move_corner_ori_comp]
    have h : (apply_move m 1).corner_ori ((apply_move_list [m, m, m] 1).corner_perm⁻¹ i) +
        (apply_move_list [m, m, m] 1).corner_ori i =  0 := by
      conv =>
        lhs
        rw [← show (apply_move_list (m :: [m, m, m]) 1).corner_ori i =
                  (apply_move m 1).corner_ori ((apply_move_list [m, m, m] 1).corner_perm⁻¹ i) +
                  (apply_move_list [m, m, m] 1).corner_ori i by
              apply apply_move_list_corner_ori_comp [m, m, m] (apply_move m 1)]
      have : apply_move_list [m, m, m, m] 1 = apply_move_list [m, m, m] (apply_move m 1) := by
        simp [apply_move_list]
      rw [this, ← inv_move, apply_move_inv_move_one_corner_ori]
    have h' : s.corner_ori ((apply_move m 1).corner_perm⁻¹ ((apply_move_list [m, m, m] 1).corner_perm⁻¹ i))
        = s.corner_ori i := by
      suffices (apply_move m 1).corner_perm⁻¹ ((apply_move_list [m, m, m] 1).corner_perm⁻¹ i) = i by
        rw [this]

      have h_p3 : (apply_move_list [m, m, m] 1).corner_perm = (get_move_corner_perm m)^3 := by
        simp [apply_move_list, get_move_corner_perm]
        cases m <;> decide
      have h_pm : (apply_move m 1).corner_perm = get_move_corner_perm m := by
        simp [apply_move, get_move_corner_perm]
        cases m <;> decide
      rw [h_p3, h_pm, ← Perm.mul_apply, ← mul_inv_rev]
      have h' : get_move_corner_perm m = (apply_move m 1).corner_perm := by
        simp [apply_move, get_move_corner_perm]
        cases m <;> decide
      rw [h']
      have : ((apply_move_list [m, m, m] (apply_move m 1))).corner_perm
          = ((apply_move m 1).corner_perm ^ 3 * (apply_move m 1).corner_perm) := by
        rw [apply_move_list_corner_perm_comp]
        dsimp [apply_move_list]
        rw [apply_move_corner_perm_comp, apply_move_corner_perm_comp]
        rw [h_pm, pow_three]
      rw [← this, Perm.eq_inv_iff_eq.1]
      rw [← inv_move]
      rw [apply_move_inv_move_one_corner_perm]
      simp
    rw [h', add_assoc, h, add_zero]
  · rw [apply_move_list_edge_ori_comp]
    rw [apply_move_edge_ori_comp]
    have h : (apply_move m 1).edge_ori ((apply_move_list [m, m, m] 1).edge_perm⁻¹ i) +
        (apply_move_list [m, m, m] 1).edge_ori i =  0 := by
      conv =>
        lhs
        rw [← show (apply_move_list (m :: [m, m, m]) 1).edge_ori i =
                  (apply_move m 1).edge_ori ((apply_move_list [m, m, m] 1).edge_perm⁻¹ i) +
                  (apply_move_list [m, m, m] 1).edge_ori i by
              apply apply_move_list_edge_ori_comp [m, m, m] (apply_move m 1)]
      have : apply_move_list [m, m, m, m] 1 = apply_move_list [m, m, m] (apply_move m 1) := by
        simp [apply_move_list]
      rw [this, ← inv_move, apply_move_inv_move_one_edge_ori]
    have h' : s.edge_ori ((apply_move m 1).edge_perm⁻¹ ((apply_move_list [m, m, m] 1).edge_perm⁻¹ i))
        = s.edge_ori i := by
      suffices (apply_move m 1).edge_perm⁻¹ ((apply_move_list [m, m, m] 1).edge_perm⁻¹ i) = i by
        rw [this]

      have h_p3 : (apply_move_list [m, m, m] 1).edge_perm = (get_move_edge_perm m)^3 := by
        simp [apply_move_list, get_move_edge_perm]
        cases m <;> decide
      have h_pm : (apply_move m 1).edge_perm = get_move_edge_perm m := by
        simp [apply_move, get_move_edge_perm]
        cases m <;> decide
      rw [h_p3, h_pm, ← Perm.mul_apply, ← mul_inv_rev]
      have h' : get_move_edge_perm m = (apply_move m 1).edge_perm := by
        simp [apply_move, get_move_edge_perm]
        cases m <;> decide
      rw [h']
      have : ((apply_move_list [m, m, m] (apply_move m 1))).edge_perm
          = ((apply_move m 1).edge_perm ^ 3 * (apply_move m 1).edge_perm) := by
        rw [apply_move_list_edge_perm_comp]
        dsimp [apply_move_list]
        rw [apply_move_edge_perm_comp, apply_move_edge_perm_comp]
        rw [h_pm, pow_three]
      rw [← this, Perm.eq_inv_iff_eq.1]
      rw [← inv_move]
      rw [apply_move_inv_move_one_edge_perm]
      simp
    rw [h', add_assoc, h, add_zero]

lemma apply_move_list_inv_move_list_cancel (M : List BasicMove) (s : CubeState) :
    apply_move_list (inv_move_list M) (apply_move_list M s) = s := by
  induction M generalizing s with
  | nil =>
    simp only [inv_move_list, List.reverse_nil, List.map_nil, List.flatten_nil, apply_move_list, List.foldl_nil]
  | cons m ms ih =>
    -- ih : ∀ (s' : CubeState), apply_move_list (inv_move_list ms) (apply_move_list ms s') = s'

    have h_inv_list_cons : inv_move_list (m :: ms) = inv_move_list ms ++ inv_move m := by
      simp [inv_move_list, List.reverse_cons, List.map_append, List.flatten_append]
    rw [h_inv_list_cons]

    simp only [apply_move_list, List.foldl_cons]

    rw [List.foldl_append]

    -- *** Here is the change ***

    let s' := apply_move m s

    specialize ih s'
    -- ih : apply_move_list (inv_move_list ms) (apply_move_list ms s') = s'
    simp only [apply_move_list] at ih

    rw [ih]

    exact apply_move_list_inv_move_cancel m s


theorem isSolvable_of_apply_move_solvable (m : BasicMove) (s : CubeState) :
    IsSolvable (apply_move m s) → IsSolvable s := by
  intro h_solv_ms
  obtain ⟨M, h_eq⟩ := h_solv_ms

  use (M ++ inv_move m)



  have h_cancel : s = apply_move_list (inv_move m) (apply_move m s) :=
    (apply_move_list_inv_move_cancel m s).symm


  rw [h_eq] at h_cancel



  rw [← apply_move_list_append] at h_cancel

  exact h_cancel


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
    use (M ++ [m])
    rw [apply_move_list_append, h_s_eq, apply_move_list_singleton]

/-- Applying a sequence of moves to a solvable state results in a solvable state. -/
theorem isSolvable_apply_move_list (M : List BasicMove) (s : CubeState) :
    IsSolvable s → IsSolvable (apply_move_list M s) := by
  intro h_s_solv -- `s` is solvable
  obtain ⟨M_s, h_s_eq⟩ := h_s_solv
  use (M_s ++ M)



  dsimp
  rw [apply_move_list_append]

  rw [h_s_eq]


lemma solvability_iff_apply_move_list (M : List BasicMove) (s : CubeState) :
    IsSolvable (apply_move_list M s) ↔ IsSolvable s := by
  constructor
  · -- Direction =>: IsSolvable (apply_move_list M s) → IsSolvable s
        intro h_solv_Ms
        obtain ⟨M', h_eq⟩ := h_solv_Ms
        use (M' ++ inv_move_list M)
        have h_cancel_base := apply_move_list_inv_move_list_cancel M s
        rw [eq_comm] at h_cancel_base
        rw [h_eq] at h_cancel_base
        let h_cancel := h_cancel_base

        -- *** Apply lemma backwards to h_cancel ***
        rw [← apply_move_list_append] at h_cancel

        exact h_cancel
  · -- Direction <=: IsSolvable s → IsSolvable (apply_move_list M s)
    exact isSolvable_apply_move_list M s


-- ## Main Solvability Theorem Statement


theorem solvability_iff (s : CubeState) :
    IsSolvable s ↔ checkPermSigns s ∧ checkCornerTwist s ∧ checkEdgeFlip s := by
  constructor
  · -- Direction "=>": If a state is solvable, it must satisfy the conditions.
    intro h_solv

    -- Prove Condition 1: checkPermSigns s

    have h_sign_prod : Perm.sign s.corner_perm * Perm.sign s.center_perm = 1 :=
      lemma2_sign_invariant s h_solv

    have h_sign_eq : checkPermSigns s := is_solvable_check_perm_signs s h_solv
      -- Prove Condition 2: checkCornerTwist s
    have h_twist : checkCornerTwist s :=
      lemma1_corner_twist_invariant s h_solv

    -- Prove Condition 3: checkEdgeFlip s
    have h_edge : checkEdgeFlip s :=
      lemma7_edge_flip_invariant s h_solv

    -- Combine the three proven conditions
    exact ⟨h_sign_eq, h_twist, h_edge⟩






  · -- Direction "<=": If a state satisfies the conditions, it is solvable.
    intro h_conditions
    let ⟨h_sign_s, h_twist_s, h_edge_s⟩ := h_conditions

    -- Step 1: Ensure center permutation ρ is even

    let s₁ : CubeState := if h_center_even : Perm.sign s.center_perm = 1 then s else apply_move BasicMove.R s


    have h_s₁_solvable_rel : IsSolvable s → IsSolvable s₁ := by
      intro hs_solv

      by_cases h_center_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: Center permutation is even

        have h_s₁_def : s₁ = s := if_pos h_center_even
        rw [h_s₁_def]
        exact hs_solv
      · -- Case 2: Center permutation is odd

        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_center_even
        rw [h_s₁_def]

        apply (solvability_iff_apply_move BasicMove.R s).mpr
        exact hs_solv

    have h_center_perm_even₁ : Perm.sign s₁.center_perm = 1 := by

      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true

        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def]
        exact h_rho_even
      · -- Case 2: permSign s.center_perm = 1 is false
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def]
        simp only [apply_move, MoveImpl.apply_move]
        rw [Perm.sign_mul]
        have h_r_sign : Perm.sign r_move_center_perm = -1 := by native_decide
        rw [h_r_sign]

        have h_s_sign : Perm.sign s.center_perm = (-1 : ℤˣ) := by

          let a : ℤˣ := Perm.sign s.center_perm

          have h_one_or_neg_one : a = (1 : ℤˣ) ∨ a = (-1 : ℤˣ) := Int.units_eq_one_or a

          exact Or.resolve_left h_one_or_neg_one h_rho_even
        rw [h_s_sign]

        simp


    have h_sign₁ : checkPermSigns s₁ := by

      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true

        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def]

        exact h_sign_s
      · -- Case 2: permSign s.center_perm = 1 is false

        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def]
        simp only [checkPermSigns, apply_move, MoveImpl.apply_move]

        rw [Perm.sign_mul, Perm.sign_mul]
        have h_r_c_sign : Perm.sign r_move_corner_perm = -1 := by native_decide
        have h_r_z_sign : Perm.sign r_move_center_perm = -1 := by native_decide
        rw [h_r_c_sign, h_r_z_sign]

        rw [h_sign_s]

    have h_twist₁ : checkCornerTwist s₁ := by

      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true

        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def]

        exact h_twist_s
      · -- Case 2: permSign s.center_perm = 1 is false
        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def]
        exact lemma1_step2_move_invariance BasicMove.R s h_twist_s
    have h_edge₁ : checkEdgeFlip s₁ := by
      by_cases h_rho_even : (Perm.sign s.center_perm = 1)
      · -- Case 1: permSign s.center_perm = 1 is true
        have h_s₁_def : s₁ = s := if_pos h_rho_even
        rw [h_s₁_def]

        exact h_edge_s
      · -- Case 2: permSign s.center_perm = 1 is false

        have h_s₁_def : s₁ = apply_move BasicMove.R s := if_neg h_rho_even
        rw [h_s₁_def]
        exact lemma7_step2_move_invariance BasicMove.R s h_edge_s

    -- Step 2: Find solvable state z₁ to cancel center permutation
    have h_center_perm_inv_even : Equiv.Perm.sign s₁.center_perm⁻¹ = 1 := by
      rw [Perm.sign_inv]; exact h_center_perm_even₁

    obtain ⟨z₁, h_z₁_solv, h_z₁_zperm_eq, h_z₁_cperm_id, h_z₁_eperm_id, h_z₁_eori_zero⟩ :=
      lemma4_center_perm_achievability (s₁.center_perm⁻¹) h_center_perm_inv_even

    obtain ⟨M_z1, h_z1_moves⟩ := h_z₁_solv


    let s₂ := apply_move_list M_z1 s₁

    -- Prove properties about the resulting state s₂
    have h_center_perm₂ : s₂.center_perm = 1 := by

      change (apply_move_list M_z1 s₁).center_perm = 1

      rw [apply_move_list_center_perm_comp M_z1 s₁]

      rw [← h_z1_moves]

      rw [h_z₁_zperm_eq]

      aesop

    have h_corner_perm₂ : s₂.corner_perm = s₁.corner_perm := by

      change (apply_move_list M_z1 s₁).corner_perm = s₁.corner_perm

      rw [apply_move_list_corner_perm_comp M_z1 s₁]

      rw [← h_z1_moves]

      rw [h_z₁_cperm_id]

      simp only [one_mul]

    have h_edge_perm₂ : s₂.edge_perm = s₁.edge_perm := by

      change (apply_move_list M_z1 s₁).edge_perm = s₁.edge_perm

      rw [apply_move_list_edge_perm_comp M_z1 s₁]

      rw [← h_z1_moves]

      rw [h_z₁_eperm_id]

      simp only [one_mul]
    have h_twist₂ : checkCornerTwist s₂ := by

      change checkCornerTwist (apply_move_list M_z1 s₁)


      apply moves_check_corner_twist M_z1 s₁

      exact h_twist₁ -- Since z₁ doesn't affect corner ori
    have h_edge₂ : checkEdgeFlip s₂ := by

      change checkEdgeFlip (apply_move_list M_z1 s₁)

      apply moves_preserves_checkEdgeFlip M_z1 s₁

      exact h_edge₁


    have h_corner_perm_even₂ : Perm.sign s₂.corner_perm = 1 := by

      rw [h_corner_perm₂]

      rw [h_sign₁]
      exact h_center_perm_even₁
    have h_corner_perm_inv_even₂ : Perm.sign s₂.corner_perm⁻¹ = 1 := by
      rw [Perm.sign_inv]
      exact h_corner_perm_even₂

    obtain ⟨c₁, h_c₁_solv, h_c₁_cperm_eq, h_c₁_eperm_id, h_c₁_zperm_id, h_c₁_eori_zero⟩ :=
      lemma3_corner_perm_achievability (s₂.corner_perm⁻¹) h_corner_perm_inv_even₂
    obtain ⟨M_c1, h_c1_moves⟩ := h_c₁_solv


    let s₃ := apply_move_list M_c1 s₂

    have h_corner_perm₃ : s₃.corner_perm = 1 := by

      change (apply_move_list M_c1 s₂).corner_perm = 1

      rw [apply_move_list_corner_perm_comp M_c1 s₂]

      rw [← h_c1_moves]

      rw [h_c₁_cperm_eq]

      aesop -- aesop GOAT!
    have h_center_perm₃ : s₃.center_perm = 1 := by
      -- State goal explicitly using definition of s₃
      change (apply_move_list M_c1 s₂).center_perm = 1

      rw [apply_move_list_center_perm_comp M_c1 s₂]

      rw [← h_c1_moves]

      rw [h_c₁_zperm_id]

      simp only [one_mul]

      exact h_center_perm₂
    have h_edge_perm₃ : s₃.edge_perm = s₂.edge_perm := by

      change (apply_move_list M_c1 s₂).edge_perm = s₂.edge_perm

      rw [apply_move_list_edge_perm_comp M_c1 s₂]

      rw [← h_c1_moves]

      rw [h_c₁_eperm_id]

      simp only [one_mul]
    have h_twist₃ : checkCornerTwist s₃ := by

      change checkCornerTwist (apply_move_list M_c1 s₂)

      apply moves_check_corner_twist M_c1 s₂

      exact h_twist₂
    have h_edge₃ : checkEdgeFlip s₃ := by

      change checkEdgeFlip (apply_move_list M_c1 s₂)

      apply moves_preserves_checkEdgeFlip M_c1 s₂

      exact h_edge₂

    -- Step 4: Fix edge permutation τ

    obtain ⟨e₁, h_e₁_solv, h_e₁_eperm_eq, h_e₁_cperm_id, h_e₁_zperm_id⟩ :=
      lemma5_edge_perm_achievability (s₃.edge_perm⁻¹)

    obtain ⟨M_e1, h_e1_moves⟩ := h_e₁_solv

    let s₄ := apply_move_list M_e1 s₃

    have h_perm₄ : s₄.corner_perm = 1 ∧ s₄.edge_perm = 1 ∧ s₄.center_perm = 1 := by
      constructor
      · -- Prove s₄.corner_perm = 1


        change (apply_move_list M_e1 s₃).corner_perm = 1

        rw [apply_move_list_corner_perm_comp M_e1 s₃]
        rw [← h_e1_moves]

        rw [h_e₁_cperm_id]

        simp only [one_mul]

        exact h_corner_perm₃
      · constructor
        · -- Prove s₄.edge_perm = 1


          change (apply_move_list M_e1 s₃).edge_perm = 1

          rw [apply_move_list_edge_perm_comp M_e1 s₃]
          rw [← h_e1_moves]

          rw [h_e₁_eperm_eq]

          aesop
        ·


          change (apply_move_list M_e1 s₃).center_perm = 1

          rw [apply_move_list_center_perm_comp M_e1 s₃]
          rw [← h_e1_moves]

          rw [h_e₁_zperm_id]

          simp only [one_mul]

          exact h_center_perm₃

    -- Step 5: Check orientations of s₄
    have h_twist₄ : checkCornerTwist s₄ := by

      change checkCornerTwist (apply_move_list M_e1 s₃)
      apply moves_check_corner_twist M_e1 s₃

      exact h_twist₃

    have h_edge₄_holds : checkEdgeFlip s₄ := by

      change checkEdgeFlip (apply_move_list M_e1 s₃)

      apply moves_preserves_checkEdgeFlip M_e1 s₃

      exact h_edge₃

    have h_edge₄_zero : s₄.edge_ori = fun _ => 0 := by

      funext i

      have h_flip_i := h_edge₄_holds i

      simp only [getPieceTypeInSlot, h_perm₄.2.1, inv_one, Perm.one_apply] at h_flip_i


      rw [edgeDelta] at h_flip_i

      simp only [eq_self] at h_flip_i
      rw [if_true] at h_flip_i

      rw [sub_self] at h_flip_i

      exact h_flip_i

    -- Step 6 concluded:
    have h_s₄_solvable_final : IsSolvable s₄ := lemma6_corner_twist_solvability s₄ h_perm₄ h_edge₄_zero h_twist₄

    -- Step 7: Combine solvability
    have h_s3_solv : IsSolvable s₃ := by

      have iff_e1 := solvability_iff_apply_move_list M_e1 s₃

      exact iff_e1.mp h_s₄_solvable_final
    have h_s2_solv : IsSolvable s₂ := by
      have iff_c1 := solvability_iff_apply_move_list M_c1 s₂
      exact iff_c1.mp h_s3_solv

    have h_s1_solv : IsSolvable s₁ := by
      have iff_z1 := solvability_iff_apply_move_list M_z1 s₁
      exact iff_z1.mp h_s2_solv

    by_cases h_sign_final : (Perm.sign s.center_perm = 1)
      aesop

    ·
      have h_s1_eq_R_s : s₁ = apply_move R s := by
        simp only [s₁, h_sign_final, if_false]
        aesop
      rw [h_s1_eq_R_s] at h_s1_solv

      exact (solvability_iff_apply_move R s).mp h_s1_solv

end FourRubik
