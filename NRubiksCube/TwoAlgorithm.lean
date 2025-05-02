
import NRubiksCube.TwoMoves

/-!
This file contains an algorithm which solves any 2×2×2 Rubik's cube satisfying the relevant
invariants. In particular, this allows us to show `isSolvable_iff_isValid`.

The first step is to define sequences of moves to move any three corners to a pre-
determined position. This is implemented as `fixCorners₃`.

We then hardcode algorithms for performing the following two basic operations:

- Permute three corners in a pre-determined position
- Rotate two corners in a pre-determined position

Through the use of conjugates, we are able to generalize these algorithms to any corners. We can then chain these together,
solving one piece at a time until we're done.
-/

open Orientation TwoIllegalRubik

theorem List.length_filter_lt {α : Type*} (a : α) (l : List α) (p : α → Bool) :
    (l.filter p).length < (a :: l).length :=
  (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)

namespace Moves

/-- Given two corners `c₁` and `c₂` in the same face `a`, `moveCornerFace c₁ c₂ a` is the sequence
of moves repeating `a` until `c₂` is sent to `c₁`. See `moveCornerFace_move`. -/
def moveCornerFace (c₁ c₂ : Corner) (a : Orientation) : Moves :=
  let f₁ := (c₁.toCornerPiece a.axis).snd
  let f₂ := (c₂.toCornerPiece a.axis).snd
  List.replicate (
    if f₁ = f₂ then 0 else
    if f₁.rotate a = f₂ then 1 else
    if (f₁.rotate a).rotate a = f₂ then 2 else 3
  ) a

theorem moveCornerFace_move : ∀ {c₁ c₂ : Corner} {a : Orientation},
    a ∈ c₁.toFinset → a ∈ c₂.toFinset → cornerEquiv (move (moveCornerFace c₁ c₂ a)) c₁ = c₂ := by
  decide

/-- A sequence of moves sending a given corner to the `D` face, guaranteeing not to move
`Corner.mk U R B` or `Corner.mk U B L` (unless that's the chosen corner). -/
def fixCornerAux (c : Corner) : Moves × Corner :=
  if D ∈ c.toFinset then ([], c) else
  if c = Corner.mk U L F then (Moves.F2, Corner.mk D R F) else
  if c = Corner.mk U F R then (Moves.F2, Corner.mk D F L) else
  if c = Corner.mk U B L then (Moves.L2, Corner.mk D F L) else (Moves.R2, Corner.mk D R F)

/-- A sequence of moves sending a given corner to `Corner.mk U L F`, guaranteeing not to move
`Corner.mk U R B` or `Corner.mk U B L` (unless that's the chosen corner). -/
def fixCorner (c : Corner) : Moves :=
  let (m, c) := fixCornerAux c
  m ++ moveCornerFace (Corner.mk D R F) c D ++ Moves.F2

@[simp]
theorem fixCorner_move : ∀ c : Corner, cornerEquiv (move (fixCorner c)) (Corner.mk U L F) = c := by
  decide

theorem fixCorner_fix₁ : ∀ {c : Corner}, c ≠ Corner.mk U R B →
    cornerEquiv (move (fixCorner c)) (Corner.mk U R B) = Corner.mk U R B := by
  decide

theorem fixCorner_fix₂ : ∀ {c : Corner}, c ≠ Corner.mk U B L →
    cornerEquiv (move (fixCorner c)) (Corner.mk U B L) = Corner.mk U B L := by
  decide

/-- A sequence of moves sending `c₁` to `Corner.mk U B L` and `c₂` to `Corner.mk U L F`. -/
def fixCorners₂ (c₁ c₂ : Corner) : Moves :=
  let m := fixCorner c₁ ++ Moves.U
  m ++ fixCorner ((cornerEquiv (move m)).symm c₂)

private theorem cornerEquiv_UBL :
    (cornerEquiv (ofOrientation U)) (Corner.mk U B L) = Corner.mk U L F :=
  rfl

theorem fixCorners₂_move₁ {c₁ c₂ : Corner} (h : c₁ ≠ c₂) :
    cornerEquiv (move (fixCorners₂ c₁ c₂)) (Corner.mk U B L) = c₁ := by
  simp [fixCorners₂]
  rw [fixCorner_fix₂, cornerEquiv_UBL, fixCorner_move]
  rwa [ne_eq, Equiv.symm_apply_eq, cornerEquiv_UBL, Equiv.symm_apply_eq, fixCorner_move, eq_comm]

@[simp]
theorem fixCorners₂_move₂ (c₁ c₂ : Corner) :
    cornerEquiv (move (fixCorners₂ c₁ c₂)) (Corner.mk U L F) = c₂ := by
  simp [fixCorners₂]

/-- A sequence of moves sending `c₁` to `Corner.mk U R B`, `c₂` to `Corner.mk U B L`, and `c₃` to
`Corner.mk U L F`. -/
def fixCorners₃ (c₁ c₂ c₃ : Corner) : Moves :=
  let m := fixCorners₂ c₁ c₂ ++ Moves.U
  m ++ fixCorner ((cornerEquiv (move m)).symm c₃)

theorem fixCorners₃_move₁ {c₁ c₂ c₃ : Corner} (h₁ : c₁ ≠ c₂) (h₂ : c₁ ≠ c₃) :
    cornerEquiv (move (fixCorners₃ c₁ c₂ c₃)) (Corner.mk U R B) = c₁ := by
  have : (cornerEquiv (ofOrientation U)) (Corner.mk U R B) = Corner.mk U B L := by decide
  simp [fixCorners₃]
  rw [fixCorner_fix₁, this, fixCorners₂_move₁ h₁]
  rwa [ne_eq, Equiv.symm_apply_eq, this, Equiv.symm_apply_eq, fixCorners₂_move₁ h₁, eq_comm]

theorem fixCorners₃_move₂ (c₁ : Corner) {c₂ c₃ : Corner} (h : c₂ ≠ c₃) :
    cornerEquiv (move (fixCorners₃ c₁ c₂ c₃)) (Corner.mk U B L) = c₂ := by
  simp [fixCorners₃]
  rw [fixCorner_fix₂, cornerEquiv_UBL, fixCorners₂_move₂]
  rwa [ne_eq, Equiv.symm_apply_eq, cornerEquiv_UBL, Equiv.symm_apply_eq, fixCorners₂_move₂, eq_comm]

@[simp]
theorem fixCorners₃_move₃ (c₁ c₂ c₃ : Corner) :
    cornerEquiv (move (fixCorners₃ c₁ c₂ c₃)) (Corner.mk U L F) = c₃ := by
  simp [fixCorners₃]

/-- A sequence of moves cycling `Corner.mk U R B`, `Corner.mk U B L`, and `Corner.mk U L F`. -/
private def cycleCornersAux : Moves :=
  [R, R, D, B, B, D, D, D, F, F, D, B, B, D, D, D, F, F, R, R]

set_option maxRecDepth 1000
private theorem cornerEquiv_cycleCornersAux : cornerEquiv (move cycleCornersAux) =
    Equiv.cycle (Corner.mk U R B) (Corner.mk U B L) (Corner.mk U L F) := by
  decide

/-- A sequence of moves that cycles three corners. -/
def cycleCorners (c₁ c₂ c₃ : Corner) : Moves :=
  if c₁ = c₂ ∨ c₂ = c₃ ∨ c₃ = c₁ then [] else
    let m := fixCorners₃ c₁ c₂ c₃
    m ++ cycleCornersAux ++ m.symm

@[simp]
theorem cornerEquiv_cycleCorners (c₁ c₂ c₃ : Corner) :
    cornerEquiv (move (cycleCorners c₁ c₂ c₃)) = Equiv.cycle c₁ c₂ c₃ := by
  rw [cycleCorners, Equiv.cycle]
  split_ifs with h
  · simp
  · have h' := h
    simp_rw [not_or, ← ne_eq] at h'
    simp [cornerEquiv_cycleCornersAux, ← mul_assoc]
    rw [fixCorners₃_move₁ h'.1 h'.2.2.symm, fixCorners₃_move₂ _ h'.2.1, Equiv.cycle, if_neg h]

/-- A sequence of moves swapping `Corner.mk U B L` and `Corner.mk U L F`. -/
def swapCornersAux : Moves :=
  [L, U, U, L, L, L, U, U, U, L, U, U, R, R, R, U, L, L, L, U, U, U, R]

private theorem cornerEquiv_swapCornersAux :
    cornerEquiv (move swapCornersAux) = Equiv.swap (Corner.mk U B L) (Corner.mk U L F) := by
  decide

/-- A sequence of moves that cycles two corners. -/
def swapCorners (c₁ c₂ : Corner) : Moves :=
  if c₁ = c₂ then [] else
    let m := Moves.fixCorners₂ c₁ c₂
    m ++ Moves.swapCornersAux ++ m.symm

@[simp]
theorem cornerEquiv_swapCorners (c₁ c₂ : Corner) :
    cornerEquiv (move (swapCorners c₁ c₂)) = Equiv.swap c₁ c₂ := by
  rw [swapCorners]
  split_ifs with h
  · simp [h]
    rfl
  · simp [cornerEquiv_swapCornersAux, ← mul_assoc]
    simp [fixCorners₂_move₁ h]

/-- A sequence of moves rotating `Corner.mk U B L` **clockwise** and, `Corner.mk U L F`
**counterclockwise**. -/
def rotateCornersAux : Moves :=
  [L, L, D, D, D, L, L, D, F, F, U, U, U, F, U, L, L, U, L, L, U, U, U, F]

theorem cornerPieceEquiv_rotateCornersAux : cornerPieceEquiv (move rotateCornersAux) =
    (Corner.mk U B L).rotateEquiv * (Corner.mk U L F).rotateEquiv⁻¹ := by
  decide -- this too requires maxRecDepth to be increased.

/-- A sequence of moves that rotates `c₁` **clockwise** and `c₂` **counterclockwise**. -/
def rotateCorners (c₁ c₂ : Corner) : Moves :=
  if c₁ = c₂ then [] else
    let m := fixCorners₂ c₁ c₂
    m ++ rotateCornersAux ++ m.symm

@[simp]
theorem cornerPieceEquiv_rotateCorners (c₁ c₂ : Corner) :
    cornerPieceEquiv (move (rotateCorners c₁ c₂)) = c₁.rotateEquiv * c₂.rotateEquiv⁻¹ := by
  rw [rotateCorners]
  split_ifs with h
  · simp [h]
  · simp only [List.append_assoc, move_append, move_symm, ← mul_assoc, cornerPieceEquiv_mul,
      cornerPieceEquiv_rotateCornersAux, Corner.rotateEquiv_mk, CornerPiece.cyclic_mk,
      Equiv.cycle_inv, cornerPieceEquiv_inv, Equiv.cycle_conj₂]
    congr
    · conv_rhs => rw [← fixCorners₂_move₁ h, cornerEquiv_mk, Corner.rotateEquiv_mk,
        ← corner_cyclic, ← corner_cyclic]
      rfl
    · conv_rhs => rw [← fixCorners₂_move₂ c₁ c₂, cornerEquiv_mk, Corner.rotateEquiv_mk,
        Equiv.cycle_inv, ← corner_cyclic, ← corner_cyclic]
      rfl

@[simp]
theorem cornerEquiv_rotateCorners (c₁ c₂ : Corner) :
    cornerEquiv (move (rotateCorners c₁ c₂)) = 1 := by
  ext c
  refine c.inductionOn ?_
  simp [cornerEquiv_mk]

end Moves

namespace TwoRubik

/-- `other a b x` is whichever of `a` or `b` which is not equal to `x`. -/
def other (a b x : Corner) : Corner :=
  if x = a then b else a

/-- A sequence of moves that puts the cube's corners in their correct position, in the specified
order. -/
def solveCornersAux (cube : TwoRubik) : List Corner → Moves
  | a::b::c::l =>
    let x := (cornerEquiv cube).symm a
    let m := Moves.cycleCorners a x (other b c x)
    let cube' := cube * move m
    m ++ solveCornersAux cube' ((b::c::l).filter fun e ↦ cornerEquiv cube' e ≠ e)
  | a::b::_l =>
    Moves.swapCorners a b
  | _ => []
termination_by l => l.length
decreasing_by exact List.length_filter_lt _ _ _

theorem solveCornersAux_cornerEquiv (cube : TwoRubik) (l : List Corner) (hl : l.Nodup)
    (hc : ∀ c, c ∈ l ↔ cornerEquiv cube c ≠ c) :
    cornerEquiv (TwoIllegalRubik.move (solveCornersAux cube l)) = cornerEquiv cube⁻¹ :=
  match l with
  | [] => by simpa [solveCornersAux, Equiv.ext_iff] using hc
  | [a] => by simp [Equiv.not_equiv_ne_iff] at hc
  | [a, b] => by sorry
  | a::b::c::_l => by sorry

/-- A sequence of moves that puts the cube's corners in their correct position. -/
def solveCorners (cube : TwoRubik) : Moves :=
  solveCornersAux cube ((Finset.univ.filter fun c ↦ cornerEquiv cube c ≠ c).sort (· ≤ ·))

theorem solveCorners_cornerEquiv (cube : TwoRubik) :
    cornerEquiv (TwoIllegalRubik.move (solveCorners cube)) = cornerEquiv cube⁻¹ := by
  apply solveCornersAux_cornerEquiv _ _ (Finset.sort_nodup _ _)
  simp

theorem cornerValue_mul_rotateCorners_fst (cube : TwoRubik) {a b : Corner} : a ≠ b →
    cornerValue (cube * TwoIllegalRubik.move (Moves.rotateCorners a b)) a = cornerValue cube a + 1 := by
  refine a.inductionOn ?_
  intro a ha
  simpa [cornerValue_mk, Corner.rotateEquiv_inv_of_ne ha.symm] using add_sub_right_comm _ _ _

theorem cornerValue_mul_rotateCorners_snd (cube : TwoRubik) {a b : Corner} : a ≠ b →
    cornerValue (cube * TwoIllegalRubik.move (Moves.rotateCorners b a)) a = cornerValue cube a + 2 := by
  have : ((1 + 1) : ZMod 3) = 2 := rfl
  refine a.inductionOn ?_
  intro a ha
  simp [cornerValue_mk, Corner.rotateEquiv_of_ne ha.symm, add_sub_right_comm, add_assoc, this]

theorem cornerValue_mul_rotateCorners_of_ne (cube : TwoRubik) {a b c : Corner} : c ≠ a → c ≠ b →
    cornerValue (cube * TwoIllegalRubik.move (Moves.rotateCorners a b)) c = cornerValue cube c := by
  refine c.inductionOn ?_
  intro c ha hb
  have ha' : a ≠ ⟦b.rotateEquiv⁻¹ c⟧ := by rwa [Corner.mk_rotateEquiv_inv, ne_comm]
  simp [cornerValue_mk, Corner.rotateEquiv_of_ne ha']
  rw [Corner.rotateEquiv_inv_of_ne hb.symm]

/-- A sequence of moves that puts the cube's corners in their correct orientation, in the specified
order. -/
def solveCornerPiecesAux (cube : TwoRubik) : List Corner → Moves
  | a::b::l =>
    let m := if cornerValue cube a = 1 then Moves.rotateCorners b a else Moves.rotateCorners a b
    let cube' := cube * move m
    m ++ solveCornerPiecesAux cube' ((b::l).filter fun c ↦ cornerValue cube' c ≠ 0)
  | _ => []
termination_by l => l.length
decreasing_by exact List.length_filter_lt _ _ _

theorem solveCornerPiecesAux_cornerPieceEquiv (cube : TwoRubik) (l : List Corner) (hl : l.Nodup)
    (h : cornerEquiv cube = 1) (hc : ∀ c, c ∈ l ↔ cornerValue cube c ≠ 0) :
    cornerPieceEquiv (TwoIllegalRubik.move (solveCornerPiecesAux cube l)) =
    cornerPieceEquiv cube⁻¹ :=
  match l with
  | [] => by
    simp_rw [List.not_mem_nil, false_iff, not_not] at hc
    ext c
    simp_rw [solveCornerPiecesAux]
    rw [TwoIllegalRubik.move_nil, cornerPieceEquiv_one, Equiv.Perm.one_apply, cornerPieceEquiv_inv,
      Equiv.Perm.inv_def, Equiv.eq_symm_apply, ← cornerValue_eq_zero]
    · exact hc _
    · exact h
  | [a] => by
    apply (not_ne_iff.2 (TwoRubik.isValid cube).cornerRotation _).elim
    obtain hx | hx | hx := ZMod.cases (TwoIllegalRubik.cornerValue cube a)
    · cases (hc a).1 (List.mem_singleton_self a) hx
    · suffices cube = TwoIllegalRubik.rotateCorner a by
        rw [this, cornerRotation_rotateCorner]
        decide
      ext e
      · obtain rfl | ha := eq_or_ne a ⟦e⟧
        · rwa [cornerPieceEquiv_rotateCorner_self, ← cornerValue_eq_one]
          exact h
        · rwa [cornerPieceEquiv_rotateCorner, Corner.rotateEquiv_of_ne ha,
            ← cornerValue_eq_zero, ← not_ne_iff, ← hc, List.mem_singleton, eq_comm]
          exact h
    · suffices cube = (TwoIllegalRubik.rotateCorner a)⁻¹ by
        rw [this, map_inv, cornerRotation_rotateCorner]
        decide
      ext e
      · rw [cornerPieceEquiv_inv]
        obtain rfl | ha := eq_or_ne a ⟦e⟧
        · rwa [cornerPieceEquiv_rotateCorner_inv_self, ← cornerValue_eq_two]
          exact h
        · rwa [cornerPieceEquiv_rotateCorner, Corner.rotateEquiv_inv_of_ne ha,
            ← cornerValue_eq_zero, ← not_ne_iff, ← hc, List.mem_singleton, eq_comm]
          exact h
  | a::b::l => by sorry

/-- A sequence of moves that puts the cube's corners in their correct orientation. -/
def solveCornerPieces (cube : TwoRubik) : Moves :=
  solveCornerPiecesAux cube ((Finset.univ.filter fun c ↦ cornerValue cube c ≠ 0).sort (· ≤ ·))

theorem solveCornerPieces_cornerPieceEquiv (cube : TwoRubik)
    (hc : cornerEquiv cube = 1) :
    cornerPieceEquiv (TwoIllegalRubik.move (solveCornerPieces cube)) = cornerPieceEquiv cube⁻¹ :=
    by
    apply solveCornerPiecesAux_cornerPieceEquiv _ _ (Finset.sort_nodup _ _) hc
    simp

/-- A sequence of moves that solves a Rubik's cube, i.e. unscrambles it. -/
def solve (c0 : TwoRubik) : Moves :=
  let s1 := solveCorners c0
  let c1 := c0 * move s1
  let s2 := solveCornerPieces c1
  s1 ++ s2

@[simp]
theorem move_solve (cube : TwoRubik) : move (solve cube) = cube⁻¹ := by
  ext x
  simp_rw [solve, move_append, Subgroup.coe_mul, val_move, cornerPieceEquiv_mul]
  rw [solveCornerPieces_cornerPieceEquiv]
  · simp
  · rw [Subgroup.coe_mul, val_move, map_mul, solveCorners_cornerEquiv]
    simp [mul_assoc]

theorem isSolvable (cube : TwoRubik) : IsSolvable cube := by
  rw [← isSolvable_inv_iff]
  exact ⟨solve cube, congr_arg Subtype.val (move_solve cube)⟩

end TwoRubik

namespace TwoIllegalRubik

variable {cube : TwoIllegalRubik}

/-- A valid cube is solvable, i.e. the invariant is a necessary and sufficient condition for
solvability. -/
theorem IsValid.isSolvable (h : IsValid cube) : IsSolvable cube :=
  TwoRubik.isSolvable ⟨_, h⟩

/-- A Rubik's cube is solvable iff it satisfies the invariant. -/
theorem isSolvable_iff_isValid : IsSolvable cube ↔ IsValid cube :=
  ⟨IsSolvable.isValid, IsValid.isSolvable⟩

end TwoIllegalRubik
