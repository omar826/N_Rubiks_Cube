import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Ring.CharZero
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Units
import NRubiksCube.Piece

/-!
Defines the type of "Illegal n×n×n Rubik's cubes". Thes are all possible n×n×n Rubik's cubes that
can be assembled by using the 8 available corners. In particular, there is no regard for
solvability, and "impossible" positions like a rotated corner are allowed.

We define a group structure in `TwoIllegalRubik`, and define the "Rubik's cube invariant", a
surjective group homomorphism into `ℤ₃` whose kernel will be shown to consist of precisely the
solvable Rubik's cubes.
-/

theorem ZMod.cases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by
  decide

open Orientation Equiv

/-- Permutations of pieces in 2×2×2 Rubik's cube. -/
structure TwoIllegalRubik where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic
deriving instance Fintype for TwoIllegalRubik

attribute [simp] TwoIllegalRubik.corner_cyclic

namespace TwoIllegalRubik

variable {cube₁ cube₂ cube : TwoIllegalRubik}

@[ext]
theorem ext (h : ∀ (c : CornerPiece), cube₁.cornerPieceEquiv c = cube₂.cornerPieceEquiv c) :
    cube₁ = cube₂ := by
  let ⟨c₁, _⟩ := cube₁
  let ⟨c₂, _⟩ := cube₂
  simp [Equiv.ext_iff]
  exact h

/-- The solved 2×2×2 Rubik's cube. -/
instance : One TwoIllegalRubik where
  one := ⟨1, by simp⟩

instance : Inhabited TwoIllegalRubik where
  default := 1

@[simp]
theorem cornerPieceEquiv_one : cornerPieceEquiv 1 = 1 :=
  rfl

/-- The product of two 2×2×2 Rubik's cubes is the 2×2×2 Rubik's cube where the first's scramble is
performed before the second's. -/
instance : Mul TwoIllegalRubik :=
  ⟨fun cube₁ cube₂ ↦ by
    refine ⟨cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv, fun c ↦ ?_⟩
    simp [cube₁.corner_cyclic, cube₂.corner_cyclic]⟩

@[simp]
theorem cornerPieceEquiv_mul (cube₁ cube₂ : TwoIllegalRubik) :
    cornerPieceEquiv (cube₁ * cube₂) = cornerPieceEquiv cube₁ * cornerPieceEquiv cube₂ :=
  rfl

@[simp]
theorem corner_cyclic_inv (cube : TwoIllegalRubik) (c : CornerPiece) :
    cube.cornerPieceEquiv⁻¹ c.cyclic = (cube.cornerPieceEquiv⁻¹ c).cyclic := by
  apply Eq.symm
  rw [← cube.cornerPieceEquiv.inv_apply_self (CornerPiece.cyclic _)]
  rw [cube.corner_cyclic, Perm.apply_inv_self]

theorem cornerPieceEquiv_equiv (cube : TwoIllegalRubik) {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) :
    cube.cornerPieceEquiv c₁ ≈ cube.cornerPieceEquiv c₂ := by
  obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
  · rfl
  · rw [corner_cyclic]
    exact CornerPiece.cyclic_equiv _
  · rw [corner_cyclic]
    exact (CornerPiece.cyclic_equiv _).symm

/-- The inverse of a 2×2×2 Rubik's cube is obtained by performing its moves backwards. --/
instance : Inv TwoIllegalRubik :=
  ⟨fun cube ↦ by
    refine ⟨cube.cornerPieceEquiv⁻¹, fun c ↦ ?_⟩
    simp [cube.corner_cyclic]⟩

@[simp]
theorem cornerPieceEquiv_inv (cube : TwoIllegalRubik) :
    cube⁻¹.cornerPieceEquiv = cube.cornerPieceEquiv⁻¹ :=
  rfl

/-- The Illegal 2×2×2 Rubik's cube group. -/
instance : Group TwoIllegalRubik where
  mul_assoc a b c := by
    ext; rfl
  one_mul a := by
    ext; rfl
  mul_one a := by
    ext; rfl
  inv_mul_cancel a := by
    ext; simp

/-- `cornerPieceEquiv` as a monoid homomorphism. -/
@[simps]
def cornerPieceEquivHom : TwoIllegalRubik →* Perm CornerPiece where
  toFun := cornerPieceEquiv
  map_one' := rfl
  map_mul' := cornerPieceEquiv_mul

/-- A 2×2×2 Rubik's cube defines a permutation of corners. -/
def cornerEquiv : TwoIllegalRubik →* Perm Corner where
  toFun cube := by
    refine ⟨Quotient.lift (fun x ↦ ⟦cube.cornerPieceEquiv x⟧) ?_,
      Quotient.lift (fun x ↦ ⟦(cube.cornerPieceEquiv)⁻¹ x⟧) ?_, fun c ↦ ?_, fun c ↦ ?_⟩
    · intro c₁ c₂ h
      apply Quotient.sound
      apply cube.cornerPieceEquiv_equiv
      exact h
    · intro c₁ c₂ h
      apply Quotient.sound
      obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h
      · rfl
      · rw [corner_cyclic_inv]
        exact CornerPiece.cyclic_equiv _
      · rw [corner_cyclic_inv]
        exact (CornerPiece.cyclic_equiv _).symm
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.inv_apply_self]
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.apply_inv_self]
  map_one' := by
    ext e
    refine Quotient.inductionOn e ?_
    exact fun _ ↦ rfl
  map_mul' cube₁ cube₂ := by
    ext e
    refine Quotient.inductionOn e ?_
    simp

theorem cornerEquiv_mk (cube : TwoIllegalRubik) (c : CornerPiece) :
    cornerEquiv cube ⟦c⟧ = ⟦cube.cornerPieceEquiv c⟧ :=
  rfl

theorem cornerEquiv_one : cornerEquiv 1 = 1 :=
  map_one _

theorem cornerEquiv_of_cornerPieceEquiv_eq_one (h : cornerPieceEquiv cube = 1) :
    cornerEquiv cube = 1 := by
  ext c
  refine c.inductionOn ?_
  simp [cornerEquiv_mk, h]

/-- In a 2×2×2 Rubik's cube where all corners are in their correct position, the "corner value" of a
corner represents the number of **counterclockwise** turns required to solve it. -/
def cornerValue (cube : TwoIllegalRubik) (c : Corner) : ZMod 3 :=
  c.lift (fun c ↦ (cornerPieceEquiv cube c).value Axis.x - c.value Axis.x) (by
    intro c₁ c₂ h
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h <;> simp
  )

theorem cornerValue_mk (cube : TwoIllegalRubik) (c : CornerPiece) :
    cornerValue cube ⟦c⟧ = (cornerPieceEquiv cube c).value Axis.x - c.value Axis.x :=
  rfl

theorem cornerValue_eq_zero (hc : cornerEquiv cube = 1) {c : CornerPiece} :
    cornerValue cube ⟦c⟧ = 0 ↔ cube.cornerPieceEquiv c = c := by
  rw [cornerValue_mk, sub_eq_zero, CornerPiece.value_eq_iff_of_equiv, eq_comm]
  rw [← Corner.eq, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_eq_one (hc : cornerEquiv cube = 1) {c : CornerPiece} :
    cornerValue cube ⟦c⟧ = 1 ↔ cube.cornerPieceEquiv c = c.cyclic := by
  have : (1 + (1 + 1) : ZMod 3) = 0 := rfl
  rw [cornerValue_mk, CornerPiece.value_cyclic', CornerPiece.value_cyclic', sub_eq_iff_eq_add,
    add_comm, ← sub_eq_iff_eq_add, sub_sub, sub_sub, this, sub_zero,
    CornerPiece.value_eq_iff_of_equiv, ← CornerPiece.cyclic_inj, CornerPiece.cyclic₃]
  rw [← Corner.eq, Corner.mk_cyclic, Corner.mk_cyclic, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_eq_two (hc : cornerEquiv cube = 1) {c : CornerPiece} :
    cornerValue cube ⟦c⟧ = 2 ↔ cube.cornerPieceEquiv c = c.cyclic.cyclic := by
  have : (2 + 1 : ZMod 3) = 0 := rfl
  rw [cornerValue_mk, sub_eq_iff_eq_add, CornerPiece.value_cyclic', add_comm, sub_eq_iff_eq_add,
    add_assoc, this, add_zero, CornerPiece.value_eq_iff_of_equiv,
    ← CornerPiece.cyclic_inj, ← CornerPiece.cyclic_inj, CornerPiece.cyclic₃]
  rw [← Corner.eq, Corner.mk_cyclic, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_mul (hc₁ : cornerEquiv cube₁ = 1) (hc₂ : cornerEquiv cube₂ = 1) (c : Corner) :
    cornerValue (cube₁ * cube₂) c = cornerValue cube₁ c + cornerValue cube₂ c := by
  have hc₃ : cornerEquiv (cube₁ * cube₂) = 1 := by rw [map_mul, hc₁, hc₂, one_mul]
  have H₁ : (1 + 1 : ZMod 3) = 2 := rfl
  have H₂ : (1 + 2 : ZMod 3) = 0 := rfl
  have H₃ : (2 + 1 : ZMod 3) = 0 := rfl
  have H₄ : (2 + 2 : ZMod 3) = 1 := rfl
  refine c.inductionOn ?_
  intro c
  obtain h₁ | h₁ | h₁ := ZMod.cases (cube₁.cornerValue ⟦c⟧) <;>
  obtain h₂ | h₂ | h₂ := ZMod.cases (cube₂.cornerValue ⟦c⟧) <;>
  rw [h₁, h₂] <;>
  simp only [cornerValue_eq_zero hc₁, cornerValue_eq_zero hc₂, cornerValue_eq_one hc₁,
    cornerValue_eq_one hc₂, cornerValue_eq_two hc₁, cornerValue_eq_two hc₂] at h₁ h₂ <;>
  simp [cornerValue_eq_zero hc₃, cornerValue_eq_one hc₃, cornerValue_eq_two hc₃, H₁, H₂, H₃, H₄,
    h₁, h₂]

theorem cornerPieceEquiv_value (cube : TwoIllegalRubik) (c : CornerPiece) (a : Axis) :
    (cube.cornerPieceEquiv c).value a =
    (cube.cornerPieceEquiv (c.withAxis a)).value a + c.value a := by
  obtain h | h | h := CornerPiece.equiv_iff.1 (CornerPiece.withAxis_equiv c a)
  · rw [h]
    conv_rhs => right; rw [← h]
    rw [CornerPiece.value_withAxis, add_zero]
  · rw [h, corner_cyclic, CornerPiece.value_cyclic, add_assoc, left_eq_add,
      CornerPiece.value_of_snd]
    · rfl
    · rw [← c.cyclic₃, ← h]
      simp
  · conv_lhs => rw [← h]
    rw [corner_cyclic, CornerPiece.value_cyclic, add_right_inj, CornerPiece.value_of_thd]
    rw [← h]
    simp

theorem cornerRotationAux (cube₁ cube₂ : TwoIllegalRubik) (c : Corner) (a : Axis) :
    (cube₁.cornerPieceEquiv (cube₂.cornerPieceEquiv (c.toCornerPiece a))).value a =
      (cube₁.cornerPieceEquiv ((cornerEquiv cube₂ c).toCornerPiece a)).value a +
      (cube₂.cornerPieceEquiv (c.toCornerPiece a)).value a := by
  refine Quotient.inductionOn c ?_
  intro c
  dsimp [cornerEquiv_mk]
  conv_lhs => rw [cornerPieceEquiv_value]
  rw [add_left_inj, CornerPiece.withAxis_eq_of_equiv]
  exact cornerPieceEquiv_equiv _ (c.withAxis_equiv a)

/-- To calculate the amount of corner rotation mod 3, we fix an arbitrary axis (here the X axis) and
count the number of **counterclockwise** corner rotations needed to orient the pieces of the
corresponding axis to said axis.

This is an invariant under any valid move. -/
def cornerRotation : TwoIllegalRubik →* Multiplicative (ZMod 3) where
  toFun cube := ∏ c : Corner,
    (Multiplicative.ofAdd <| (cube.cornerPieceEquiv (c.toCornerPiece Axis.x)).value Axis.x)
  map_one' := by
    convert Finset.prod_const_one
    simp
  map_mul' cube₁ cube₂ := by
    dsimp
    simp_rw [cornerRotationAux, ofAdd_add, Finset.prod_mul_distrib, mul_left_inj]
    rw [Finset.prod_equiv (cornerEquiv cube₂)] <;>
    simp

/-- Rotates a single corner **clockwise**. -/
def rotateCorner (c : Corner) : TwoIllegalRubik where
  cornerPieceEquiv := c.rotateEquiv
  corner_cyclic := c.rotateEquiv_cyclic

theorem cornerPieceEquiv_rotateCorner (c : Corner) :
    cornerPieceEquiv (rotateCorner c) = c.rotateEquiv :=
  rfl

@[simp]
theorem cornerPieceEquiv_rotateCorner_self (c : CornerPiece) :
    cornerPieceEquiv (rotateCorner ⟦c⟧) c = c.cyclic := by
  rw [cornerPieceEquiv_rotateCorner, Corner.rotateEquiv_self]

@[simp]
theorem cornerPieceEquiv_rotateCorner_inv_self (c : CornerPiece) :
    (cornerPieceEquiv (rotateCorner ⟦c⟧))⁻¹ c = c.cyclic.cyclic := by
  rw [cornerPieceEquiv_rotateCorner, Corner.rotateEquiv_inv_self]

@[simp]
theorem cornerRotation_rotateCorner :
    ∀ c, cornerRotation (rotateCorner c) = Multiplicative.ofAdd 1 := by
  decide

/-- The **2×2×2 Rubik's cube invariant**. This is actually just the `cornerRotation`
of a 2×2×2 Rubik's cube.

A 2×2×2 Rubik's cube is solvable iff it lies in the kernel of this homomorphism. -/
def invariant : TwoIllegalRubik →* Multiplicative (ZMod 3) :=
  cornerRotation

/-- A constructive right inverse for the invariant. -/
def invariant_inv : Multiplicative (ZMod 3) → TwoIllegalRubik :=
  fun a ↦ (rotateCorner default) ^ a.1

theorem invariant_leftInverse : Function.LeftInverse invariant invariant_inv := by
  sorry

theorem invariant_surjective : Function.Surjective invariant :=
  invariant_leftInverse.surjective

/-- A Rubik's cube is valid when it has invariant 1. We want to show that this condition
is equivalent to being solvable. -/
def IsValid (cube : TwoIllegalRubik) : Prop :=
  cube ∈ invariant.ker

instance : DecidablePred IsValid :=
  fun cube ↦ inferInstanceAs (Decidable (invariant cube = 1))

theorem isValid_one : IsValid 1 :=
  one_mem _

theorem IsValid.mul (h₁ : IsValid cube₁) (h₂ : IsValid cube₂) : IsValid (cube₁ * cube₂) :=
  mul_mem h₁ h₂

theorem IsValid.inv (h : IsValid cube) : IsValid cube⁻¹ :=
  inv_mem h

theorem isValid_iff :
    IsValid cube ↔ cornerRotation cube = 1 := by
  rw [IsValid, invariant]
  simp only [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one]

theorem IsValid.cornerRotation (h : IsValid cube) : cornerRotation cube = 1 :=
  isValid_iff.1 h

end TwoIllegalRubik

/-- The subgroup of valid 2×2×2 Rubik's cubes, i.e. those that can be reached
using only valid moves. -/
def TwoRubik : Subgroup TwoIllegalRubik :=
  TwoIllegalRubik.invariant.ker

namespace TwoRubik

instance : Fintype TwoRubik :=
  Subtype.fintype TwoIllegalRubik.IsValid

theorem isValid (cube : TwoRubik) : cube.val.IsValid :=
  cube.2

end TwoRubik
