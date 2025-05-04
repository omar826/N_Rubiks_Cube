/-
This file is adapted from the vihdzp/rubik-lean4 repository:
https://github.com/vihdzp/rubik-lean4

Original code licensed under Apache-2.0.
Some parts have been modified significantly.
-/
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Defs
import NRubiksCube.Equiv
import NRubiksCube.Orientation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

/-!
Defines structures for the pieces in an n×n×n Rubik's cube.

We subdivide the edges and corners into
their individual stickers. This gives us `EdgePiece`s and `CornerPiece`s, which can be
identified with `IsAdjacent` oriented pairs, and `IsAdjacent₃` oriented triples, so that
permutations of these tuples yield the other pieces in the same edge or corner.

`Edge` and `Corner` are then defined as quotients of `EdgePiece` and `CornerPiece` under the
relation of being in the same edge or corner..

We ignore centremost piece for odd cubes, as they're always fixed in place, and subdivide the rest
of the centre pieces into `CentreSquareEdge` and `CentreSquareCorner` pieces.
-/

open Orientation

/-- A corner piece is an ordered triple of pairwise adjacent orientations, oriented as the standard
basis. -/
structure CornerPiece : Type where
  fst : Orientation
  snd : Orientation
  thd : Orientation
  isAdjacent₃ : IsAdjacent₃ fst snd thd
deriving instance DecidableEq, Fintype for CornerPiece

namespace CornerPiece

/--
two corner pieces are equal if they have the same
fst and snd orientations.
-/
theorem ext {c₁ c₂ : CornerPiece} (hf : c₁.fst = c₂.fst) (hs : c₁.snd = c₂.snd): c₁ = c₂ := by
    obtain ⟨f₁, s₁, t₁, h₁⟩ := c₁
    obtain ⟨f₂, s₂, t₂, h₂⟩ := c₂
    dsimp at *
    subst hf hs
    simpa using h₁.congr h₂

/--
two corner pieces are equal iff they have the same
fst and snd orientations.
-/
theorem ext_iff {c₁ c₂ : CornerPiece} : c₁ = c₂ ↔ c₁.fst = c₂.fst ∧ c₁.snd = c₂.snd := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hf, hs⟩
    exact ext hf hs


/--
fst and snd orient of a corner piece are adjacent.
-/
theorem isAdjacent (c : CornerPiece) : IsAdjacent c.fst c.snd :=
  c.isAdjacent₃.isAdjacent

/--
default corner piece is U B L.
-/
instance Inhabited : Inhabited CornerPiece where
  default := ⟨U, B, L, by decide⟩

instance : Repr CornerPiece :=
  ⟨fun c ↦ [c.fst, c.snd, c.thd].repr⟩

instance : LinearOrder CornerPiece :=
  LinearOrder.lift' (fun c ↦ [c.fst, c.snd]) (fun _ _ ↦ by simp [ext_iff])

theorem ne (e : CornerPiece) : e.fst ≠ e.snd ∧ e.snd ≠ e.thd ∧ e.thd ≠ e.fst := e.isAdjacent₃.ne

/-- Permutes the colors in a corner cyclically.
(fst, snd, thd) -> (snd, thd, fst).
-/
def cyclic (c : CornerPiece) : CornerPiece :=
  ⟨_, _, _, c.isAdjacent₃.cyclic⟩
/--
cyclic(a, b, c) = (b, c, a)
-/
@[simp]
theorem cyclic_mk {a b c : Orientation} (h : IsAdjacent₃ a b c) : cyclic ⟨a, b, c, h⟩ = ⟨b, c, a, h.cyclic⟩ :=
  rfl

@[simp]
theorem cyclic_fst (c : CornerPiece) : c.cyclic.fst = c.snd :=
  rfl

@[simp]
theorem cyclic_snd (c : CornerPiece) : c.cyclic.snd = c.thd :=
  rfl

@[simp]
theorem cyclic_thd (c : CornerPiece) : c.cyclic.thd = c.fst :=
  rfl

/--
cyclic₃(c) = c
-/
@[simp]
theorem cyclic₃ (c : CornerPiece) : c.cyclic.cyclic.cyclic = c :=
  rfl

/--
cyclic is injective.
-/
@[simp]
theorem cyclic_inj  {c₁ c₂ : CornerPiece} : c₁.cyclic = c₂.cyclic ↔ c₁ = c₂ := by
  constructor
  · exact congr_arg (cyclic ∘ cyclic)
  · rintro rfl
    rfl


/--
cyclic(c) ≠ c
-/
@[simp]
theorem cyclic_ne (c : CornerPiece) : c.cyclic ≠ c := by
  rw [ne_eq, ext_iff, not_and, cyclic_fst]
  intro h
  cases c.isAdjacent.ne h.symm

/--
cyclic₂(c) ≠ c
-/
@[simp]
theorem cyclic_cyclic_ne (c : CornerPiece) : c.cyclic.cyclic ≠ c :=
  (cyclic_ne c.cyclic.cyclic).symm

/--
(a,b,c) is a corner piece → c = a⨯ b
-/
theorem axis_thd (c : CornerPiece) : c.thd.axis = c.fst.axis.other c.snd.axis := by
  rw [c.isAdjacent₃.eq_cross, axis_cross]

/-- Constructs the finset containing the corner's orientations. -/
def toFinset (c : CornerPiece) : Finset Orientation :=
  ⟨{c.fst, c.snd, c.thd}, by
    obtain ⟨h₁, h₂, h₃⟩ := c.isAdjacent₃.ne
    simpa using ⟨⟨h₁, h₃.symm⟩, h₂⟩⟩

/--
c.toFinset.val = {c.fst, c.snd, c.thd}
-/
theorem toFinset_val (c : CornerPiece) : c.toFinset.val = {c.fst, c.snd, c.thd} :=
  rfl

theorem mem_toFinset{a : Orientation} {c : CornerPiece} :
  a ∈ c.toFinset ↔ a = c.fst ∨ a = c.snd ∨ a = c.thd := by
    rw [toFinset]
    simp
/--
applying cyclic to a corner piece does not change the finset of orientations.
-/

@[simp]
theorem cyclic_toFinset (c : CornerPiece) : c.cyclic.toFinset = c.toFinset := by
  have (a b c : Orientation) : ({a, b, c} : Multiset _) = {c, a, b} := by
    change a ::ₘ b ::ₘ c ::ₘ 0 = c ::ₘ a ::ₘ b ::ₘ 0
    rw [Multiset.cons_swap b, Multiset.cons_swap a]
  simp_rw [toFinset, cyclic, this]

/-- Returns the unique corner piece sharing a corner, with the orientation of the given axis.
withAxis((a, b, c), x) = (b, c, a) if b.axis = x
-/
def withAxis (c : CornerPiece) (a : Axis) : CornerPiece :=
  if c.fst.axis = a then c else if c.snd.axis = a then c.cyclic else c.cyclic.cyclic
/--
withAxis(c, x).fst.axis = x
-/

@[simp]
theorem axis_withAxis_fst (c : CornerPiece) (a : Axis) : (c.withAxis a).fst.axis = a := by
  rw [withAxis]
  split_ifs with h₁ h₂
  · exact h₁
  · rwa [cyclic_fst]
  · rw [cyclic_fst, cyclic_snd, axis_thd, Axis.other_eq_iff c.isAdjacent]
    exact ⟨Ne.symm h₁, Ne.symm h₂⟩

/--
withAxis is invariant under cyclic.
-/
@[simp]
theorem withAxis_cyclic (c : CornerPiece) (a : Axis) : c.cyclic.withAxis a = c.withAxis a := by
  simp [withAxis, cyclic]
  split_ifs with h₁ h₂ h₃ h₄ h₅ <;>
  try rfl
  · exact (c.isAdjacent (h₁ ▸ h₂)).elim
  · exact (c.cyclic.cyclic.isAdjacent (h₄ ▸ h₃)).elim
  · rw [axis_thd, ← ne_eq, Axis.other_ne_iff c.isAdjacent] at h₃
    obtain rfl | rfl := h₃
    · exact (h₅ rfl).elim
    · exact (h₁ rfl).elim

/-- The "value" of a corner piece is the number of **counterclockwise** rotations needed to orient
a specific face towards its corresponding axis.
eg) value((a, b, c), b.axis) = 1
-/
def value (c : CornerPiece) (a : Axis) : ZMod 3 :=
  if c.fst.axis = a then 0 else if c.thd.axis = a then 1 else 2


theorem value_of_fst {c : CornerPiece} {a : Axis} (h : c.fst.axis = a) : c.value a = 0 :=
  if_pos h

theorem value_of_snd {c : CornerPiece} {a : Axis} (h : c.snd.axis = a) : c.value a = 2 := by
  have : c.thd.axis ≠ a := (h.symm.trans_ne c.cyclic.isAdjacent).symm
  rw [value, if_neg (ne_of_ne_of_eq c.isAdjacent h), if_neg this]

theorem value_of_thd {c : CornerPiece} {a : Axis} (h : c.thd.axis = a) : c.value a = 1 := by
  have : c.fst.axis ≠ a := (h.symm.trans_ne c.cyclic.cyclic.isAdjacent).symm
  rw [value, if_neg this, if_pos h]

/--
withAxis(c, x).value(x) = 0
-/
@[simp]
theorem value_withAxis (c : CornerPiece) (a : Axis) : (c.withAxis a).value a = 0 :=
  value_of_fst (axis_withAxis_fst c a)

/--
value(cyclic(c), x) = value(c, x) + 1 mod 3
-/
@[simp]
theorem value_cyclic (c : CornerPiece) (a : Axis) : c.cyclic.value a = c.value a + 1 := by
  rw [value]
  split_ifs with h₁ h₂
  · rw [value_of_snd h₁]
    rfl
  · rw [value_of_fst h₂, zero_add]
  · rw [value_of_thd, one_add_one_eq_two]
    rw [c.isAdjacent₃.eq_cross, axis_cross, Axis.other_eq_iff c.isAdjacent]
    exact ⟨Ne.symm h₂, Ne.symm h₁⟩
/--
value(c, x) = value(cyclic(c), x) - 1 mod 3
-/
theorem value_cyclic' (c : CornerPiece) (a : Axis) : c.value a = c.cyclic.value a - 1 :=
  eq_sub_iff_add_eq.2 (value_cyclic c a).symm

/--
toFinset(a) = toFinset(b), is an equivalence relation.

Two corner pieces are equivalent if they
represent the same physical piece in the cube.
-/
instance : Setoid CornerPiece where
  r c₁ c₂ := c₁.toFinset = c₂.toFinset
  iseqv := by
    constructor
    · exact fun x ↦ rfl
    · exact Eq.symm
    · exact Eq.trans
/--
a ≈ b ↔ toFinset(a) = toFinset(b)
-/
theorem equiv_def {c₁ c₂ : CornerPiece} : c₁ ≈ c₂ ↔ c₁.toFinset = c₂.toFinset :=
  Iff.rfl
/--
a ≈ b → a and b are equal or cyclic.
-/
theorem equiv_iff : ∀ {c₁ c₂ : CornerPiece},
    c₁ ≈ c₂ ↔ c₁ = c₂ ∨ c₁ = c₂.cyclic ∨ c₁.cyclic = c₂ := by
    simp_rw [equiv_def]
    decide

theorem equiv_iff' {c₁ c₂ : CornerPiece} : c₁ ≈ c₂ ↔ c₁ = c₂ ∨ c₁ = c₂.cyclic ∨ c₁ = c₂.cyclic.cyclic := by
  rw [equiv_iff]
  convert Iff.rfl using 3
  rw [← cyclic_inj, cyclic₃]

instance : DecidableRel (α := CornerPiece) (· ≈ ·) :=
  fun _ _ ↦ decidable_of_iff _ equiv_iff.symm

theorem cyclic_equiv (c : CornerPiece) : c.cyclic ≈ c :=
  c.cyclic_toFinset

/--
c and c.withAxis(a) are equivalent.
-/
theorem withAxis_equiv (c : CornerPiece) (a : Axis) : c.withAxis a ≈ c := by
  rw [withAxis]
  split_ifs
  · rfl
  · exact cyclic_equiv c
  · exact (cyclic_equiv _).trans (cyclic_equiv c)


/--
if c₁ ≈ c₂, then c₁.withAxis(a) = c₂.withAxis(a).
-/
theorem withAxis_eq_of_equiv {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) (a : Axis) :
    c₁.withAxis a = c₂.withAxis a := by
  obtain rfl | rfl | rfl := equiv_iff.1 h
  · rfl
  · rw [withAxis_cyclic]
  · rw [withAxis_cyclic]

/--
if c₁ ≈ c₂ and c₁.value(a) = c₂.value(a), then c₁ = c₂.
-/
theorem value_eq_iff_of_equiv{c₁ c₂ : CornerPiece} {a : Axis} (hc : c₁ ≈ c₂)
    : c₁.value a = c₂.value a ↔ c₁ = c₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ congr_arg (fun x ↦ x.value a) h⟩
  rw [equiv_iff] at hc
  obtain rfl | rfl | rfl := hc
  · rfl
  · simp at h
    contradiction
  · simp at h
    contradiction
end CornerPiece

/--
corners are the equivalence class of cornerpiece
-/
def Corner : Type := Quotient CornerPiece.instSetoid

namespace Corner

/--
Provides a default corner instance
-/
instance : Inhabited Corner :=
  Quotient.instInhabitedQuotient _

instance : DecidableEq Corner :=
  Quotient.decidableEq

instance : Fintype Corner :=
  Quotient.fintype _

@[simp]
protected theorem eq {c₁ c₂ : CornerPiece} : (⟦c₁⟧ : Corner) = ⟦c₂⟧ ↔ c₁ ≈ c₂ :=
  Quotient.eq

/-- Builds a `Corner`, inferring the adjacency condition. -/
protected abbrev mk (a b c : Orientation) (h : IsAdjacent₃ a b c := by decide) : Corner :=
  ⟦CornerPiece.mk a b c h⟧

/--
⟦c.cyclic⟧ = ⟦c⟧
-/
@[simp]
theorem mk_cyclic (c : CornerPiece) : (⟦c.cyclic⟧ : Corner) = ⟦c⟧ :=
  Quotient.sound c.cyclic_toFinset

/-- Constructs the finset containing the edge's orientations. -/
def toFinset : Corner → Finset Orientation :=
  Quotient.lift CornerPiece.toFinset (fun _ _ ↦ id)

@[simp]
theorem toFinset_mk (c : CornerPiece) : toFinset ⟦c⟧ = c.toFinset :=
  rfl

/--toFinset is injective-/
theorem toFinset_injective : Function.Injective toFinset := by
  intro c₁ c₂
  refine Quotient.inductionOn₂ c₁ c₂ ?_
  intro c₁ c₂ h
  rwa [toFinset_mk, toFinset_mk, ← CornerPiece.equiv_def, ← Corner.eq] at h

@[simp]
theorem toFinset_inj (c₁ c₂ : Corner) : c₁.toFinset = c₂.toFinset ↔ c₁ = c₂ :=
  toFinset_injective.eq_iff

unsafe instance : Repr Corner :=
  ⟨fun c _ ↦ repr c.toFinset⟩


#eval (Corner.mk U B L ) -- {U, B, L}

/-- An "arbitrary" computable linear order. -/
instance : LinearOrder Corner :=
  LinearOrder.lift' (fun c ↦ Finset.Colex.toColex c.toFinset) (fun _ _ ↦ by simp)

/-- Given a corner and an axis, you can recover a unique corner piece within that corner with that
axis first -/
def toCornerPiece (c : Corner) (a : Axis) : CornerPiece :=
  c.lift (fun c ↦ CornerPiece.withAxis c a) (by
    intro _ _ h
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h <;>
    simp
  )

@[simp]
theorem toCornerPiece_mk (c : CornerPiece) (a : Axis) : toCornerPiece ⟦c⟧ a = c.withAxis a :=
  rfl

@[simp]
theorem axis_toCornerPiece (c : Corner) (a : Axis) : (c.toCornerPiece a).fst.axis = a := by
  refine c.inductionOn ?_
  intro c
  rw [toCornerPiece_mk, CornerPiece.axis_withAxis_fst]

@[simp]
theorem mk_toCornerPiece (c : Corner) (a : Axis) : ⟦c.toCornerPiece a⟧ = c := by
  refine c.inductionOn ?_
  intro c
  rw [toCornerPiece_mk, Quotient.eq]
  exact CornerPiece.withAxis_equiv c a

@[simp]
theorem value_toCornerPiece (c : Corner) (a : Axis) : (c.toCornerPiece a).value a = 0 := by
  refine c.inductionOn ?_
  intro c
  rw [toCornerPiece_mk, CornerPiece.value_withAxis]

/-- Returns the permutation of corner pieces resulting from rotating a given corner
**clockwise**. -/
def rotateEquiv (c : Corner) : Equiv.Perm CornerPiece :=
  c.lift (fun c ↦ Equiv.cycle c c.cyclic c.cyclic.cyclic) (by
    intro _ _ h
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h <;>
      dsimp <;>
      repeat rw [Equiv.cycle_cyclic]
  )

/--
rotateEquiv(⟦(a,b,c)⟧) = ((a,b,c), (b,c,a), (c,a,b))
-/
theorem rotateEquiv_mk (c : CornerPiece) :
    rotateEquiv ⟦c⟧ = Equiv.cycle c c.cyclic c.cyclic.cyclic :=
  rfl

/--
((a,b,c), (b,c,a), (c,a,b))(a,b,c) = (b,c,a)
-/
@[simp]
theorem rotateEquiv_self (c : CornerPiece) : rotateEquiv ⟦c⟧ c = c.cyclic := by
  rw [rotateEquiv_mk, Equiv.cycle_fst]
  · exact (CornerPiece.cyclic_ne _).symm
  · exact CornerPiece.cyclic_cyclic_ne _

@[simp]
theorem rotateEquiv_inv_self (c : CornerPiece) : (rotateEquiv ⟦c⟧)⁻¹ c = c.cyclic.cyclic := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, ← mk_cyclic, ← mk_cyclic, rotateEquiv_self,
    CornerPiece.cyclic₃]

theorem rotateEquiv_of_ne {c : Corner} {a : CornerPiece} :
    c ≠ ⟦a⟧ → c.rotateEquiv a = a := by
  refine c.inductionOn ?_
  intro c hc
  rw [ne_eq, Corner.eq, @comm _ (· ≈ ·), CornerPiece.equiv_iff', not_or, not_or] at hc
  rw [rotateEquiv_mk, Equiv.cycle_apply_of_ne hc.1 hc.2.1 hc.2.2]

theorem rotateEquiv_inv_of_ne {c : Corner} {a : CornerPiece} (hc : c ≠ ⟦a⟧) :
    c.rotateEquiv⁻¹ a = a := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, rotateEquiv_of_ne hc]

@[simp]
theorem mk_rotateEquiv (c : Corner) (a : CornerPiece) :
    ⟦c.rotateEquiv a⟧ = (⟦a⟧ : Corner) := by
  obtain rfl | ha := eq_or_ne c ⟦a⟧
  · rw [rotateEquiv_mk, Quotient.eq, Equiv.cycle_fst]
    · exact a.cyclic_equiv
    · rw [ne_eq, CornerPiece.cyclic_inj]
      exact a.cyclic_ne.symm
    · exact a.cyclic_cyclic_ne
  · rw [rotateEquiv_of_ne ha]

@[simp]
theorem mk_rotateEquiv_inv (c : Corner) (a : CornerPiece) :
    ⟦c.rotateEquiv⁻¹ a⟧ = (⟦a⟧ : Corner) := by
  conv_rhs => rw [← c.rotateEquiv.apply_symm_apply a]
  rw [mk_rotateEquiv, Equiv.Perm.inv_def]

@[simp]
theorem rotateEquiv_cyclic (c : Corner) (a : CornerPiece) :
    c.rotateEquiv a.cyclic = (c.rotateEquiv a).cyclic := by
  obtain rfl | ha := eq_or_ne c ⟦a⟧
  · rw [rotateEquiv_mk, Equiv.cycle_fst a.cyclic.cyclic_ne.symm a.cyclic_cyclic_ne,
      Equiv.cycle_snd a.cyclic_ne.symm a.cyclic_cyclic_ne]
  · rw [rotateEquiv_of_ne, rotateEquiv_of_ne ha]
    rwa [mk_cyclic]

end Corner

/-- The type `PRubik` contains a `Perm EdgePiece` field, which assigns to each edge piece position in
the cube a particular sticker. -/
structure SingleEdgePiece : Type where
  /-- The first and "distinguished" orientation in the edge piece. -/
  fst : Orientation
  /-- The second orientation in the edge piece. -/
  snd : Orientation
  /-- Both orientations are adjacent. -/
  isAdjacent : IsAdjacent fst snd

deriving instance DecidableEq, Fintype for SingleEdgePiece

namespace SingleEdgePiece

variable {e₁ e₂ : SingleEdgePiece}

instance : Inhabited SingleEdgePiece :=
  ⟨SingleEdgePiece.mk U B (by decide)⟩

instance : Repr SingleEdgePiece :=
  ⟨fun e ↦ [e.fst, e.snd].repr⟩

protected theorem ne (e : SingleEdgePiece) : e.fst ≠ e.snd :=
  e.isAdjacent.ne

-- Not marked as `ext` since it creates undesirable goals with `PRubik.ext`.
theorem ext (hf : e₁.fst = e₂.fst) (hs : e₁.snd = e₂.snd) : e₁ = e₂ := by
  cases e₁
  cases e₂
  simpa using ⟨hf, hs⟩

theorem ext_iff : e₁ = e₂ ↔ e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hf, hs⟩
    exact ext hf hs

/-- An "arbitrary" computable linear order. -/
instance : LinearOrder SingleEdgePiece :=
  LinearOrder.lift' (fun e ↦ [e.fst, e.snd]) (fun _ _ ↦ by simp [ext_iff])

/-- Builds an `EdgePiece`, automatically inferring the adjacency condition. -/
protected abbrev mk' (a b : Orientation) (h : IsAdjacent a b := by decide) : SingleEdgePiece :=
  SingleEdgePiece.mk a b h

/-- Constructs the other edge piece sharing an edge. -/
def flip (e : SingleEdgePiece) : SingleEdgePiece :=
  ⟨_, _, e.isAdjacent.symm⟩

@[simp]
theorem flip_mk (h : IsAdjacent a b) : flip ⟨a, b, h⟩ = ⟨b, a, h.symm⟩ :=
  rfl

@[simp]
theorem flip_fst (e : SingleEdgePiece) : e.flip.fst = e.snd :=
  rfl

@[simp]
theorem flip_snd (e : SingleEdgePiece) : e.flip.snd = e.fst :=
  rfl

@[simp]
theorem flip₂ (e : SingleEdgePiece) : e.flip.flip = e :=
  rfl

@[simp]
theorem flip_inj : e₁.flip = e₂.flip ↔ e₁ = e₂ :=
  (Function.LeftInverse.injective flip₂).eq_iff

@[simp]
theorem flip_ne (e : SingleEdgePiece) : e.flip ≠ e := by
  rw [ne_eq, SingleEdgePiece.ext_iff, flip_fst, flip_snd, not_and]
  intro h
  cases e.isAdjacent.ne h.symm

/-- Constructs the finset containing the edge's orientations. -/
def toFinset (e : SingleEdgePiece) : Finset Orientation :=
  ⟨{e.fst, e.snd}, by simpa using e.isAdjacent.ne⟩

theorem toFinset_val (e : SingleEdgePiece) : e.toFinset.val = {e.fst, e.snd} :=
  rfl

theorem mem_toFinset {e : SingleEdgePiece} : a ∈ e.toFinset ↔ a = e.fst ∨ a = e.snd := by
  rw [toFinset]
  simp

@[simp]
theorem flip_toFinset (e : SingleEdgePiece) : e.flip.toFinset = e.toFinset := by
  rw [toFinset]
  simp_rw [Multiset.pair_comm]
  rfl

/-- Returns the unique edge piece sharing a edge, with the given orientation.

If the edge does not contain the orientation, we return some dummy edge piece. -/
def withOrientation (e : SingleEdgePiece) (a : Orientation) : SingleEdgePiece :=
  if e.fst = a then e else if e.snd = a then e.flip else default

theorem withOrientation_fst (e : SingleEdgePiece) (ha : a ∈ e.toFinset) :
    (e.withOrientation a).fst = a := by
  rw [withOrientation]
  obtain rfl | rfl := mem_toFinset.1 ha
  · rw [if_pos rfl]
  · rw [if_neg e.isAdjacent.ne, if_pos rfl, flip_fst]

@[simp]
theorem withOrientation_flip (e : SingleEdgePiece) : e.flip.withOrientation a = e.withOrientation a := by
  rw [withOrientation, withOrientation]
  by_cases ha : a ∈ e.toFinset
  · have h := e.isAdjacent.ne
    obtain rfl | rfl := mem_toFinset.1 ha <;>
    simp [h, h.symm]
  · rw [mem_toFinset, not_or] at ha
    simp [Ne.symm ha.1, Ne.symm ha.2]

instance : Setoid SingleEdgePiece where
  r e₁ e₂ := e₁.toFinset = e₂.toFinset
  iseqv := by
    constructor
    · exact fun x ↦ rfl
    · exact Eq.symm
    · exact Eq.trans

theorem equiv_def : e₁ ≈ e₂ ↔ e₁.toFinset = e₂.toFinset :=
  Iff.rfl

theorem equiv_iff : ∀ {e₁ e₂ : SingleEdgePiece}, e₁ ≈ e₂ ↔ e₁ = e₂ ∨ e₁ = e₂.flip := by
  simp_rw [equiv_def]
  decide

instance : DecidableRel (α := SingleEdgePiece) (· ≈ ·) :=
  fun _ _ ↦ decidable_of_iff _ equiv_iff.symm

theorem flip_equiv (e : SingleEdgePiece) : e.flip ≈ e :=
  e.flip_toFinset

end SingleEdgePiece

/-- An edge is the equivalence class of edge pieces sharing an edge. -/
def SingleEdge : Type := Quotient SingleEdgePiece.instSetoid

namespace SingleEdge

instance : Inhabited SingleEdge :=
  Quotient.instInhabitedQuotient _

instance : DecidableEq SingleEdge :=
  Quotient.decidableEq

instance : Fintype SingleEdge :=
  Quotient.fintype _

@[simp]
protected theorem eq {e₁ e₂ : SingleEdgePiece} : (⟦e₁⟧ : SingleEdge) = ⟦e₂⟧ ↔ e₁ ≈ e₂ :=
  Quotient.eq

/-- Builds an `Edge`, automatically inferring the adjacency condition. -/
protected abbrev mk (a b : Orientation) (h : IsAdjacent a b := by decide) : SingleEdge :=
  ⟦SingleEdgePiece.mk a b h⟧

@[simp]
theorem mk_flip (e : SingleEdgePiece) : (⟦e.flip⟧ : SingleEdge) = ⟦e⟧ :=
  Quotient.sound e.flip_equiv

/-- Constructs the finset containing the edge's orientations. -/
def toFinset : SingleEdge → Finset Orientation :=
  Quotient.lift SingleEdgePiece.toFinset (fun _ _ ↦ id)

@[simp]
theorem toFinset_mk (e : SingleEdgePiece) : toFinset ⟦e⟧ = e.toFinset :=
  rfl

theorem toFinset_injective : Function.Injective toFinset := by
  intro e₁ e₂
  refine Quotient.inductionOn₂ e₁ e₂ ?_
  intro e₁ e₂ h
  rwa [toFinset_mk, toFinset_mk, ← SingleEdgePiece.equiv_def, ← SingleEdge.eq] at h

@[simp]
theorem toFinset_inj (e₁ e₂ : SingleEdge) : e₁.toFinset = e₂.toFinset ↔ e₁ = e₂ :=
  toFinset_injective.eq_iff

unsafe instance : Repr SingleEdge :=
  ⟨fun e _ ↦ repr e.toFinset⟩

/-- An "arbitrary" computable linear order. -/
instance : LinearOrder SingleEdge :=
  LinearOrder.lift' (fun e ↦ Finset.Colex.toColex e.toFinset) (fun _ _ ↦ by simp)

/-- Computably chooses an edge piece equivalent to this edge. -/
def out (e : SingleEdge) : SingleEdgePiece :=
  (Finset.univ.sort (· ≤ ·)).choose (fun x ↦ ⟦x⟧ = e) ⟨Quotient.out e, by simp⟩

@[simp]
theorem out_eq (e : SingleEdge) : ⟦e.out⟧ = e :=
  (List.choose_spec (fun x ↦ ⟦x⟧ = e) _ _).2

theorem mk_out (e : SingleEdgePiece) : SingleEdge.out ⟦e⟧ ≈ e :=
  Quotient.exact (out_eq _)

/-- Given an edge and an orientation it contains, you can recover a unique edge piece within that
edge with that orientation.

If the edge does not contain the orientation, we return some dummy edge piece. -/
def toSingleEdgePiece (e : SingleEdge) (a : Orientation) : SingleEdgePiece :=
  e.lift (fun e ↦ SingleEdgePiece.withOrientation e a) (by
    intro _ _ h
    obtain rfl | rfl := SingleEdgePiece.equiv_iff.1 h <;>
    simp
  )

/-- Returns the permutation of edge pieces resulting from flipping a given edge. -/
def flipEquiv (e : SingleEdge) : Equiv.Perm SingleEdgePiece :=
  e.lift (fun e ↦ Equiv.swap e e.flip) (by
    intro _ _ h
    obtain rfl | rfl := SingleEdgePiece.equiv_iff.1 h
    · rfl
    · dsimp
      rw [Equiv.swap_comm]
  )

@[simp]
theorem flipEquiv_mk (e : SingleEdgePiece) : flipEquiv ⟦e⟧ = Equiv.swap e e.flip :=
  rfl

theorem flipEquiv_of_ne {e : SingleEdge} {a : SingleEdgePiece} : e ≠ ⟦a⟧ → e.flipEquiv a = a := by
  refine e.inductionOn ?_
  intro e he
  rw [ne_eq, SingleEdge.eq, @comm _ (· ≈ ·), SingleEdgePiece.equiv_iff, not_or] at he
  rw [flipEquiv_mk, Equiv.swap_apply_of_ne_of_ne he.1 he.2]

@[simp]
theorem mk_flipEquiv (e : SingleEdge) (a : SingleEdgePiece) : ⟦e.flipEquiv a⟧ = (⟦a⟧ : SingleEdge) := by
  obtain rfl | ha := eq_or_ne e ⟦a⟧
  · simp
  · rw [flipEquiv_of_ne ha]

@[simp]
theorem flipEquiv_flip (e : SingleEdge) (a : SingleEdgePiece) : e.flipEquiv a.flip = (e.flipEquiv a).flip := by
  obtain rfl | ha := eq_or_ne e ⟦a⟧
  · simp
  · rw [flipEquiv_of_ne, flipEquiv_of_ne ha]
    rwa [mk_flip]

@[simp]
theorem flipEquiv_flipEquiv (e : SingleEdge) : e.flipEquiv * e.flipEquiv = 1 := by
  refine e.inductionOn ?_
  intro e
  rw [flipEquiv_mk, Equiv.swap_mul_self]

end SingleEdge

/-




single edge ends here




-/
inductive EdgeType | A | B
  deriving DecidableEq, Fintype, Repr, Inhabited

structure EdgePiece where
  fst : Orientation
  snd : Orientation
  isAdjacent : IsAdjacent fst snd
  piece_type : EdgeType
deriving DecidableEq, Fintype, Repr

namespace EdgePiece

instance : Inhabited EdgePiece where
  default := ⟨U, B, by decide, EdgeType.A⟩


theorem ne (e : EdgePiece) : e.fst ≠ e.snd := e.isAdjacent.ne

theorem ext {e₁ e₂ : EdgePiece}
    (h₁ : e₁.fst = e₂.fst) (h₂ : e₁.snd = e₂.snd) (ht : e₁.piece_type = e₂.piece_type) :
    e₁ = e₂ := by
  cases e₁; cases e₂; simp_all -- Use simp_all to handle field equalities

theorem ext_iff {e₁ e₂ : EdgePiece} :
    e₁ = e₂ ↔ e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd ∧ e₁.piece_type = e₂.piece_type := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h₁, h₂, ht⟩; exact ext h₁ h₂ ht

@[simps fst snd piece_type] -- Auto-generate theorems for field access
def flip (e : EdgePiece) : EdgePiece :=
  ⟨e.snd, e.fst, e.isAdjacent.symm, e.piece_type⟩

theorem flip_mk (a b : Orientation) (h : IsAdjacent a b) (t : EdgeType) :
    flip ⟨a, b, h, t⟩ = ⟨b, a, h.symm, t⟩ :=
  rfl

@[simp]
theorem flip₂ (e : EdgePiece) : e.flip.flip = e := by
  cases e; rfl -- Use `cases` to destruct the structure and simplify


@[simp]
theorem flip_inj {e₁ e₂ : EdgePiece} : e₁.flip = e₂.flip ↔ e₁ = e₂ :=
  Function.Injective.eq_iff (Function.LeftInverse.injective flip₂) -- Use flip₂ as left inverse

theorem flip_ne (e : EdgePiece) : e.flip ≠ e := by
  intro h_eq
  have h_fst := congr_arg EdgePiece.fst h_eq
  simp at h_fst -- e.snd = e.fst
  exact e.ne h_fst.symm -- Contradicts e.fst ≠ e.snd

def toFinset (e : EdgePiece) : Finset Orientation :=
  {e.fst, e.snd} -- Uses implicit conversion from Multiset + Nodup proof

/-- The underlying multiset `val` of the `toFinset` result. -/
theorem toFinset_val (e : EdgePiece) : e.toFinset.val = {e.fst, e.snd} := by
  sorry

theorem mem_toFinset {a : Orientation} {e : EdgePiece} :
    a ∈ e.toFinset ↔ a = e.fst ∨ a = e.snd := by
  simp [toFinset, Finset.mem_insert, Finset.mem_singleton]

/-- Applying `flip` does not change the `Finset` of orientations. -/
@[simp]
theorem flip_toFinset (e : EdgePiece) : e.flip.toFinset = e.toFinset := by
  ext x; simp [mem_toFinset, flip_fst, flip_snd, or_comm]

/-- Defines the equivalence relation for `EdgePiece`s. Two pieces are
    equivalent if they have the same pair of orientations (colors),
    regardless of their `piece_type` (A/B) or internal order (fst/snd).
    This groups the two physical pieces of a coupled pair into the same class. -/
instance instSetoid : Setoid EdgePiece where
  r e₁ e₂ := e₁.toFinset = e₂.toFinset
  iseqv := by -- Standard proof for equivalence relation based on equality
    constructor
    · intro x; rfl
    · intro x y h; exact h.symm
    · intro x y z h₁ h₂; exact h₁.trans h₂

/-- The definition of the equivalence relation `≈` on `EdgePiece`. -/
theorem equiv_def {e₁ e₂ : EdgePiece} : e₁ ≈ e₂ ↔ e₁.toFinset = e₂.toFinset :=
  Iff.rfl

-- Optional: A theorem connecting the equivalence relation to the structure fields.
-- Note: This does *not* imply e₁.piece_type = e₂.piece_type.
theorem equiv_iff_orientations {e₁ e₂ : EdgePiece} :
    e₁ ≈ e₂ ↔ (e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd) ∨ (e₁.fst = e₂.snd ∧ e₁.snd = e₂.fst) := by
  sorry

end EdgePiece

/-- Represents a physical edge location on the cube, abstracting away the
    specific orientation (fst/snd order) and the piece type (A/B) of the
    `EdgePiece` currently occupying it.
    Defined as the Quotient of `EdgePiece` by the `Setoid` instance based on `toFinset`.
    `⟦e⟧` denotes the `Edge` corresponding to the `EdgePiece` `e`. -/
def Edge : Type := Quotient EdgePiece.instSetoid

namespace Edge

/-- Provides a default `Edge` instance. -/
instance : Inhabited Edge :=
  Quotient.instInhabitedQuotient _

/-- Two `Edge`s `⟦e₁⟧` and `⟦e₂⟧` are equal if and only if the underlying
    `EdgePiece`s `e₁` and `e₂` are equivalent (`e₁ ≈ e₂`), meaning they
    have the same `toFinset`. -/
@[simp]
protected theorem eq {e₁ e₂ : EdgePiece} : (⟦e₁⟧ : Edge) = ⟦e₂⟧ ↔ e₁ ≈ e₂ :=
  Quotient.eq -- Fundamental property of quotients

end Edge
/-
/-- An edge piece is an ordered pair of adjacent orientations along with an index. -/
structure EdgePiece (n : {m : ℕ // m ≥ 3}) : Type where
  fst : Orientation
  snd : Orientation
  isAdjacent : IsAdjacent fst snd
  index : Fin (n.val - 2)

deriving DecidableEq, Fintype

namespace EdgePiece

instance (n : {m : ℕ // m ≥ 3}) : Inhabited (EdgePiece n) where
  default := ⟨U, B, by decide, ⟨0, by omega⟩⟩

instance (n : {m : ℕ // m ≥ 3}) : Repr (EdgePiece n) :=
  ⟨fun e ↦ ([e.fst, e.snd], e.index).repr⟩

theorem ne (n : {m : ℕ // m ≥ 3}) (e : EdgePiece n) : e.fst ≠ e.snd := e.isAdjacent.ne

theorem ext {n : {m : ℕ // m ≥ 3}} (e₁ e₂ : EdgePiece n)
  (h₁ : e₁.fst = e₂.fst) (h₂ : e₁.snd = e₂.snd) (hi : e₁.index = e₂.index) :
  e₁ = e₂ := by
    cases e₁
    cases e₂
    simp [h₁, h₂, hi]
    exact ⟨h₁, h₂, hi⟩

theorem ext_iff {n : {m : ℕ // m ≥ 3}} (e₁ e₂ : EdgePiece n) :
  e₁ = e₂ ↔ e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd ∧ e₁.index = e₂.index := by
    constructor
    · intro h
      simp [h]
    · intro h
      cases e₁
      cases e₂
      simp [h]
      exact h

/-- Constructs the other edge piece sharing an edge and index. -/
def flip {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : EdgePiece n :=
  ⟨_, _, e.isAdjacent.symm, e.index⟩

@[simp]
theorem flip_mk (h : IsAdjacent a b) : flip ⟨a, b, h, k⟩ = ⟨b, a, h.symm, k⟩ :=
  rfl

@[simp]
theorem flip_fst {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : e.flip.fst = e.snd :=
  rfl

@[simp]
theorem flip_snd {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : e.flip.snd = e.fst :=
  rfl

@[simp]
theorem flip₂ {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : e.flip.flip = e :=
  rfl

@[simp]
theorem flip_inj {n : {m : ℕ // m ≥ 3}} (e₁ e₂ : EdgePiece n) :
e₁.flip = e₂.flip ↔ e₁ = e₂ :=
  (Function.LeftInverse.injective flip₂).eq_iff

@[simp]
theorem flip_ne {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : e.flip ≠ e := by
  rw [ne_eq, EdgePiece.ext_iff, flip_fst, flip_snd, not_and]
  intro h
  cases e.isAdjacent.ne h.symm

/-- Constructs the finset containing the edge's orientations. -/
def toFinset {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : Finset Orientation :=
  ⟨{e.fst, e.snd}, by
    have h : e.fst ≠ e.snd := e.isAdjacent.ne
    simp [h]⟩

theorem toFinset_val {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) :
  e.toFinset.val = {e.fst, e.snd} := rfl

theorem mem_toFinset {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) :
  e.fst ∈ e.toFinset.val ∧ e.snd ∈ e.toFinset.val := by
    rw [toFinset_val]
    simp

theorem flip_toFinset {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) :
  (e.flip).toFinset = e.toFinset := by
    rw [toFinset]
    simp_rw [Multiset.pair_comm]
    rfl

@[simp]
theorem flip_index {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) :
  (e.flip).index = e.index := rfl

instance (n : {m : ℕ // m ≥ 3}): Setoid (EdgePiece n) where
  r e₁ e₂ := e₁.toFinset = e₂.toFinset ∧ e₁.index = e₂.index
  iseqv := by
    constructor
    · intro x
      simp
    · intro x y h
      simp [h]
    · intro x y z h₁ h₂
      simp [h₁, h₂]

theorem equiv_def {n : {m : ℕ // m ≥ 3}} {e₁ e₂ : EdgePiece n} :
    e₁ ≈ e₂ ↔ e₁.toFinset = e₂.toFinset ∧ e₁.index = e₂.index := Iff.rfl

theorem flip_equiv {n : {m : ℕ // m ≥ 3}} (e : EdgePiece n) : e.flip ≈ e := by
  simp [equiv_def, e.flip_toFinset]

@[simp]
theorem finset_pair_eq_iff {α : Type*} [DecidableEq α] {a b x y : α} (h₁ : a ≠ b) (h₂ : x ≠ y) :
    ({a, b} : Finset α) = ({x, y} : Finset α) ↔ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  simp [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton, or_self]
  constructor
  · intro H
    have ha := H a
    simp [h₁] at ha
    have hb := H b
    simp [Ne.symm h₁] at hb
    cases ha with
    | inl ha_eq_x =>
      cases hb with
      | inl hb_eq_x =>
          exfalso; exact h₁ (ha_eq_x ▸ hb_eq_x.symm)
      | inr hb_eq_y =>
          left; exact ⟨ha_eq_x, hb_eq_y⟩
    | inr ha_eq_y =>
      cases hb with
      | inl hb_eq_x =>
          right; exact ⟨ha_eq_y, hb_eq_x⟩
      | inr hb_eq_y =>
          exfalso; exact h₁ (ha_eq_y ▸ hb_eq_y.symm)
  · intro H
    intro z
    cases H with
    | inl h_match =>
      simp_all only [ne_eq, not_false_eq_true]
    | inr h_swap =>
      simp_all only [ne_eq]
      obtain ⟨left, right⟩ := h_swap
      subst left right
      apply Iff.intro
      · intro a_1
        cases a_1 with
        | inl h =>
          subst h
          simp_all only [or_true]
        | inr h_1 =>
          subst h_1
          simp_all only [or_false]
      · intro a_1
        cases a_1 with
        | inl h =>
          subst h
          simp_all only [or_true]
        | inr h_1 =>
          subst h_1
          simp_all only [or_false]

theorem equiv_iff (n : {m : ℕ // m ≥ 3}) :
    ∀ {e₁ e₂ : EdgePiece n}, e₁ ≈ e₂ ↔ e₁ = e₂ ∨ e₁ = e₂.flip := by
    intro e₁ e₂
    constructor
    · intro h
      simp [equiv_def] at h
      obtain ⟨h₁, h₂⟩ := h
      have h₃ : e₁.toFinset.val = e₂.toFinset.val := by simp [h₁]
      have p₁ : e₁.fst ≠ e₁.snd := e₁.isAdjacent.ne
      have p₂ : e₂.fst ≠ e₂.snd := e₂.isAdjacent.ne
      simp [toFinset_val] at h₃
      have h₄ : e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd ∨ e₁.fst = e₂.snd ∧ e₁.snd = e₂.fst := by
        apply (finset_pair_eq_iff p₁ p₂).1
        apply Finset.eq_of_veq
        simp_all only [ne_eq, Finset.insert_val, Finset.singleton_val, Multiset.mem_singleton,
        not_false_eq_true, Multiset.ndinsert_of_not_mem]
      by_cases c : e₁.fst = e₂.fst ∧ e₁.snd = e₂.snd
      · left
        simp [ext_iff, c, h₂]
      · simp [c] at h₄
        right
        simp [ext_iff, h₄, h₂]
    · intro h
      by_cases h₁ : e₁ = e₂
      · simp [h₁, EdgePiece.equiv_def]
      · simp [h₁] at h
        simp [h, flip_equiv]

end EdgePiece

/-- Identifies edge pieces in an edge. -/
def Edge (n: {m : ℕ // m ≥ 3}) : Type := Quotient (EdgePiece.instSetoid n)

namespace Edge

@[simp]
theorem eq {n : {m : ℕ // m ≥ 3}} (e₁ e₂ : EdgePiece n) : (⟦e₁⟧ : Edge n)= ⟦e₂⟧ ↔ e₁ ≈ e₂ := by
  rw [Quotient.eq]
  exact EdgePiece.equiv_def

end Edge
-/
/-- The edges of concentric squares of centre pieces. Note that such
concentric squares contain edges only when the side length of the square
is atleast 3 (which requires n atleast 5).

These pieces are defined by the side length of the square it belongs to,
their color, as well an index.
TODO: How do we exactly index? and does it matter? -/
structure CentreSquareEdge (n : {m : ℕ // m ≥ 5}) : Type where
  k : Fin (n.val - 4) -- side length - 3
  h : k.val % 2 = (n.val + 1) % 2 -- parity condition
  face : Orientation
  index : Fin (4 * (k.val + 1))

namespace CentreSquareEdge

instance Inhabited (n : {m : ℕ // m ≥ 5}) : Inhabited (CentreSquareEdge n) where
  default :=
    if p : (n.val + 1) % 2 = 0 then
      ⟨⟨0, by omega⟩ , by simp [p], U, 0⟩
    else
      have h : (n.val + 1) % 2 = 1 := by simp at p; exact p
      ⟨⟨1, by omega⟩ , by simp [h], U, 0⟩

theorem ext {n : {m : ℕ // m ≥ 5}} (e₁ e₂ : CentreSquareEdge n)
  (h₁ : e₁.k.val = e₂.k.val) (h₂ : e₁.face = e₂.face) (h₃ : e₁.index.val = e₂.index.val) :
  e₁ = e₂ := by
    cases e₁
    cases e₂
    simp at h₁ h₂ h₃
    simp [h₁, h₂]
    rw [Fin.heq_ext_iff]
    simp [h₃]
    · omega
    · omega

theorem ext_iff {n : {m : ℕ // m ≥ 5}} (e₁ e₂ : CentreSquareEdge n) :
  e₁ = e₂ ↔ e₁.k = e₂.k ∧ e₁.face = e₂.face ∧ e₁.index.val = e₂.index.val := by
    constructor
    · intro h
      cases e₁
      cases e₂
      simp at h
      rw [Fin.heq_ext_iff] at h
      simp [h]
      omega

    · intro h
      cases e₁
      cases e₂
      simp at h
      simp [h]
      rw [Fin.heq_ext_iff]
      · omega
      · omega

end CentreSquareEdge

/-- The centre square edges with the same k-value. -/
def CentreSquareEdgeK (n : {m : ℕ // m ≥ 5}) (k : Fin (n.val - 4))
(_h : k.val % 2 = (n.val + 1) % 2) : Type :=
  {e : CentreSquareEdge n // e.k = k}

/-- The corners of concentric squares of centre pieces. Note that such
concentric squares contain corners only when the sidelength of the square
is atleast 2 (which requires n atleast 4).

These pieces are define by the side length of the square it belongs tozz,
their color, as well as an index ranging from 0 to 3. -/
structure CentreSquareCorner (n : {m : ℕ // m ≥ 4}) : Type where
  k : Fin (n.val - 3) -- side length - 2
  h : k.val % 2 = n.val % 2
  face : Orientation
  index : Fin 4

namespace CentreSquareCorner

instance Inhabited (n : {m : ℕ // m ≥ 4}) : Inhabited (CentreSquareCorner n) where
  default :=
    if p : n.val % 2 = 0 then
      ⟨⟨0, by omega⟩ , by simp [p], U, 0⟩
    else
      have h : n.val % 2 = 1 := by simp at p; exact p
      ⟨⟨1, by omega⟩ , by simp [h], U, 0⟩

theorem ext {n : {m : ℕ // m ≥ 4}} (e₁ e₂ : CentreSquareCorner n)
  (h₁ : e₁.k = e₂.k) (h₂ : e₁.face = e₂.face) (h₃ : e₁.index.val = e₂.index.val) :
  e₁ = e₂ := by
    cases e₁
    cases e₂
    simp at h₁ h₂ h₃
    simp [h₁, h₂]
    omega

theorem ext_iff {n : {m : ℕ // m ≥ 4}} (e₁ e₂ : CentreSquareCorner n) :
  e₁ = e₂ ↔ e₁.k = e₂.k ∧ e₁.face = e₂.face ∧ e₁.index.val = e₂.index.val := by
    constructor
    · intro h
      cases e₁
      cases e₂
      simp at h
      simp [h]
    · intro h
      cases e₁
      cases e₂
      simp at h
      simp [h]
      omega

end CentreSquareCorner

/-- The centre square corners with the same k-value. -/
def CentreSquareCornerK (n : {m : ℕ // m ≥ 4}) (k : Fin (n.val - 3))
(_h : k.val % 2 = n.val % 2) : Type :=
  {e : CentreSquareCorner n // e.k = k}
