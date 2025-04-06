/-
This file is adapted from the vihdzp/rubik-lean4 repository:
https://github.com/vihdzp/rubik-lean4

Original code licensed under Apache-2.0.
Some parts have been modified significantly.
-/
--import Mathlib (cannot do this due to name clashes)
import Mathlib.Data.ZMod.Defs
import NRubiksCube.Equiv
import NRubiksCube.Orientation

namespace Orientation

/-- A corner piece is an ordered triple of pairwise adjacent orientations, oriented as the standard
basis. -/
structure CornerPiece where
  fst : Orientation
  snd : Orientation
  thd : Orientation
  isAdjacent₃ : IsAdjacent₃ fst snd thd

namespace CornerPiece

theorem ext {c₁ c₂ : CornerPiece} (hf : c₁.fst = c₂.fst) (hs : c₁.snd = c₂.snd): c₁ = c₂ := by
    obtain ⟨f₁, s₁, t₁, h₁⟩ := c₁
    obtain ⟨f₂, s₂, t₂, h₂⟩ := c₂
    dsimp at *
    subst hf hs
    simpa using h₁.congr h₂

theorem ext_iff {c₁ c₂ : CornerPiece} : c₁ = c₂ ↔ c₁.fst = c₂.fst ∧ c₁.snd = c₂.snd := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hf, hs⟩
    exact ext hf hs

theorem isAdjacent (c : CornerPiece) : IsAdjacent c.fst c.snd :=
  c.isAdjacent₃.isAdjacent

instance Inhabited : Inhabited CornerPiece where
  default := ⟨U, B, L, by decide⟩

theorem ne (e : CornerPiece) : e.fst ≠ e.snd ∧ e.snd ≠ e.thd ∧ e.thd ≠ e.fst := e.isAdjacent₃.ne

/-- Permutes the colors in a corner cyclically. -/
def cyclic (c : CornerPiece) : CornerPiece :=
  ⟨_, _, _, c.isAdjacent₃.cyclic⟩

theorem cyclic_mk {a b c : Orientation} (h : IsAdjacent₃ a b c) : cyclic ⟨a, b, c, h⟩ = ⟨b, c, a, h.cyclic⟩ :=
  rfl

theorem cyclic_fst (c : CornerPiece) : c.cyclic.fst = c.snd :=
  rfl

theorem cyclic_snd (c : CornerPiece) : c.cyclic.snd = c.thd :=
  rfl

theorem cyclic_thd (c : CornerPiece) : c.cyclic.thd = c.fst :=
  rfl

theorem cyclic₃ (c : CornerPiece) : c.cyclic.cyclic.cyclic = c :=
  rfl

theorem cyclic_inj  {c₁ c₂ : CornerPiece} : c₁.cyclic = c₂.cyclic ↔ c₁ = c₂ := by
  constructor
  · exact congr_arg (cyclic ∘ cyclic)
  · rintro rfl
    rfl

theorem cyclic_ne (c : CornerPiece) : c.cyclic ≠ c := by
  rw [ne_eq, ext_iff, not_and, cyclic_fst]
  intro h
  cases c.isAdjacent.ne h.symm

theorem cyclic_cyclic_ne (c : CornerPiece) : c.cyclic.cyclic ≠ c :=
  (cyclic_ne c.cyclic.cyclic).symm

theorem axis_thd (c : CornerPiece) : c.thd.axis = c.fst.axis.other c.snd.axis := by
  rw [c.isAdjacent₃.eq_cross, axis_cross]

/-- Constructs the finset containing the corner's orientations. -/
def toFinset (e : CornerPiece) : Finset Orientation :=
  ⟨{e.fst, e.snd, e.thd}, by
    obtain ⟨h₁, h₂, h₃⟩ := e.isAdjacent₃.ne
    simpa using ⟨⟨h₁, h₃.symm⟩, h₂⟩⟩

theorem toFinset_val (c : CornerPiece) : c.toFinset.val = {c.fst, c.snd, c.thd} :=
  rfl

theorem mem_toFinset{a : Orientation} {c : CornerPiece} :
  a ∈ c.toFinset ↔ a = c.fst ∨ a = c.snd ∨ a = c.thd := by
    rw [toFinset]
    simp

theorem cyclic_toFinset (c : CornerPiece) : c.cyclic.toFinset = c.toFinset := by
  have (a b c : Orientation) : ({a, b, c} : Multiset _) = {c, a, b} := by
    change a ::ₘ b ::ₘ c ::ₘ 0 = c ::ₘ a ::ₘ b ::ₘ 0
    rw [Multiset.cons_swap b, Multiset.cons_swap a]
  simp_rw [toFinset, cyclic, this]

/-- Returns the unique corner piece sharing a corner, with the orientation of the given axis. -/
def withAxis (c : CornerPiece) (a : Axis) : CornerPiece :=
  if c.fst.axis = a then c else if c.snd.axis = a then c.cyclic else c.cyclic.cyclic

theorem axis_withAxis_fst (c : CornerPiece) (a : Axis) : (c.withAxis a).fst.axis = a := by
  rw [withAxis]
  split_ifs with h₁ h₂
  · exact h₁
  · rwa [cyclic_fst]
  · rw [cyclic_fst, cyclic_snd, axis_thd, Axis.other_eq_iff c.isAdjacent]
    exact ⟨Ne.symm h₁, Ne.symm h₂⟩

theorem withAxis_cyclic (c : CornerPiece) (a : Axis) : c.cyclic.withAxis a = c.withAxis a := sorry

/-- The "value" of a corner piece is the number of **counterclockwise** rotations needed to orient
a specific face towards its corresponding axis. -/
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

theorem value_withAxis (c : CornerPiece) (a : Axis) : (c.withAxis a).value a = 0 :=
  value_of_fst (axis_withAxis_fst c a)

theorem value_cyclic (c : CornerPiece) (a : Axis) : c.cyclic.value a = c.value a + 1 := by
  rw [value]
  split_ifs with h₁ h₂
  · rw [value_of_snd h₁]
    rfl
  · rw [value_of_fst h₂, zero_add]
  · rw [value_of_thd, one_add_one_eq_two]
    rw [c.isAdjacent₃.eq_cross, axis_cross, Axis.other_eq_iff c.isAdjacent]
    exact ⟨Ne.symm h₂, Ne.symm h₁⟩

theorem value_cyclic' (c : CornerPiece) (a : Axis) : c.value a = c.cyclic.value a - 1 :=
  eq_sub_iff_add_eq.2 (value_cyclic c a).symm

instance : Setoid CornerPiece where
  r c₁ c₂ := c₁.toFinset = c₂.toFinset
  iseqv := by
    constructor
    · exact fun x ↦ rfl
    · exact Eq.symm
    · exact Eq.trans

theorem equiv_def {c₁ c₂ : CornerPiece} : c₁ ≈ c₂ ↔ c₁.toFinset = c₂.toFinset :=
  Iff.rfl

theorem equiv_iff : ∀ {c₁ c₂ : CornerPiece},
    c₁ ≈ c₂ ↔ c₁ = c₂ ∨ c₁ = c₂.cyclic ∨ c₁.cyclic = c₂ := sorry

theorem equiv_iff' {c₁ c₂ : CornerPiece} : c₁ ≈ c₂ ↔ c₁ = c₂ ∨ c₁ = c₂.cyclic ∨ c₁ = c₂.cyclic.cyclic := by
  rw [equiv_iff]
  convert Iff.rfl using 3
  rw [← cyclic_inj, cyclic₃]

theorem cyclic_equiv (c : CornerPiece) : c.cyclic ≈ c :=
  c.cyclic_toFinset

theorem withAxis_equiv (c : CornerPiece) (a : Axis) : c.withAxis a ≈ c := by
  rw [withAxis]
  split_ifs
  · rfl
  · exact cyclic_equiv c
  · exact (cyclic_equiv _).trans (cyclic_equiv c)

theorem withAxis_eq_of_equiv {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) (a : Axis) :
    c₁.withAxis a = c₂.withAxis a := by
  obtain rfl | rfl | rfl := equiv_iff.1 h
  · rfl
  · rw [withAxis_cyclic]
  · rw [withAxis_cyclic]

theorem value_eq_iff_of_equiv{c₁ c₂ : CornerPiece} {a : Axis} (hc : c₁ ≈ c₂)
    : c₁.value a = c₂.value a ↔ c₁ = c₂ := sorry
end CornerPiece

/-- Identifies corner pieces in a corner. -/
def Corner : Type := Quotient CornerPiece.instSetoid

/-- An edge piece is an ordered pair of adjacent orientations along with an index. -/
structure EdgePiece (n : {m : ℕ // m ≥ 3}) where
  fst : Orientation
  snd : Orientation
  isAdjacent : IsAdjacent fst snd
  index : Fin (n.val - 2)

namespace EdgePiece

instance (n : {m : ℕ // m ≥ 3}) : Inhabited (EdgePiece n) where
  default := ⟨U, B, by decide, ⟨0, by omega⟩⟩

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

theorem equiv_def {n : {m : ℕ // m ≥ 3}} (e₁ e₂ : EdgePiece n) :
  e₁ ≈ e₂ ↔ e₁.toFinset = e₂.toFinset ∧ e₁.index = e₂.index := Iff.rfl

theorem equiv_iff {n : {m : ℕ // m ≥ 3}} (e₁ e₂ : EdgePiece n) :
  e₁ ≈ e₂ ↔ e₁ = e₂ ∨ e₁ = e₂.flip := by
    simp_rw [equiv_def]
    constructor
    · intro h
      by_cases h₁ : e₁ = e₂
      · simp [h₁]
      · simp [h₁]
        sorry -- TODO: finish this

    · by_cases h : e₁ = e₂
      · simp [h]
      · simp [h]
        intro h₁
        simp [h₁, flip_toFinset, flip_index]

end EdgePiece

/-- Identifies edge pieces in an edge. -/
def Edge (n: {m : ℕ // m ≥ 3}) : Type := Quotient (EdgePiece.instSetoid n)

/-- The edges of concentric squares of centre pieces. Note that such
concentric squares contain edges only when the side length of the square
is atleast 3 (which requires n atleast 5).

These pieces are defined by the side length of the square it belongs to,
their color, as well an index.
TODO: How do we exactly index? and does it matter? -/
structure CentreSquareEdge (n : {m : ℕ // m ≥ 5}) where
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
(h : k.val % 2 = (n.val + 1) % 2) : Type :=
  have h₁ (e : CentreSquareEdge n) (h₂ : e.k = k) : e.k.val % 2 = (n.val + 1) % 2 := by
    rw [h₂]
    exact h
  sorry

/-- The corners of concentric squares of centre pieces. Note that such
concentric squares contain corners only when the sidelength of the square
is atleast 2 (which requires n atleast 4).

These pieces are define by the side length of the square it belongs tozz,
their color, as well as an index ranging from 0 to 3. -/
structure CentreSquareCorner (n : {m : ℕ // m ≥ 4}) where
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
(h : k.val % 2 = n.val % 2) : Type :=
  have h₁ (e : CentreSquareCorner n) (h₂ : e.k = k) : e.k.val % 2 = n.val % 2 := by
    rw [h₂]
    exact h
  sorry

end Orientation
