import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Ring.CharZero
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Units
import NRubiksCube.Piece

/-!
Defines the type of "Illegal n×n×n Rubik's cubes". Thes are all possible n×n×n Rubik's cubes that
can be assembled by using the pieces. In particular, there is no regard for solvability, and
"impossible" positions like a rotated corner or flipped edge are allowed.

We define a group structure in `BigIllegalRubik`, and define the "Rubik's cube invariant", a
surjective group homomorphism into `TODO` whose kernel will be shown to consist of
precisely the solvable Rubik's cubes.
-/

/-- The map `1 → 0`, `-1 → 1`. -/
def Units.toZMod (x : ℤˣ) : ZMod 2 :=
  if x = 1 then 0 else 1

@[simp]
theorem Units.toZMod_mul : ∀ x y : ℤˣ, (x * y).toZMod = x.toZMod + y.toZMod := by
  decide

theorem ZMod.cases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by
  decide

open Orientation Equiv

/-- Permutations of pieces in an big Rubik's cube (n ≥ 5). -/
structure BigIllegalRubik (n : {m : ℕ // m ≥ 5}) where
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm (EdgePiece ⟨n.val, by omega⟩)
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Returns the centre square edge at a given location -/
  centreSquareEdgeEquiv : Perm (CentreSquareEdge ⟨n.val, by omega⟩)
  /-- Returns the centre square corner at a given location -/
  centreSquareCornerEquiv : Perm (CentreSquareCorner ⟨n.val, by omega⟩)
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : (EdgePiece ⟨n.val, by omega⟩)) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic
  /-- Pieces in the same centre square get mapped to pieces in the same centre square -/
  centre_square_edge_square (e : CentreSquareEdge ⟨n.val, by omega⟩) : (centreSquareEdgeEquiv e).k = e.k
  centre_square_corner_square (c : CentreSquareCorner ⟨n.val, by omega⟩) : (centreSquareCornerEquiv c).k = c.k

namespace BigIllegalRubik

@[ext]
theorem ext {n : {m // m ≥ 5}} {cube₁ : BigIllegalRubik n} {cube₂ : BigIllegalRubik n}
  (he : ∀ (e : EdgePiece ⟨n.val, by omega⟩), cube₁.edgePieceEquiv e = cube₂.edgePieceEquiv e)
  (hc : ∀ (c : CornerPiece), cube₁.cornerPieceEquiv c = cube₂.cornerPieceEquiv c)
  (hcse : ∀ (cse : CentreSquareEdge ⟨n.val, by omega⟩), cube₁.centreSquareEdgeEquiv cse = cube₂.centreSquareEdgeEquiv cse)
  (hcsc : ∀ (csc : CentreSquareCorner ⟨n.val, by omega⟩), cube₁.centreSquareCornerEquiv csc = cube₂.centreSquareCornerEquiv csc) :
  cube₁ = cube₂ := by
  let ⟨e₁, c₁, cse₁, csc₁, _, _, _, _⟩ := cube₁
  let ⟨e₂, c₂, cse₂, csc₂, _, _, _, _⟩ := cube₂
  simp
  rw [Equiv.ext_iff, Equiv.ext_iff, Equiv.ext_iff, Equiv.ext_iff]
  exact ⟨he, hc, hcse, hcsc⟩

/-- The solved Big Rubik's cubes. -/
instance (n : {m // m ≥ 5}) : One (BigIllegalRubik n) where
  one := ⟨1, 1, 1, 1, by simp, by simp, by simp, by simp⟩

instance (n : {m // m ≥ 5}) : Inhabited (BigIllegalRubik n) where
  default := 1

@[simp]
theorem edgePieceEquiv_one {n : {m : ℕ // m ≥ 5}} : @edgePieceEquiv n 1 = 1 :=
  rfl

@[simp]
theorem cornerPieceEquiv_one {n : {m : ℕ // m ≥ 5}}: @cornerPieceEquiv n 1 = 1 :=
  rfl

/-- The product of two  Big Rubik's cubes is the Big Rubik's cube where the first's scramble is
performed before the second's. -/
instance (n : {m // m ≥ 5}) : Mul (BigIllegalRubik n) :=
  have h₁ (cube₁ cube₂ : BigIllegalRubik n) (c : EdgePiece ⟨n.val, by omega⟩) :
  (cube₁.edgePieceEquiv * cube₂.edgePieceEquiv) c.flip =
  ((cube₁.edgePieceEquiv * cube₂.edgePieceEquiv) c).flip := by
    simp [cube₁.edge_flip, cube₂.edge_flip]
  have h₂ (cube₁ cube₂ : BigIllegalRubik n) (c : CornerPiece) :
  (cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv) c.cyclic =
  ((cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv) c).cyclic := by
    simp [cube₁.corner_cyclic, cube₂.corner_cyclic]
  have h₃ (cube₁ cube₂ : BigIllegalRubik n) (e : CentreSquareEdge ⟨n.val, by omega⟩) :
  ((cube₁.centreSquareEdgeEquiv * cube₂.centreSquareEdgeEquiv) e).k = e.k := by
    simp [cube₁.centre_square_edge_square, cube₂.centre_square_edge_square]
  have h₄ (cube₁ cube₂ : BigIllegalRubik n) (c : CentreSquareCorner ⟨n.val, by omega⟩) :
  ((cube₁.centreSquareCornerEquiv * cube₂.centreSquareCornerEquiv) c).k = c.k := by
    simp [cube₁.centre_square_corner_square, cube₂.centre_square_corner_square]

  ⟨fun cube₁ cube₂ ↦
    ⟨cube₁.edgePieceEquiv * cube₂.edgePieceEquiv,
    cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv,
    cube₁.centreSquareEdgeEquiv * cube₂.centreSquareEdgeEquiv,
    cube₁.centreSquareCornerEquiv * cube₂.centreSquareCornerEquiv,
    fun e ↦ h₁ cube₁ cube₂ e,
    fun c ↦ h₂ cube₁ cube₂ c,
    fun cse ↦ h₃ cube₁ cube₂ cse,
    fun csc ↦ h₄ cube₁ cube₂ csc⟩⟩


@[simp]
theorem edgePieceEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).edgePieceEquiv = cube₁.edgePieceEquiv * cube₂.edgePieceEquiv := rfl

@[simp]
theorem cornerPieceEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).cornerPieceEquiv = cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv := rfl

@[simp]
theorem centreSquareEdgeEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).centreSquareEdgeEquiv =
  cube₁.centreSquareEdgeEquiv * cube₂.centreSquareEdgeEquiv := rfl

@[simp]
theorem centreSquareCornerEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).centreSquareCornerEquiv =
  cube₁.centreSquareCornerEquiv * cube₂.centreSquareCornerEquiv := rfl

@[simp]
theorem edge_flip_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  (e : (EdgePiece ⟨n.val, by omega⟩)) :
  cube.edgePieceEquiv⁻¹ e.flip = (cube.edgePieceEquiv⁻¹ e).flip := by
    apply Eq.symm
    rw [← cube.edgePieceEquiv.inv_apply_self (EdgePiece.flip _)]
    rw [cube.edge_flip, Perm.apply_inv_self]

@[simp]
theorem corner_cyclic_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n) (c : CornerPiece) :
  cube.cornerPieceEquiv⁻¹ c.cyclic = (cube.cornerPieceEquiv⁻¹ c).cyclic := by
  apply Eq.symm
  rw [← cube.cornerPieceEquiv.inv_apply_self (CornerPiece.cyclic _)]
  rw [cube.corner_cyclic, Perm.apply_inv_self]

@[simp]
theorem centre_square_edge_square_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  (e : CentreSquareEdge ⟨n.val, by omega⟩) : (cube.centreSquareEdgeEquiv⁻¹ e).k = e.k := by
  let e' := cube.centreSquareEdgeEquiv⁻¹ e
  show e'.k = e.k
  have h : e = cube.centreSquareEdgeEquiv e' := by
    unfold e'
    rw [Perm.apply_inv_self]
  rw [h]
  apply Eq.symm
  exact cube.centre_square_edge_square e'

@[simp]
theorem centre_square_corner_square_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  (c : CentreSquareCorner ⟨n.val, by omega⟩) : (cube.centreSquareCornerEquiv⁻¹ c).k = c.k := by
  let c' := cube.centreSquareCornerEquiv⁻¹ c
  show c'.k = c.k
  have h : c = cube.centreSquareCornerEquiv c' := by
    unfold c'
    rw [Perm.apply_inv_self]
  rw [h]
  apply Eq.symm
  exact cube.centre_square_corner_square c'

theorem edgePieceEquiv_equiv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  {e₁ e₂ : EdgePiece ⟨n.val, by omega⟩} (h : e₁ ≈ e₂) :
  cube.edgePieceEquiv e₁ ≈ cube.edgePieceEquiv e₂ := by
    by_cases h₁ : e₁ = e₂
    · simp [h₁]
    · rw [EdgePiece.equiv_iff] at h
      simp [h₁] at h
      rw [h]
      simp [cube.edge_flip]
      simp [EdgePiece.equiv_iff]

theorem cornerPieceEquiv_equiv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) :
  cube.cornerPieceEquiv c₁ ≈ cube.cornerPieceEquiv c₂ := by
    by_cases h₁ : c₁ = c₂
    · simp [h₁]
    · rw [CornerPiece.equiv_iff] at h
      simp [h₁] at h
      by_cases h₂ : c₁ = c₂.cyclic
      · simp [h₂, cube.corner_cyclic, CornerPiece.equiv_iff]
      · simp [h₂] at h
        rw [← h]
        simp [cube.corner_cyclic, CornerPiece.equiv_iff]

/-- The inverse of a Big Rubik's cube is obtained by performing its moves backwards. -/
instance (n : {m // m ≥ 5}) : Inv (BigIllegalRubik n) :=
  ⟨fun cube ↦ ⟨cube.edgePieceEquiv⁻¹, cube.cornerPieceEquiv⁻¹,
    cube.centreSquareEdgeEquiv⁻¹, cube.centreSquareCornerEquiv⁻¹,
    fun e ↦ edge_flip_inv cube e,
    fun c ↦ corner_cyclic_inv cube c,
    fun cse ↦ centre_square_edge_square_inv cube cse,
    fun csc ↦ centre_square_corner_square_inv cube csc⟩⟩

@[simp]
theorem edgePieceEquiv_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n) :
  cube⁻¹.edgePieceEquiv = cube.edgePieceEquiv⁻¹ := rfl

@[simp]
theorem cornerPieceEquiv_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n) :
  cube⁻¹.cornerPieceEquiv = cube.cornerPieceEquiv⁻¹ := rfl

@[simp]
theorem centreSquareEdgeEquiv_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n):
  cube⁻¹.centreSquareEdgeEquiv = cube.centreSquareEdgeEquiv⁻¹ := rfl

@[simp]
theorem centreSquareCornerEquiv_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n):
  cube⁻¹.centreSquareCornerEquiv = cube.centreSquareCornerEquiv⁻¹ := rfl

/-- The Illegal Rubik's cube group. -/
instance (n : {m : ℕ // m ≥ 5}) : Group (BigIllegalRubik n) where
  mul_assoc a b c := by ext <;> rfl
  one_mul a := by ext <;> rfl
  mul_one a := by ext <;> rfl
  inv_mul_cancel a := by
    apply ext
    · intro e
      have h : (edgePieceEquiv 1) e = e := rfl
      rw [h]
      rw [edgePieceEquiv_mul, edgePieceEquiv_inv]
      simp
    · intro c
      have h : (@cornerPieceEquiv n 1) c = c := rfl
      rw [h]
      rw [cornerPieceEquiv_mul, cornerPieceEquiv_inv]
      simp
    · intro cse
      have h : (centreSquareEdgeEquiv 1) cse = cse := rfl
      rw [h]
      rw [centreSquareEdgeEquiv_mul, centreSquareEdgeEquiv_inv]
      simp
    · intro csc
      have h : (centreSquareCornerEquiv 1) csc = csc := rfl
      rw [h]
      rw [centreSquareCornerEquiv_mul, centreSquareCornerEquiv_inv]
      simp

/-- `edgePieceEquiv` as a monoid homomorphism. -/
@[simps]
def edgePieceEquivHom (n : {m : ℕ // m ≥ 5}) :
  BigIllegalRubik n →* Perm (EdgePiece ⟨n.val, by omega⟩) where
  toFun cube := cube.edgePieceEquiv
  map_one' := rfl
  map_mul' a b := edgePieceEquiv_mul a b

/-- `cornerPieceEquiv` as a monoid homomorphism. -/
@[simps]
def cornerPieceEquivHom (n : {m : ℕ // m ≥ 5}) :
  BigIllegalRubik n →* Perm CornerPiece where
  toFun cube := cube.cornerPieceEquiv
  map_one' := rfl
  map_mul' a b := cornerPieceEquiv_mul a b

/-- `centreSquareEdgeEquiv` as a monoid homomorphism. -/
@[simps]
def centreSquareEdgeEquivHom (n : {m : ℕ // m ≥ 5}) :
  BigIllegalRubik n →* Perm (CentreSquareEdge ⟨n.val, by omega⟩) where
  toFun cube := cube.centreSquareEdgeEquiv
  map_one' := rfl
  map_mul' a b := centreSquareEdgeEquiv_mul a b

/-- `centreSquareCornerEquiv` as a monoid homomorphism. -/
@[simps]
def centreSquareCornerEquivHom (n : {m : ℕ // m ≥ 5}) :
  BigIllegalRubik n →* Perm (CentreSquareCorner ⟨n.val, by omega⟩) where
  toFun cube := cube.centreSquareCornerEquiv
  map_one' := rfl
  map_mul' a b := centreSquareCornerEquiv_mul a b

/-- A Rubik's cube defines a permutation of edges. -/
def edgeEquiv (n : {m : ℕ // m ≥ 5}) :
  BigIllegalRubik n →* Perm (Edge ⟨n.val, by omega⟩) where
  toFun cube := by
    refine ⟨Quotient.lift (fun x ↦ ⟦cube.edgePieceEquiv x⟧) ?_,
      Quotient.lift (fun x ↦ ⟦(cube.edgePieceEquiv)⁻¹ x⟧) ?_, fun e ↦ ?_, fun e ↦ ?_⟩
    · intro e₁ e₂ h
      apply Quotient.sound
      rw [EdgePiece.equiv_iff] at h
      by_cases h₁ : e₁ = e₂
      · rw [h₁]
      · simp [h₁] at h
        rw [h]
        rw [cube.edge_flip]
        simp [EdgePiece.equiv_iff]
    · intro e₁ e₂ h
      apply Quotient.sound
      rw [EdgePiece.equiv_iff] at h
      by_cases h₁ : e₁ = e₂
      · rw [h₁]
      · simp [h₁] at h
        rw [h]
        rw[cube.edge_flip_inv]
        simp [EdgePiece.equiv_iff]
    · refine Quotient.inductionOn e ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.inv_apply_self]
    · refine Quotient.inductionOn e ?_
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

theorem edgeEquiv_mk {n : {m : ℕ // m ≥ 5}} (cube : BigIllegalRubik n) (e : EdgePiece ⟨n.val, by omega⟩) :
  edgeEquiv n cube (⟦e⟧) = ⟦cube.edgePieceEquiv e⟧ := rfl

theorem edgeEquiv_one (n : {m : ℕ // m ≥ 5}) : edgeEquiv n 1 = 1 :=
  map_one _

theorem edgeEquiv_of_edgePieceEquiv_eq_one (n : {m : ℕ // m ≥ 5}) {cube : BigIllegalRubik n}
(h : edgePieceEquiv cube = 1) : edgeEquiv n cube = 1 := by
  ext e
  refine e.inductionOn ?_
  simp [edgeEquiv_mk, h]

/-- A Rubik's cube defines a permutation of corners -/
def cornerEquiv (n : {m : ℕ // m ≥ 5}) :
  BigIllegalRubik n →* Perm Corner where
  toFun cube := by
    refine ⟨Quotient.lift (fun x ↦ ⟦cube.cornerPieceEquiv x⟧) ?_,
      Quotient.lift (fun x ↦ ⟦(cube.cornerPieceEquiv)⁻¹ x⟧) ?_, fun c ↦ ?_, fun c ↦ ?_⟩
    · intro c₁ c₂ h
      apply Quotient.sound
      rw [CornerPiece.equiv_iff] at h
      by_cases h₁ : c₁ = c₂
      · rw [h₁]
      · by_cases h₂ : c₁ = c₂.cyclic
        · rw [h₂]
          simp [cube.corner_cyclic, CornerPiece.equiv_iff]
        · simp [h₁, h₂] at h
          rw [← h]
          simp [cube.corner_cyclic, CornerPiece.equiv_iff]
    · intro c₁ c₂ h
      apply Quotient.sound
      rw [CornerPiece.equiv_iff] at h
      by_cases h₁ : c₁ = c₂
      · rw [h₁]
      · simp [h₁] at h
        by_cases h₂ : c₁ = c₂.cyclic
        · rw [h₂]
          simp [cube.corner_cyclic_inv, CornerPiece.equiv_iff]
        · simp [h₂] at h
          rw [← h]
          simp [cube.corner_cyclic_inv, CornerPiece.equiv_iff]
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.inv_apply_self]
    · refine Quotient.inductionOn c ?_
      intro
      simp_rw [Quotient.lift_mk, Perm.apply_inv_self]
  map_one' := by
    ext c
    refine Quotient.inductionOn c ?_
    exact fun _ ↦ rfl
  map_mul' cube₁ cube₂ := by
    ext c
    refine Quotient.inductionOn c ?_
    simp

theorem cornerEquiv_mk {n : {m : ℕ // m ≥ 5}} (cube : BigIllegalRubik n) (c : CornerPiece) :
  cornerEquiv n cube (⟦c⟧) = ⟦cube.cornerPieceEquiv c⟧ := rfl

theorem cornerEquiv_one (n : {m : ℕ // m ≥ 5}) : cornerEquiv n 1 = 1 :=
  map_one _

theorem cornerEquiv_of_cornerPieceEquiv_eq_one (n : {m : ℕ // m ≥ 5}) {cube : BigIllegalRubik n}
(h : cornerPieceEquiv cube = 1) : cornerEquiv n cube = 1 := by
  ext c
  refine c.inductionOn ?_
  simp [cornerEquiv_mk, h]

/-- In a Big Rubik's cube where all edges are in their correct position, the "edge value" of an edge
represents whether it's flipped or not. -/
def edgeValue {n : {m : ℕ // m ≥ 5}} (cube : BigIllegalRubik n) (e : Edge ⟨n.val, by omega⟩) :
ℤˣ :=
  e.lift (fun e ↦ if cube.edgePieceEquiv e = e then 1 else -1) (by
    intro e₁ e₂ h
    obtain rfl | rfl := (EdgePiece.equiv_iff ⟨n, by omega⟩).1 h <;> simp [edge_flip]
  )

theorem edgeValue_mk (n : {m : ℕ // m ≥ 5}) (cube : BigIllegalRubik n)
(e : EdgePiece ⟨n.val, by omega⟩) :
edgeValue cube (⟦e⟧) = if cube.edgePieceEquiv e = e then 1 else -1 := rfl

theorem edgeValue_eq_one {n : {m : ℕ // m ≥ 5}} {e : EdgePiece ⟨n.val, by omega⟩}
{cube : BigIllegalRubik n} :
edgeValue cube ⟦e⟧ = 1 ↔ cube.edgePieceEquiv e = e := by
  simp [edgeValue_mk]

theorem edgeValue_eq_neg_one' {n : {m : ℕ // m ≥ 5}} {e : EdgePiece ⟨n.val, by omega⟩}
{cube : BigIllegalRubik n} :
    edgeValue cube ⟦e⟧ = -1 ↔ cube.edgePieceEquiv e ≠ e := by
  simp [edgeValue_mk]

theorem edgeValue_eq_neg_one {n : {m : ℕ // m ≥ 5}} {cube : BigIllegalRubik n}
(he : edgeEquiv n cube = 1) {e : EdgePiece ⟨n.val, by omega⟩} :
edgeValue cube ⟦e⟧ = -1 ↔ cube.edgePieceEquiv e = e.flip := by
  rw [edgeValue_eq_neg_one']
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ e.flip_ne⟩
  have : ⟦cube.edgePieceEquiv e⟧ = (⟦e⟧ : Edge ⟨n, by omega⟩) := by
    rw [← edgeEquiv_mk, he, Perm.one_apply]
  rw [Edge.eq, EdgePiece.equiv_iff] at this
  obtain he | he := this
  · contradiction
  · rw [he]

/-- In a Rubik's cube where all corners are in their correct position, the "corner value" of a
corner represents the number of **counterclockwise** turns required to solve it. -/
def cornerValue {n : {m // m ≥ 5}} (cube : BigIllegalRubik n) (c : Corner) : ZMod 3 :=
  c.lift (fun c ↦ (cube.cornerPieceEquiv c).value Axis.x - c.value Axis.x) (by
    intro c₁ c₂ h
    obtain rfl | rfl | rfl := CornerPiece.equiv_iff.1 h <;> simp [corner_cyclic]
  )

theorem cornerValue_mk {n : {m // m ≥ 5}} (cube : BigIllegalRubik n) (c : CornerPiece) :
cornerValue cube ⟦c⟧ = (cube.cornerPieceEquiv c).value Axis.x - c.value Axis.x :=
  rfl

theorem cornerValue_eq_zero {n : {m // m ≥ 5}} {cube : BigIllegalRubik n}
(hc : cornerEquiv n cube = 1) {c : CornerPiece} :
cornerValue cube ⟦c⟧ = 0 ↔ cube.cornerPieceEquiv c = c := by
  rw [cornerValue_mk, sub_eq_zero, CornerPiece.value_eq_iff_of_equiv, eq_comm]
  rw [← Corner.eq, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_eq_one {n : {m // m ≥ 5}} {cube : BigIllegalRubik n}
(hc : cornerEquiv n cube = 1) {c : CornerPiece} :
cornerValue cube ⟦c⟧ = 1 ↔ cube.cornerPieceEquiv c = c.cyclic := by
  have : (1 + (1 + 1) : ZMod 3) = 0 := rfl
  rw [cornerValue_mk, CornerPiece.value_cyclic', CornerPiece.value_cyclic', sub_eq_iff_eq_add,
    add_comm, ← sub_eq_iff_eq_add, sub_sub, sub_sub, this, sub_zero,
    CornerPiece.value_eq_iff_of_equiv, ← CornerPiece.cyclic_inj, CornerPiece.cyclic₃]
  rw [← Corner.eq, Corner.mk_cyclic, Corner.mk_cyclic, ← cornerEquiv_mk, hc, Perm.one_apply]

theorem cornerValue_eq_two {n : {m // m ≥ 5}} {cube : BigIllegalRubik n}
(hc : cornerEquiv n cube = 1) {c : CornerPiece} :
cornerValue cube ⟦c⟧ = 2 ↔ cube.cornerPieceEquiv c = c.cyclic.cyclic := by
  have : (2 + 1 : ZMod 3) = 0 := rfl
  rw [cornerValue_mk, sub_eq_iff_eq_add, CornerPiece.value_cyclic', add_comm, sub_eq_iff_eq_add,
    add_assoc, this, add_zero, CornerPiece.value_eq_iff_of_equiv,
    ← CornerPiece.cyclic_inj, ← CornerPiece.cyclic_inj, CornerPiece.cyclic₃]
  rw [← Corner.eq, Corner.mk_cyclic, ← cornerEquiv_mk, hc, Perm.one_apply]

end BigIllegalRubik
