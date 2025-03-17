-- import Mathlib (cannot do this due to name clashes)
import NRubiksCube.Piece

open Orientation Equiv

/-- Permutations of pieces in an big Rubik's cube (n ≥ 5). -/
structure BigIllegalRubik (n : {m : ℕ // m ≥ 5}) where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm (EdgePiece ⟨n.val, by omega⟩)
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


/-- The solved Big Rubik's cubes. -/
instance (n : {m // m ≥ 5}) : One (BigIllegalRubik n) where
  one := ⟨1, 1, 1, 1, by simp, by simp, by simp, by simp⟩

instance (n : {m // m ≥ 5}) : Inhabited (BigIllegalRubik n) where
  default := 1

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
    ⟨cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv,
    cube₁.edgePieceEquiv * cube₂.edgePieceEquiv,
    cube₁.centreSquareEdgeEquiv * cube₂.centreSquareEdgeEquiv,
    cube₁.centreSquareCornerEquiv * cube₂.centreSquareCornerEquiv,
    fun e ↦ h₁ cube₁ cube₂ e,
    fun c ↦ h₂ cube₁ cube₂ c,
    fun cse ↦ h₃ cube₁ cube₂ cse,
    fun csc ↦ h₄ cube₁ cube₂ csc⟩⟩

theorem edgePieceEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).edgePieceEquiv = cube₁.edgePieceEquiv * cube₂.edgePieceEquiv := rfl

theorem cornerPieceEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).cornerPieceEquiv = cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv := rfl

theorem centreSquareEdgeEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).centreSquareEdgeEquiv =
  cube₁.centreSquareEdgeEquiv * cube₂.centreSquareEdgeEquiv := rfl

theorem centreSquareCornerEquiv_mul {n : {m // m ≥ 5}} (cube₁ cube₂ : BigIllegalRubik n) :
  (cube₁ * cube₂).centreSquareCornerEquiv =
  cube₁.centreSquareCornerEquiv * cube₂.centreSquareCornerEquiv := rfl

theorem edge_flip_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  (e : (EdgePiece ⟨n.val, by omega⟩)) :
  cube.edgePieceEquiv⁻¹ e.flip = (cube.edgePieceEquiv⁻¹ e).flip := by
    apply Eq.symm
    rw [← cube.edgePieceEquiv.inv_apply_self (EdgePiece.flip _)]
    rw [cube.edge_flip, Perm.apply_inv_self]

theorem corner_cyclic_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  (c : CornerPiece) :
  cube.cornerPieceEquiv⁻¹ c.cyclic = (cube.cornerPieceEquiv⁻¹ c).cyclic := by
  apply Eq.symm
  rw [← cube.cornerPieceEquiv.inv_apply_self (CornerPiece.cyclic _)]
  rw [cube.corner_cyclic, Perm.apply_inv_self]

theorem centre_square_edge_square_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  (e : CentreSquareEdge ⟨n.val, by omega⟩) :
  (cube.centreSquareEdgeEquiv⁻¹ e).k = e.k := sorry -- TODO: finish this

theorem centre_square_corner_square_inv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  (c : CentreSquareCorner ⟨n.val, by omega⟩) :
  (cube.centreSquareCornerEquiv⁻¹ c).k = c.k := sorry -- TODO: finish this

theorem edgePieceEquiv_equiv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  {e₁ e₂ : EdgePiece ⟨n.val, by omega⟩} (h : e₁ ≈ e₂) :
  cube.edgePieceEquiv e₁ ≈ cube.edgePieceEquiv e₂ := by
    by_cases h₁ : e₁ = e₂
    · simp [h₁]
      apply Setoid.refl
    · rw [EdgePiece.equiv_iff] at h
      simp [h₁] at h
      rw [h]
      simp [cube.edge_flip]
      simp [EdgePiece.equiv_iff]

theorem cornerPieceEquiv_equiv {n : {m // m ≥ 5}} (cube : BigIllegalRubik n)
  {c₁ c₂ : CornerPiece} (h : c₁ ≈ c₂) :
  cube.cornerPieceEquiv c₁ ≈ cube.cornerPieceEquiv c₂ :=
    sorry -- TODO: finish this

/-- The inverse of a Big Rubik's cube is obtained by performing its moves backwards. -/
instance (n : {m // m ≥ 5}) : Inv (BigIllegalRubik n) :=
  ⟨fun cube ↦ ⟨cube.cornerPieceEquiv⁻¹, cube.edgePieceEquiv⁻¹, cube.centreSquareEdgeEquiv⁻¹,
    cube.centreSquareCornerEquiv⁻¹, fun e ↦ edge_flip_inv cube e, fun c ↦ corner_cyclic_inv cube c,
    fun cse ↦ centre_square_edge_square_inv cube cse, fun csc ↦ centre_square_corner_square_inv cube csc⟩⟩

end BigIllegalRubik
