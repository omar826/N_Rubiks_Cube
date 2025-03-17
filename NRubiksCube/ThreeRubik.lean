-- import Mathlib (cannot do this due to name clashes)
import NRubiksCube.Piece

open Orientation Equiv

/-- Permutations of pieces in 3×3×3 Rubik's cube. -/
structure ThreeIllegalRubik where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Returns the edge piece at a given location. -/
  edgePieceEquiv : Perm (EdgePiece ⟨3, by decide⟩)
  /-- Pieces in the same edge get mapped to pieces in the same edge. -/
  edge_flip (e : (EdgePiece ⟨3, by decide⟩)) : edgePieceEquiv e.flip = (edgePieceEquiv e).flip
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic

namespace ThreeIllegalRubik

/-- The solved 3×3×3 Rubik's cube. -/
instance : One ThreeIllegalRubik where
  one := ⟨1, 1, by simp, by simp⟩

instance : Inhabited ThreeIllegalRubik where
  default := 1

/-- The product of two 3×3×3 Rubik's cubes is the 3×3×3 Rubik's cube where the first's scramble is
performed before the second's. -/
instance : Mul ThreeIllegalRubik :=
  ⟨fun cube₁ cube₂ ↦ by
    refine ⟨cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv,
      cube₁.edgePieceEquiv * cube₂.edgePieceEquiv,
      fun e ↦ ?_, fun c ↦ ?_⟩
    · simp [cube₁.edge_flip, cube₂.edge_flip]
    · simp [cube₁.corner_cyclic, cube₂.corner_cyclic]⟩

end ThreeIllegalRubik
