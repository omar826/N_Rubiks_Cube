-- import Mathlib (cannot do this due to name clashes)
import NRubiksCube.Piece

open Orientation Equiv

/-- Permutations of pieces in 2×2×2 Rubik's cube. -/
structure TwoIllegalRubik where
  /-- Returns the corner piece at a given location. -/
  cornerPieceEquiv : Perm CornerPiece
  /-- Pieces in the same corner get mapped to pieces in the same corner. -/
  corner_cyclic (c : CornerPiece) : cornerPieceEquiv c.cyclic = (cornerPieceEquiv c).cyclic

namespace TwoIllegalRubik

/-- The solved 2×2×2 Rubik's cube. -/
instance : One TwoIllegalRubik where
  one := ⟨1, by simp⟩

instance : Inhabited TwoIllegalRubik where
  default := 1

/-- The product of two 2×2×2 Rubik's cubes is the 2×2×2 Rubik's cube where the first's scramble is
performed before the second's. -/
instance : Mul TwoIllegalRubik :=
  ⟨fun cube₁ cube₂ ↦ by
    refine ⟨cube₁.cornerPieceEquiv * cube₂.cornerPieceEquiv, fun c ↦ ?_⟩
    simp [cube₁.corner_cyclic, cube₂.corner_cyclic]⟩

end TwoIllegalRubik
