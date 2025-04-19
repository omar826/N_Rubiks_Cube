import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import NRubiksCube.Orientation
import NRubiksCube.Piece
import NRubiksCube.Equiv
import NRubiksCube.visual
import Mathlib.Data.Array.Defs

open Orientation
open Equiv
namespace FourRubik

-- ## Index Types for Piece Slots

/-- There are 8 corner positions. -/
abbrev CornerSlot : Type := Fin 8

/-- There are 24 edge positions (12 physical edges * 2 labeled pieces 'a'/'b'). -/
abbrev EdgeSlot : Type := Fin 24

/-- There are 24 center positions. -/
abbrev CenterSlot : Type := Fin 24

-- ## Cube State Structure (S_Conf)
structure CubeState where
  corner_perm : Equiv.Perm CornerSlot -- permutation of corner pieces
  edge_perm : Equiv.Perm EdgeSlot
  center_perm : Equiv.Perm CenterSlot
  corner_ori : CornerSlot → ZMod 3 -- (ℤ₃)⁸
  edge_ori : EdgeSlot → ZMod 2


def initialState : CubeState where
  corner_perm := 1
  edge_perm   := 1
  center_perm := 1
  corner_ori  := fun _ => 0
  edge_ori    := fun _ => 0

-- ## Basic Moves
inductive BasicMove
  | R | L | U | D | F | B  -- Outer faces
  | CR | CL | CU | CD | CF | CB -- Inner slices adjacent to the corresponding outer face
  deriving Fintype, DecidableEq, Repr


--Note: a type has Fintype if it has a finite number of elements.

/-!
## Step 1: Indexing Scheme and Constants

**Convention:**

Up - White
Front - Red
Right - Blue
-/

namespace Indexing

-- ### Corner Slots (Fin 8)
-- UFL=0, URF=1, URB=2, ULB=3, DFL=4, DRF=5, DRB=6, DLB=7
def c_ufl : CornerSlot := 0
def c_urf : CornerSlot := 1
def c_urb : CornerSlot := 2
def c_ulb : CornerSlot := 3
def c_dfl : CornerSlot := 4
def c_drf : CornerSlot := 5
def c_drb : CornerSlot := 6
def c_dlb : CornerSlot := 7

-- Corner slots affected by each face move (clockwise cycle order)
def r_face_corners : List CornerSlot := [c_urf, c_drf, c_drb, c_urb] -- 1, 5, 6, 2
def l_face_corners : List CornerSlot := [c_ulb, c_dlb, c_dfl, c_ufl] -- 3, 7, 4, 0
def u_face_corners : List CornerSlot := [c_ulb, c_urb, c_urf, c_ufl] -- 3, 2, 1, 0
def d_face_corners : List CornerSlot := [c_dfl, c_drf, c_drb, c_dlb] -- 4, 5, 6, 7
def f_face_corners : List CornerSlot := [c_ufl, c_urf, c_drf, c_dfl] -- 0, 1, 5, 4
def b_face_corners : List CornerSlot := [c_urb, c_ulb, c_dlb, c_drb] -- 2, 3, 7, 6


-- ### Orientation Delta Constants

/-
## Convention for Corners
corners with white side - white side gets 0 then 1,2 clockwise
corners with yellow side - yellow side gets 0 then 1,2 clockwise

corner orientation: number on up/down face
-/

-- Corner twists for R move

def r_move_corner_ori_delta (slot_before_move : CornerSlot) : ZMod 3 :=
  if slot_before_move = c_urf then 2 -- 0 to 2 etc
  else if slot_before_move = c_drf then 1
  else if slot_before_move = c_drb then 2
  else if slot_before_move = c_urb then 1
  else 0

-- Similarly define deltas for L, U, D, F, B moves...


-- Helper to get sticker index for a corner based on the face being viewed

def getCanonicalCornerColors (slot : CornerSlot) : Orientation × Orientation × Orientation :=
  match slot.val with
  | 0 => (U, F, L) -- UFL
  | 1 => (U, R, F) -- URF
  | 2 => (U, B, R) -- URB
  | 3 => (U, L, B) -- ULB
  | 4 => (D, L, F) -- DFL
  | 5 => (D, F, R) -- DRF
  | 6 => (D, R, B) -- DRB
  | 7 => (D, B, L) -- DLB
  | _ => (U, F, L) -- Should be unreachable

def getCornerStickerIndex (slot : CornerSlot) (face : Orientation) : Fin 3 :=
  let (c0, c1, _) := getCanonicalCornerColors slot
  if face = c0 then 0
  else if face = c1 then 1
  else 2 -- Assumes face is one of c0, c1, c2

-- Applies corner orientation value to determine visible sticker color.

/-
canonical - the piece
ori_val - orientation of the piece
sticker_idx - which sticker we want to know the color of
-/

def applyCornerOrientation (canonical : Orientation × Orientation × Orientation)
    (ori_val : ZMod 3) (sticker_idx : Fin 3) : Orientation :=
  let (c0, c1, c2) := canonical
  match ori_val.val with
  | 0 => -- No twist
    match sticker_idx.val with | 0 => c0 | 1 => c1 | 2 => c2 | _ => c0
  | 1 => -- One CW twist (orig 1->pos 0, orig 2->pos 1, orig 0->pos 2)
    match sticker_idx.val with | 0 => c1 | 1 => c2 | 2 => c0 | _ => c1
  | 2 => -- Two CW twists (orig 2->pos 0, orig 0->pos 1, orig 1->pos 2)
    match sticker_idx.val with | 0 => c2 | 1 => c0 | 2 => c1 | _ => c2
  | _ => c0 -- Unreachable for ZMod 3


-- ### Edge Slots (Fin 24)
-- Using 2*i for type A, 2*i+1 for type B, based on 12 physical locations (0-11)
-- UF(0), UR(1), UB(2), UL(3) - Top layer F->R->B->L
-- FL(4), FR(5), BR(6), BL(7) - Middle layer slice F->R->B->L
-- DF(8), DR(9), DB(10), DL(11) - Bottom layer F->R->B->L

-- Example: UR edge, type A -> Slot index 2*1 + 0 = 2
-- Example: UR edge, type B -> Slot index 2*1 + 1 = 3
def edgeSlot (loc : Fin 12) (type : Orientation.EdgeType) : EdgeSlot :=
  ⟨2 * loc.val + if type = Orientation.EdgeType.A then 0 else 1,
   by -- Proof that the value is < 24
      split_ifs with h_type -- Creates two goals based on if
      · -- Goal 1: Assumes type = EdgeType.A, prove 2 * loc.val + 0 < 24
        linarith [loc.isLt]
      · -- Goal 2: Assumes type ≠ EdgeType.A, prove 2 * loc.val + 1 < 24
        linarith [loc.isLt]
   ⟩
-- Define constants for specific locations (A type)
def e_uf_a : EdgeSlot := edgeSlot 0 EdgeType.A  -- 0
def e_ur_a : EdgeSlot := edgeSlot 1 EdgeType.A  -- 2
def e_ub_a : EdgeSlot := edgeSlot 2 EdgeType.A  -- 4
def e_ul_a : EdgeSlot := edgeSlot 3 EdgeType.A  -- 6
def e_fl_a : EdgeSlot := edgeSlot 4 EdgeType.A  -- 8
def e_fr_a : EdgeSlot := edgeSlot 5 EdgeType.A  -- 10
def e_br_a : EdgeSlot := edgeSlot 6 EdgeType.A  -- 12
def e_bl_a : EdgeSlot := edgeSlot 7 EdgeType.A  -- 14
def e_df_a : EdgeSlot := edgeSlot 8 EdgeType.A  -- 16
def e_dr_a : EdgeSlot := edgeSlot 9 EdgeType.A  -- 18
def e_db_a : EdgeSlot := edgeSlot 10 EdgeType.A -- 20
def e_dl_a : EdgeSlot := edgeSlot 11 EdgeType.A -- 22

-- Define constants for specific locations (B type)
def e_uf_b : EdgeSlot := edgeSlot 0 EdgeType.B  -- 1
def e_ur_b : EdgeSlot := edgeSlot 1 EdgeType.B  -- 3
def e_ub_b : EdgeSlot := edgeSlot 2 EdgeType.B  -- 5
def e_ul_b : EdgeSlot := edgeSlot 3 EdgeType.B  -- 7
def e_fl_b : EdgeSlot := edgeSlot 4 EdgeType.B  -- 9
def e_fr_b : EdgeSlot := edgeSlot 5 EdgeType.B  -- 11
def e_br_b : EdgeSlot := edgeSlot 6 EdgeType.B  -- 13
def e_bl_b : EdgeSlot := edgeSlot 7 EdgeType.B  -- 15
def e_df_b : EdgeSlot := edgeSlot 8 EdgeType.B  -- 16
def e_dr_b : EdgeSlot := edgeSlot 9 EdgeType.B  -- 19
def e_db_b : EdgeSlot := edgeSlot 10 EdgeType.B -- 21
def e_dl_b : EdgeSlot := edgeSlot 11 EdgeType.B -- 23

-- Edge slots affected by R face move (UR, FR, DR, BR)
-- Cycle 1 (Type A): 2 -> 10 -> 18 -> 12 -> 2
-- Cycle 2 (Type B): 3 -> 11 -> 19 -> 13 -> 3
def r_face_edges_a : List EdgeSlot := [e_ur_a, e_fr_a, e_dr_a, e_br_a]
def r_face_edges_b : List EdgeSlot := [e_ur_b, e_fr_b, e_dr_b, e_br_b]
-- define lists for L, U, D, F, B faces... (toDo)

-- ### Center Slots (Fin 24)
-- Group by face (U=0-3, L=4-7, F=8-11, R=12-15, B=16-19, D=20-23)
-- Within face, index 0=UL, 1=UR, 2=DR, 3=DL relative to center block
def centerSlot (face : Orientation) (idx : Fin 4) : CenterSlot :=
  let face_base : Fin 6 := match face.axis with | .x => if face.sign then 3 else 1 | .y => if face.sign then 0 else 5 | .z => if face.sign then 2 else 4 -- R L U D F B -> 3 1 0 5 2 4
  ⟨4 * face_base.val + idx.val, by omega⟩ -- Proof value is < 24

-- Define constants for R face centers (Indices 12, 13, 14, 15)
-- Assume clockwise cycle: 12(UL) -> 13(UR) -> 15(DR) -> 14(DL) -> 12
def z_r_ul : CenterSlot := centerSlot Orientation.R 0 -- 12
def z_r_ur : CenterSlot := centerSlot Orientation.R 1 -- 13
def z_r_dr : CenterSlot := centerSlot Orientation.R 2 -- 14
def z_r_dl : CenterSlot := centerSlot Orientation.R 3 -- 15
def r_face_centers : List CenterSlot := [z_r_ul, z_r_ur, z_r_dr, z_r_dl] -- 12, 13, 14, 15
def z_r_1 := z_r_ul
def z_r_2 := z_r_ur
def z_r_3 := z_r_dr
def z_r_4 := z_r_dl -- Use 1/2/3/4 locally


def cr_slice_centers : List CenterSlot := [
  centerSlot Orientation.F 1, centerSlot Orientation.F 3, -- F_UR, F_DR
  centerSlot Orientation.U 1, centerSlot Orientation.U 3, -- U_UR, U_DR
  centerSlot Orientation.B 1, centerSlot Orientation.B 3, -- B_UR, B_DR (from back view?) -> B_UL, B_DL (indices 17, 19)
  centerSlot Orientation.D 1, centerSlot Orientation.D 3  -- D_UR, D_DR
]
-- Similarly define lists for other slices...





/-! ### Indices for CR Move ### -/

-- CR affects Corners: None
-- CR affects Edges: UF(0,1), UB(4,5), DB(20,21), DF(16,17) - Perpendicular slice
-- Cycle 1 (Type A): 0 -> 4 -> 20 -> 16 -> 0
-- Cycle 2 (Type B): 1 -> 5 -> 21 -> 17 -> 1
def cr_slice_edges_a : List EdgeSlot := [e_uf_a, e_ub_a, e_db_a, e_df_a] -- 0, 4, 20, 16
def cr_slice_edges_b : List EdgeSlot := [e_uf_b, e_ub_b, e_db_b, e_df_b] -- 1, 5, 21, 17


-- U Face: Affects UR (1) and DR (3) -> Indices 1, 3
-- F Face: Affects UR (1) and DR (3) -> Indices 9, 11
-- D Face: Affects UR (1) and DR (3) -> Indices 21, 23
-- B Face: Affects UL (0) and DL (2) -> Indices 17, 19 (Indices relative to Back face perspective)
-- Cycle 1: U_UR(1) -> F_UR(9) -> D_UR(21) -> B_UL(17) -> U_UR(1)
-- Cycle 2: U_DR(3) -> F_DR(11) -> D_DR(23) -> B_DL(19) -> U_DR(3)

def z_u_ur : CenterSlot := centerSlot Orientation.U 1 -- 1
def z_u_dr : CenterSlot := centerSlot Orientation.U 3 -- 3
def z_f_ur : CenterSlot := centerSlot Orientation.F 1 -- 9
def z_f_dr : CenterSlot := centerSlot Orientation.F 3 -- 11
def z_d_ur : CenterSlot := centerSlot Orientation.D 1 -- 21
def z_d_dr : CenterSlot := centerSlot Orientation.D 3 -- 23
def z_b_ul : CenterSlot := centerSlot Orientation.B 0 -- 16 (Check B face indexing: 0=UL?)
def z_b_dl : CenterSlot := centerSlot Orientation.B 2 -- 18 (Check B face indexing: 2=DL?)


def cr_slice_centers1 : List CenterSlot := [z_u_ur, z_f_ur, z_d_ur, z_b_ul] -- 1, 9, 21, 16
def cr_slice_centers2 : List CenterSlot := [z_u_dr, z_f_dr, z_d_dr, z_b_dl] -- 3, 11, 23, 18

-- Define Center indices for L, F, B faces too
def z_l_ul : CenterSlot := centerSlot Orientation.L 0 -- 4
def z_l_ur : CenterSlot := centerSlot Orientation.L 1 -- 5
def z_l_dr : CenterSlot := centerSlot Orientation.L 2 -- 6
def z_l_dl : CenterSlot := centerSlot Orientation.L 3 -- 7
def z_f_ul : CenterSlot := centerSlot Orientation.F 0 -- 8
def z_f_dl : CenterSlot := centerSlot Orientation.F 3 -- 11
def z_b_ur : CenterSlot := centerSlot Orientation.B 1 -- 17
def z_b_dr : CenterSlot := centerSlot Orientation.B 2 -- 18
def z_d_ul : CenterSlot := centerSlot Orientation.D 0 -- 20
def z_d_dl : CenterSlot := centerSlot Orientation.D 3 -- 23

/-! ### Orientation Deltas ### -/
-- (Keep r_move_corner_ori_delta from previous step)

-- CR move flips the edges it cycles
def cr_move_edge_ori_delta (slot_before_move : EdgeSlot) : ZMod 2 :=
  -- Check if the slot is one of the 8 involved in the CR slice turn
  if slot_before_move ∈ cr_slice_edges_a || slot_before_move ∈ cr_slice_edges_b then 1 else 0


----------------------------------------STOP----------------------------------------



















/-! ### Indices for U Move ### -/

-- Corners: UFL(0), URF(1), URB(2), ULB(3)
-- Cycle: 0 → 1 → 2 → 3 → 0

-- Edges: UF(0,1), UR(2,3), UB(4,5), UL(6,7)
-- Cycle A: 0 → 2 → 4 → 6 → 0
-- Cycle B: 1 → 3 → 5 → 7 → 1
def u_face_edges_a : List EdgeSlot := [e_uf_a, e_ur_a, e_ub_a, e_ul_a] -- 0, 2, 4, 6
def u_face_edges_b : List EdgeSlot := [e_uf_b, e_ur_b, e_ub_b, e_ul_b] -- 1, 3, 5, 7

-- Centers: U face centers (Indices 0, 1, 2, 3)
-- Assume 0=UL, 1=UR, 2=DR, 3=DL relative to center block
-- Clockwise Cycle: 0 → 1 → 2 → 3 → 0
def z_u_ul : CenterSlot := centerSlot Orientation.U 0 -- 0
def z_u_dl : CenterSlot := centerSlot Orientation.U 3 -- 3
def u_face_centers : List CenterSlot := [z_u_ul, z_u_ur, z_u_dr, z_u_dl] -- 0, 1, 2, 3

/-! ### Orientation Deltas ### -/
-- (Keep r_move_corner_ori_delta and cr_move_edge_ori_delta)

-- U move does not twist corners
def u_move_corner_ori_delta (_slot_before_move : CornerSlot) : ZMod 3 := 0

-- U move does not flip edges
def u_move_edge_ori_delta (_slot_before_move : EdgeSlot) : ZMod 2 := 0





/-- Returns the two canonical orientations (colors) of an edge piece
    given its solved slot index. Note: Slots 2*i and 2*i+1 have the same colors.
    Order: Primary (U/D/F/B), Secondary (L/R) face preference. -/
def getCanonicalEdgeColors (slot : EdgeSlot) : Orientation × Orientation :=
  let physicalLocIdx := slot.val / 2 -- Integer division 0..11
  match physicalLocIdx with
  | 0 => (U, F) -- UF
  | 1 => (U, R) -- UR
  | 2 => (U, B) -- UB
  | 3 => (U, L) -- UL
  | 4 => (F, L) -- FL
  | 5 => (F, R) -- FR
  | 6 => (B, R) -- BR
  | 7 => (B, L) -- BL
  | 8 => (D, F) -- DF
  | 9 => (D, R) -- DR
  | 10 => (D, B) -- DB
  | 11 => (D, L) -- DL
  | _ => (U, F) -- Should be unreachable

/-- Helper to get sticker index for an edge based on the face being viewed.
    Convention: 0 is U/D/F/B face sticker, 1 is L/R face sticker. -/
def getEdgeStickerIndex (edgeSlot : EdgeSlot) (face : Orientation) : Fin 2 :=
  -- Get the two canonical faces for this edge's location
  let (face1, _) := getCanonicalEdgeColors edgeSlot
  -- face1 is always U/D/F/B, face2 is always L/R by construction
  if face = face1 then
     0 -- We are looking at the sticker belonging to the U/D/F/B face
  else -- Otherwise, we must be looking at the sticker belonging to the L/R face
  -- (We assume 'face' is one of the two valid faces for this edge location)
     1

/-- Returns the canonical orientation (color) of a center piece
    given its solved slot index. -/
def getCanonicalCenterColor (slot : CenterSlot) : Orientation :=
  -- We defined centerSlot based on Face and index 0..3 within face
  -- Determine face based on slot index range
  if slot.val < 4 then U -- Slots 0-3 are U face
  else if slot.val < 8 then L -- Slots 4-7 are L face
  else if slot.val < 12 then F -- Slots 8-11 are F face
  else if slot.val < 16 then R -- Slots 12-15 are R face
  else if slot.val < 20 then B -- Slots 16-19 are B face
  else D -- Slots 20-23 are D face



/-- Applies edge orientation value to determine visible sticker color.
    Args:
      canonical: The pair of 2 orientations in solved state (Primary, Secondary order).
      ori_val: The current orientation value (0=unflipped, 1=flipped).
      sticker_idx: Which sticker face we want to know the color of (0 or 1).
    Returns: The Orientation (color) visible at that sticker index. -/
def applyEdgeOrientation (canonical : Orientation × Orientation)
    (ori_val : ZMod 2) (sticker_idx : Fin 2) : Orientation :=
  let (c1, c2) := canonical -- Unpack (c1=Primary U/D/F/B, c2=Secondary L/R)
  match ori_val.val with -- Match on the Nat value 0 or 1
  | 0 => -- Not flipped
    match sticker_idx.val with
    | 0 => c1
    | 1 => c2
    | _ => c1 -- Unreachable for Fin 2
  | 1 => -- Flipped (0->1, 1->0)
    match sticker_idx.val with
    | 0 => c2 -- Sticker 0 now shows color originally at index 1
    | 1 => c1 -- Sticker 1 now shows color originally at index 0
    | _ => c2 -- Unreachable
  | _ => c1 -- Unreachable for ZMod 2

end Indexing -- End Indexing namespace

namespace MoveImpl

open Indexing -- Make constants visible
open Equiv -- Make Perm and swap visible

--## Permutations for R Move
-- Let's assume B face indices are 0=UL, 1=UR, 2=DR, 3=DL
-- Then B_UL is 16, B_DL is 18.
-- Cycle 1: 1 -> 9 -> 21 -> 16 -> 1
-- Cycle 2: 3 -> 11 -> 23 -> 18 -> 3
def r_move_corner_perm : Perm CornerSlot :=
  swap c_urf c_drf * swap c_urf c_drb * swap c_urf c_urb
def r_move_edge_perm : Perm EdgeSlot :=
  (swap e_ur_b e_fr_b * swap e_ur_b e_dr_b * swap e_ur_b e_br_b)
  *(swap e_ur_a e_fr_a * swap e_ur_a e_dr_a * swap e_ur_a e_br_a)


/-- The permutation of center slots caused by a clockwise R face turn.
    Cycles the 4 center slots on the R face.
    Cycle: R_UL(12) → R_UR(13) → R_DR(14) → R_DL(15) → R_UL(12) -/
def r_move_center_perm : Perm CenterSlot :=
  swap z_r_1 z_r_2 * swap z_r_1 z_r_3 * swap z_r_1 z_r_4

-- ## Permutations for U Move

-- Cycle: 0 → 1 → 2 → 3 → 0
def u_move_corner_perm : Perm CornerSlot :=
  swap c_ufl c_urf * swap c_ufl c_urb * swap c_ufl c_ulb

-- Cycle A: 0 → 2 → 4 → 6 → 0
-- Cycle B: 1 → 3 → 5 → 7 → 1
def u_move_edge_perm : Perm EdgeSlot :=
  ( swap e_uf_b e_ur_b * swap e_uf_b e_ub_b * swap e_uf_b e_ul_b)*
  ( swap e_uf_a e_ur_a* swap e_uf_a e_ub_a * swap e_uf_a e_ul_a)


-- Cycle: 0 → 1 → 2 → 3 → 0
def u_move_center_perm : Perm CenterSlot :=
  swap z_u_ul z_u_ur * swap z_u_ul z_u_dr * swap z_u_ul z_u_dl

open Indexing -- Make constants visible

-- ## Permutations for CR Move
def cr_move_corner_perm : Equiv.Perm CornerSlot := 1 -- CR doesn't affect corners

-- Cycle 1: 0 -> 4 -> 20 -> 16 -> 0
-- Cycle 2: 1 -> 5 -> 21 -> 17 -> 1
def cr_move_edge_perm : Perm EdgeSlot :=
  swap e_uf_a e_ub_b * swap e_uf_a e_db_a * swap e_uf_a e_df_b -- Implements 0 → 5 → 20 → 17 → 0

/-- The permutation of center slots caused by a clockwise CR slice turn.
    Cycles two groups of 4 centers on U, F, D, B faces.
    Cycle 1: U_UR(1) → F_UR(9) → D_UR(21) → B_UL(16) → U_UR(1)
    Cycle 2: U_DR(3) → F_DR(11) → D_DR(23) → B_DL(19) → U_DR(3) -/
def cr_move_center_perm : Perm CenterSlot :=
  ( swap z_u_dr z_f_dr* swap z_u_dr z_d_dr * swap z_u_dr z_b_dl) *
  ( swap z_u_ur z_f_ur* swap z_u_ur z_d_ur * swap z_u_ur z_b_ul)


def rotY_corner_perm : Perm CornerSlot :=
  (swap c_ufl c_ulb * swap c_ufl c_urb * swap c_ufl c_urf) * -- Top layer 0->1->2->3->0
  (swap c_dfl c_dlb * swap c_dfl c_drb * swap c_dfl c_drf)   -- Bottom layer 4->5->6->7->4

def rotY_edge_perm : Perm EdgeSlot :=
  (swap e_uf_a e_ul_a * swap e_uf_a e_ub_a * swap e_uf_a e_ur_a) * -- Top A
  (swap e_uf_b e_ul_b * swap e_uf_b e_ub_b * swap e_uf_b e_ur_b) * -- Top B
  (swap e_fl_a e_bl_a * swap e_fl_a e_br_a * swap e_fl_a e_fr_a) * -- Mid A
  (swap e_fl_b e_bl_b * swap e_fl_b e_br_b * swap e_fl_b e_fr_b) * -- Mid B
  (swap e_df_a e_dl_a * swap e_df_a e_db_a * swap e_df_a e_dr_a) * -- Bot A
  (swap e_df_b e_dl_b * swap e_df_b e_db_b * swap e_df_b e_dr_b)   -- Bot B

def rotY_center_perm : Perm CenterSlot :=
  (swap z_u_ul z_u_dl * swap z_u_ul z_u_dr * swap z_u_ul z_u_ur) * -- U face 0->1->2->3->0
  (swap z_d_ul z_d_dl * swap z_d_ul z_d_dr * swap z_d_ul z_d_ur) * -- D face 20->21->22->23->20
  (swap z_l_ul z_b_ul * swap z_l_ul z_r_ul * swap z_l_ul z_f_ul) * -- UL pos: 4->8->12->16->4
  (swap z_l_ur z_b_ur * swap z_l_ur z_r_ur * swap z_l_ur z_f_ur) * -- UR pos: 5->9->13->17->5
  (swap z_l_dr z_b_dr * swap z_l_dr z_r_dr * swap z_l_dr z_f_dr) * -- DR pos: 6->10->14->18->6
  (swap z_l_dl z_b_dl * swap z_l_dl z_r_dl * swap z_l_dl z_f_dl)   -- DL pos: 7->11->15->19->7


-- ## Apply Move Implementation (Cases R, CR)

def apply_move (m : BasicMove) (s : CubeState) : CubeState :=
  match m with
  | BasicMove.R => -- (Keep implementation from previous step)
    { corner_perm := r_move_corner_perm * s.corner_perm,
      edge_perm   := r_move_edge_perm * s.edge_perm,
      center_perm := r_move_center_perm * s.center_perm,
      corner_ori  := fun i => s.corner_ori (r_move_corner_perm⁻¹ i) + r_move_corner_ori_delta (r_move_corner_perm⁻¹ i),
      edge_ori    := fun i => s.edge_ori (r_move_edge_perm⁻¹ i)
    }
  | BasicMove.CR =>
    { corner_perm := cr_move_corner_perm * s.corner_perm, -- = s.corner_perm * 1
      edge_perm   := cr_move_edge_perm * s.edge_perm,
      center_perm := cr_move_center_perm * s.center_perm,
      -- Corners not affected, ori function remains the same relative to permuted slots
      corner_ori  := fun i => s.corner_ori (cr_move_corner_perm⁻¹ i), -- = s.corner_ori i
      -- Edges are permuted AND flipped
      edge_ori    := fun i => s.edge_ori (cr_move_edge_perm⁻¹ i) + cr_move_edge_ori_delta (cr_move_edge_perm⁻¹ i)
    }
  | BasicMove.L => s
  | BasicMove.U =>
    { corner_perm := u_move_corner_perm * s.corner_perm,
      edge_perm   := u_move_edge_perm * s.edge_perm,
      center_perm := u_move_center_perm * s.center_perm,
      -- U move does not twist corners, delta is 0
      corner_ori  := fun i => s.corner_ori (u_move_corner_perm⁻¹ i), -- + u_move_corner_ori_delta (u_move_corner_perm⁻¹ i) = + 0
      -- U move does not flip edges, delta is 0
      edge_ori    := fun i => s.edge_ori (u_move_edge_perm⁻¹ i)    -- + u_move_edge_ori_delta (u_move_edge_perm⁻¹ i) = + 0
    }
  | BasicMove.D => s
  | BasicMove.F => s
  | BasicMove.B => s
  | BasicMove.CL => s
  | BasicMove.CU => s
  | BasicMove.CD => s
  | BasicMove.CF => s
  | BasicMove.CB => s

end MoveImpl -- End MoveImpl namespace
open MoveImpl -- Need access to the rotY permutations

/-- Rotates the entire cube state 90 degrees clockwise around the Y (Up/Down) axis.
    This changes the frame of reference: F becomes R, R becomes B, etc.
    Permutations are conjugated, and orientation functions are composed with the
    inverse permutation (as Y-rotation doesn't intrinsically change twist/flip). -/
def rotateCubeY (s : CubeState) : CubeState where
  corner_perm := rotY_corner_perm * s.corner_perm * rotY_corner_perm⁻¹
  edge_perm   := rotY_edge_perm * s.edge_perm * rotY_edge_perm⁻¹
  center_perm := rotY_center_perm * s.center_perm * rotY_center_perm⁻¹
  -- Define the new function explicitly: apply inverse perm, then old ori function
  corner_ori  := fun i => s.corner_ori (rotY_corner_perm⁻¹ i)
  edge_ori    := fun i => s.edge_ori (rotY_edge_perm⁻¹ i)


namespace Visual


-- Represents which sticker of a piece we're looking at
-- Corner: 0=Up/Down face sticker, 1=Side1, 2=Side2

-- Union type for different piece slots + sticker index
inductive PieceStickerID where
  /-- A corner sticker: identifies the corner slot and which of its 3 faces
      this sticker is (0:U/D, 1:F/B, 2:L/R, based on canonical orientation). -/
  | corner (slot : CornerSlot) (sticker_idx : Fin 3) : PieceStickerID
  /-- An edge sticker: identifies the edge slot (incl. A/B type) and which
      of its 2 faces this sticker is (0:U/D/F/B, 1:L/R, based on canonical orientation). -/
  | edge (slot : EdgeSlot) (sticker_idx : Fin 2) : PieceStickerID
  /-- A center sticker: identifies the center slot. -/
  | center (slot : CenterSlot) : PieceStickerID
  deriving Repr, DecidableEq -- Add needed instances


instance : Inhabited PieceStickerID where
    default :=  PieceStickerID.center default-- Default to UFL corner sticker
def n_four : Nat := 4
structure StickerLocation (n: Nat) where
  face : Orientation
  row  : Fin n
  col  : Fin n
  deriving DecidableEq, Repr, Fintype

abbrev StickerLoc4 : Type := StickerLocation n_four

open Indexing

/-- Given a sticker location (face, row, col) on a solved 4x4x4 cube,
    determines which piece slot occupies that location and which specific
    sticker of that piece it is. -/
def getSolvedPieceInfo (loc : StickerLocation n_four) : PieceStickerID :=
  match loc.face with
  -- U Face (White): Row 0 = Back, Col 0 = Left
  | (true, Axis.y) => match (loc.row.val, loc.col.val) with
      | (3, 0) => .corner c_ufl (getCornerStickerIndex c_ufl U) -- UFL, U sticker = idx 0
      | (3, 3) => .corner c_urf (getCornerStickerIndex c_urf U) -- URF, U sticker = idx 0
      | (0, 3) => .corner c_urb (getCornerStickerIndex c_urb U) -- URB, U sticker = idx 0
      | (0, 0) => .corner c_ulb (getCornerStickerIndex c_ulb U) -- ULB, U sticker = idx 0
      | (3, 1) => .edge e_uf_a (getEdgeStickerIndex e_uf_a U) -- UF, A(col 1), U sticker = idx 0
      | (3, 2) => .edge e_uf_b (getEdgeStickerIndex e_uf_b U) -- UF, B(col 2), U sticker = idx 0
      | (1, 0) => .edge e_ul_a (getEdgeStickerIndex e_ul_a U) -- UL, A(row 2?), U sticker = idx 0 -- CHECKED A/B
      | (2, 0) => .edge e_ul_b (getEdgeStickerIndex e_ul_b U) -- UL, B(row 1?), U sticker = idx 0 -- CHECKED A/B
      | (0, 1) => .edge e_ub_a (getEdgeStickerIndex e_ub_a U) -- UB, A(col 1), U sticker = idx 0
      | (0, 2) => .edge e_ub_b (getEdgeStickerIndex e_ub_b U) -- UB, B(col 2), U sticker = idx 0
      | (1, 3) => .edge e_ur_a (getEdgeStickerIndex e_ur_a U) -- UR, A(row 2?), U sticker = idx 0 -- CHECKED A/B
      | (2, 3) => .edge e_ur_b (getEdgeStickerIndex e_ur_b U) -- UR, B(row 1?), U sticker = idx 0 -- CHECKED A/B
      | (1, 1) => .center z_u_ul -- Center UL (row 1, col 1)
      | (1, 2) => .center z_u_ur -- Center UR (row 1, col 2)
      | (2, 2) => .center z_u_dr -- Center DR (row 2, col 2)
      | (2, 1) => .center z_u_dl -- Center DL (row 2, col 1)
      | _      => panic! "Impossible U coordinate"
  -- F Face (Green): Row 0 = Top, Col 0 = Left
  | (true, Axis.z) => match (loc.row.val, loc.col.val) with
      | (0, 0) => .corner c_ufl (getCornerStickerIndex c_ufl F) -- UFL, F sticker = idx 1
      | (0, 3) => .corner c_urf (getCornerStickerIndex c_urf F) -- URF, F sticker = idx 1
      | (3, 0) => .corner c_dfl (getCornerStickerIndex c_dfl F) -- DFL, F sticker = idx 1
      | (3, 3) => .corner c_drf (getCornerStickerIndex c_drf F) -- DRF, F sticker = idx 1
      | (0, 1) => .edge e_uf_a (getEdgeStickerIndex e_uf_a F) -- UF, A(row 1?), F sticker = idx 0 -- CHECKED A/B
      | (0, 2) => .edge e_uf_b (getEdgeStickerIndex e_uf_b F) -- UF, B(row 2?), F sticker = idx 0 -- CHECKED A/B
      | (1, 0) => .edge e_fl_a (getEdgeStickerIndex e_fl_a F) -- FL, A(col 1?), F sticker = idx 0
      | (2, 0) => .edge e_fl_b (getEdgeStickerIndex e_fl_b F) -- FL, B(col 2?), F sticker = idx 0
      | (1, 3) => .edge e_fr_a (getEdgeStickerIndex e_fr_a F) -- FR, A(col 1?), F sticker = idx 0
      | (2, 3) => .edge e_fr_b (getEdgeStickerIndex e_fr_b F) -- FR, B(col 2?), F sticker = idx 0
      | (3, 1) => .edge e_df_a (getEdgeStickerIndex e_df_a F) -- DF, A(row 1?), F sticker = idx 0 -- CHECKED A/B
      | (3, 2) => .edge e_df_b (getEdgeStickerIndex e_df_b F) -- DF, B(row 2?), F sticker = idx 0 -- CHECKED A/B
      | (1, 1) => .center z_f_ul -- Center UL (row 1, col 1)
      | (1, 2) => .center z_f_ur -- Center UR (row 1, col 2)
      | (2, 2) => .center z_f_dr -- Center DR (row 2, col 2)
      | (2, 1) => .center z_f_dl -- Center DL (row 2, col 1)
      | _      => panic! "Impossible F coordinate"
  -- R Face (Red): Row 0 = Top, Col 0 = Back
  | (true, Axis.x) => match (loc.row.val, loc.col.val) with
      | (0, 3) => .corner c_urf (getCornerStickerIndex c_urf R) -- URF, R sticker = idx 2
      | (3, 3) => .corner c_drf (getCornerStickerIndex c_drf R) -- DRF, R sticker = idx 2
      | (3, 0) => .corner c_drb (getCornerStickerIndex c_drb R) -- DRB, R sticker = idx 2
      | (0, 0) => .corner c_urb (getCornerStickerIndex c_urb R) -- URB, R sticker = idx 2
      | (0, 1) => .edge e_ur_a (getEdgeStickerIndex e_ur_a R) -- UR, A(row 1?), R sticker = idx 1 -- CHECKED A/B
      | (0, 2) => .edge e_ur_b (getEdgeStickerIndex e_ur_b R) -- UR, B(row 2?), R sticker = idx 1 -- CHECKED A/B
      | (1, 3) => .edge e_fr_a (getEdgeStickerIndex e_fr_a R) -- FR, A(col 1?), R sticker = idx 1
      | (2, 3) => .edge e_fr_b (getEdgeStickerIndex e_fr_b R) -- FR, B(col 2?), R sticker = idx 1
      | (3, 1) => .edge e_dr_a (getEdgeStickerIndex e_dr_a R) -- DR, A(row 1?), R sticker = idx 1 -- CHECKED A/B
      | (3, 2) => .edge e_dr_b (getEdgeStickerIndex e_dr_b R) -- DR, B(row 2?), R sticker = idx 1 -- CHECKED A/B
      | (1, 0) => .edge e_br_a (getEdgeStickerIndex e_br_a R) -- BR, A(col 1?), R sticker = idx 1
      | (2, 0) => .edge e_br_b (getEdgeStickerIndex e_br_b R) -- BR, B(col 2?), R sticker = idx 1
      | (1, 1) => .center z_r_ul -- Center UL (row 1, col 1)
      | (1, 2) => .center z_r_ur -- Center UR (row 1, col 2)
      | (2, 2) => .center z_r_dr -- Center DR (row 2, col 2)
      | (2, 1) => .center z_r_dl -- Center DL (row 2, col 1)
      | _      => panic! "Impossible R coordinate"
  -- B Face (Blue): Row 0 = Top, Col 0 = Left
  | (false, Axis.z) => match (loc.row.val, loc.col.val) with
      | (0, 3) => .corner c_urb (getCornerStickerIndex c_urb B) -- URB, B sticker = idx 1
      | (0, 0) => .corner c_ulb (getCornerStickerIndex c_ulb B) -- ULB, B sticker = idx 1
      | (3, 0) => .corner c_dlb (getCornerStickerIndex c_dlb B) -- DLB, B sticker = idx 1
      | (3, 3) => .corner c_drb (getCornerStickerIndex c_drb B) -- DRB, B sticker = idx 1
      | (0, 1) => .edge e_ub_a (getEdgeStickerIndex e_ub_a B) -- UB, A(row 1?), B sticker = idx 0 -- CHECKED A/B
      | (0, 2) => .edge e_ub_b (getEdgeStickerIndex e_ub_b B) -- UB, B(row 2?), B sticker = idx 0 -- CHECKED A/B
      | (1, 0) => .edge e_bl_a (getEdgeStickerIndex e_bl_a B) -- BL, A(col 1?), B sticker = idx 0
      | (2, 0) => .edge e_bl_b (getEdgeStickerIndex e_bl_b B) -- BL, B(col 2?), B sticker = idx 0
      | (1, 3) => .edge e_br_a (getEdgeStickerIndex e_br_a B) -- BR, A(col 1?), B sticker = idx 0
      | (2, 3) => .edge e_br_b (getEdgeStickerIndex e_br_b B) -- BR, B(col 2?), B sticker = idx 0
      | (3, 1) => .edge e_db_a (getEdgeStickerIndex e_db_a B) -- DB, A(row 1?), B sticker = idx 0 -- CHECKED A/B
      | (3, 2) => .edge e_db_b (getEdgeStickerIndex e_db_b B) -- DB, B(row 2?), B sticker = idx 0 -- CHECKED A/B
      | (1, 1) => .center z_b_ul -- Center UL (row 1, col 1)
      | (1, 2) => .center z_b_ur -- Center UR (row 1, col 2)
      | (2, 2) => .center z_b_dr -- Center DR (row 2, col 2)
      | (2, 1) => .center z_b_dl -- Center DL (row 2, col 1)
      | _      => panic! "Impossible B coordinate"
  -- L Face (Orange): Row 0 = Top, Col 0 = Back
  | (false, Axis.x) => match (loc.row.val, loc.col.val) with
      | (0, 0) => .corner c_ulb (getCornerStickerIndex c_ulb L) -- ULB, L sticker = idx 2
      | (3, 0) => .corner c_dlb (getCornerStickerIndex c_dlb L) -- DLB, L sticker = idx 2
      | (3, 3) => .corner c_dfl (getCornerStickerIndex c_dfl L) -- DFL, L sticker = idx 2
      | (0, 3) => .corner c_ufl (getCornerStickerIndex c_ufl L) -- UFL, L sticker = idx 2
      | (0, 1) => .edge e_ul_a (getEdgeStickerIndex e_ul_a L) -- UL, A(row 1?), L sticker = idx 1 -- CHECKED A/B
      | (0, 2) => .edge e_ul_b (getEdgeStickerIndex e_ul_b L) -- UL, B(row 2?), L sticker = idx 1 -- CHECKED A/B
      | (1, 0) => .edge e_bl_a (getEdgeStickerIndex e_bl_a L) -- BL, A(col 1?), L sticker = idx 1
      | (2, 0) => .edge e_bl_b (getEdgeStickerIndex e_bl_b L) -- BL, B(col 2?), L sticker = idx 1
      | (3, 1) => .edge e_dl_a (getEdgeStickerIndex e_dl_a L) -- DL, A(row 1?), L sticker = idx 1 -- CHECKED A/B
      | (3, 2) => .edge e_dl_b (getEdgeStickerIndex e_dl_b L) -- DL, B(row 2?), L sticker = idx 1 -- CHECKED A/B
      | (1, 3) => .edge e_fl_a (getEdgeStickerIndex e_fl_a L) -- FL, A(col 1?), L sticker = idx 1
      | (2, 3) => .edge e_fl_b (getEdgeStickerIndex e_fl_b L) -- FL, B(col 2?), L sticker = idx 1
      | (1, 1) => .center z_l_ul -- Center UL (row 1, col 1)
      | (1, 2) => .center z_l_ur -- Center UR (row 1, col 2)
      | (2, 2) => .center z_l_dr -- Center DR (row 2, col 2)
      | (2, 1) => .center z_l_dl -- Center DL (row 2, col 1)
      | _      => panic! "Impossible L coordinate"
  -- D Face (Yellow): Row 0 = Back, Col 0 = Left
  | (false, Axis.y) => match (loc.row.val, loc.col.val) with
      | (0, 0) => .corner c_dlb (getCornerStickerIndex c_dlb D) -- DLB, D sticker = idx 0
      | (0, 3) => .corner c_drb (getCornerStickerIndex c_drb D) -- DRB, D sticker = idx 0
      | (3, 3) => .corner c_drf (getCornerStickerIndex c_drf D) -- DRF, D sticker = idx 0
      | (3, 0) => .corner c_dfl (getCornerStickerIndex c_dfl D) -- DFL, D sticker = idx 0
      | (0, 1) => .edge e_db_a (getEdgeStickerIndex e_db_a D) -- DB, A(col 1?), D sticker = idx 0
      | (0, 2) => .edge e_db_b (getEdgeStickerIndex e_db_b D) -- DB, B(col 2?), D sticker = idx 0
      | (1, 0) => .edge e_dl_a (getEdgeStickerIndex e_dl_a D) -- DL, A(row 1?), D sticker = idx 0 -- CHECKED A/B
      | (2, 0) => .edge e_dl_b (getEdgeStickerIndex e_dl_b D) -- DL, B(row 2?), D sticker = idx 0 -- CHECKED A/B
      | (3, 1) => .edge e_df_a (getEdgeStickerIndex e_df_a D) -- DF, A(col 1?), D sticker = idx 0
      | (3, 2) => .edge e_df_b (getEdgeStickerIndex e_df_b D) -- DF, B(col 2?), D sticker = idx 0
      | (1, 3) => .edge e_dr_a (getEdgeStickerIndex e_dr_a D) -- DR, A(row 1?), D sticker = idx 0 -- CHECKED A/B
      | (2, 3) => .edge e_dr_b (getEdgeStickerIndex e_dr_b D) -- DR, B(row 2?), D sticker = idx 0 -- CHECKED A/B
      | (1, 1) => .center z_d_ul -- Center UL (row 1, col 1)
      | (1, 2) => .center z_d_ur -- Center UR (row 1, col 2)
      | (2, 2) => .center z_d_dr -- Center DR (row 2, col 2)
      | (2, 1) => .center z_d_dl -- Center DL (row 2, col 1)
      | _      => panic! "Impossible D coordinate"

end Visual
open Orientation Visual

def mapOrientationToVisualColor (o : Orientation) : Color :=
  match o with
  | (true, Axis.x) => Color.red
  | (false, Axis.x) => Color.orange
  | (true, Axis.y) => Color.white
  | (false, Axis.y) => Color.yellow
  | (true, Axis.z) => Color.green
  | (false, Axis.z) => Color.blue

-- Now, let's implement the core logic within FourRubik namespace

open Indexing Visual MoveImpl -- Assuming helpers are in Indexing/MoveImpl

/-- Calculates the visual color of a single sticker based on the abstract cube state. -/
def getStickerVisualColor (s : CubeState) (loc : StickerLocation n_four) : Color :=
  let pieceId := getSolvedPieceInfo loc -- Get Slot & StickerIdx for this location in solved state
  match pieceId with
  | .corner slot sticker_idx =>
      -- Find which original corner piece is currently at this slot
      let origin_slot : CornerSlot := s.corner_perm⁻¹ slot
      -- Get the canonical colors of that original piece
      let canonical_colors := getCanonicalCornerColors origin_slot
      -- Get the current orientation value of whatever piece is at 'slot'
      let ori_val : ZMod 3 := s.corner_ori slot
      -- Apply the orientation value to find the visible color for this sticker_idx
      let current_orientation := applyCornerOrientation canonical_colors ori_val sticker_idx
      -- Convert the result to Visual.Color
      mapOrientationToVisualColor current_orientation
  | .edge slot sticker_idx =>
      -- Find which original edge piece (A/B) is currently at this slot
      let origin_slot : EdgeSlot := s.edge_perm⁻¹ slot
      -- Get the canonical colors of that original piece
      let canonical_colors := getCanonicalEdgeColors origin_slot
      -- Get the current orientation value of whatever piece is at 'slot'
      let ori_val : ZMod 2 := s.edge_ori slot
      -- Apply the orientation value to find the visible color for this sticker_idx
      let current_orientation := applyEdgeOrientation canonical_colors ori_val sticker_idx
      -- Convert the result to Visual.Color
      mapOrientationToVisualColor current_orientation
  | .center slot =>
      -- Find which original center piece is currently at this slot
      let origin_slot : CenterSlot := s.center_perm⁻¹ slot
      -- Get the canonical color of that original piece (centers don't orient)
      let current_orientation := getCanonicalCenterColor origin_slot
      -- Convert the result to Visual.Color
      mapOrientationToVisualColor current_orientation

/-- Converts an abstract CubeState into a visually representable Cube structure. -/
def stateToVisual (s : CubeState) : Cube n_four :=
  -- Helper to create one face
  let mkFace (faceOrientation : Orientation) : Face n_four :=
    { stickers := Id.run do -- Using Id monad for mutable array approach
        -- Create a default row (Array Sticker) using replicate
        let defaultSticker : Sticker := { color := Color.white } -- Default value
        let defaultRow : Array Sticker := Array.replicate n_four defaultSticker
        -- Create the face array (Array (Array Sticker)) using replicate with the default row
        let mut faceStickers := Array.replicate n_four defaultRow
        -- Loop through stickers and set the calculated color
        for r_idx in List.finRange n_four do
          for c_idx in List.finRange n_four do
            let loc : StickerLocation n_four := { face := faceOrientation, row := r_idx, col := c_idx }
            let visualColor := getStickerVisualColor s loc
            -- Update the mutable array:
            -- NOTE: Accessing/setting mutable arrays like this in Id can be tricky.
            -- A purely functional approach using Array.set might be safer depending on context.
            -- Let's stick to the mutable approach for now, assuming it works in this context.
            -- Make sure to handle potential ! errors if indices could be out of bounds (shouldn't happen here)
            let currentRow := faceStickers[r_idx.val]!
            let updatedRow := currentRow.set! c_idx { color := visualColor }
            faceStickers := faceStickers.set! r_idx updatedRow
        return faceStickers -- Return the final array
     }

  -- Create each face by calling the helper
  { front  := mkFace F,
    back   := mkFace B,
    left   := mkFace L,
    right  := mkFace R,
    top    := mkFace U,
    bottom := mkFace D
  }

-- Example Usage (after finishing getEdgeStickerIndex etc.)
def view_initial : IO Unit := printUnfoldedCube (stateToVisual initialState)
def view_after_R : IO Unit := printUnfoldedCube (stateToVisual (apply_move BasicMove.R initialState))
def view_after_U : IO Unit := printUnfoldedCube (stateToVisual (apply_move BasicMove.U initialState))
def view_after_CR : IO Unit := printUnfoldedCube (stateToVisual (apply_move BasicMove.CR initialState))

def apply_move_list (moves : List BasicMove) (start_state : CubeState) : CubeState :=
  List.foldl (fun s m => apply_move m s) start_state moves
def view_URUinv : IO Unit := do
  let moves : List BasicMove := [BasicMove.U, BasicMove.R, BasicMove.U, BasicMove.U, BasicMove.U]
  let final_state := apply_move_list moves initialState
  printUnfoldedCube (stateToVisual final_state)

-- To run these (ensure all helpers like getEdgeStickerIndex are implemented):
#eval view_initial
#eval view_after_R
#eval view_after_U
#eval view_after_CR

#eval view_URUinv

#eval getCanonicalCornerColors c_urf

#eval getCornerStickerIndex c_urf U
#eval getCornerStickerIndex c_urf R
#eval getCornerStickerIndex c_urf F

#eval applyCornerOrientation (U, R, F) 0 (⟨0, by decide⟩ : Fin 3)
#eval applyCornerOrientation (U, R, F) 1 (⟨0, by decide⟩ : Fin 3)
#eval applyCornerOrientation (U, R, F) 1 (⟨1, by decide⟩ : Fin 3)

-- Define the state after one R move
def state_after_R := apply_move BasicMove.R initialState

-- Check the orientation values for the affected slots
-- Note: We check the orientation AT the destination slot index

#eval state_after_R.corner_ori c_urf -- Slot 1 (Piece from DRF, delta +1). Expected: 1
#eval state_after_R.corner_ori c_urb -- Slot 2 (Piece from URF, delta +2). Expected: 2
#eval state_after_R.corner_ori c_drb -- Slot 6 (Piece from URB, delta +1). Expected: 1
#eval state_after_R.corner_ori c_drf -- Slot 5 (Piece from DRB, delta +2). Expected: 2

-- Check an unaffected corner slot
#eval state_after_R.corner_ori c_ufl -- Slot 0 (Unaffected). Expected: 0

#eval "--- Tracing Sticker U(3,3) after R Move ---"

-- Define the state and location we are testing
def loc_U33 : StickerLocation n_four := { face := U, row := ⟨3, by decide⟩, col := ⟨3, by decide⟩ }

-- 1. What PieceStickerID does getSolvedPieceInfo return for this location?
-- Expected: PieceStickerID.corner c_urf 0 (Corner slot 1, sticker index 0)
#eval getSolvedPieceInfo loc_U33

-- Assuming the above is correct (slot=1, sticker_idx=0), let's use these values:
def test_slot : CornerSlot := c_urf -- Slot 1
def test_sticker_idx : Fin 3 := ⟨0, by decide⟩ -- Sticker index 0

-- 2. Which piece originally occupied the slot that moved into slot 1? (s.corner_perm⁻¹ slot)
-- Expected: 5 (c_drf)
def test_origin_slot := state_after_R.corner_perm⁻¹ test_slot
#eval test_origin_slot

-- 3. What are the canonical colors of that original piece (from slot 5)?
-- Expected: (D, R, F)
def test_canonical_colors := getCanonicalCornerColors test_origin_slot
#eval test_canonical_colors

-- 4. What is the orientation value stored AT the destination slot (slot 1) after the move?
-- Expected: 1
def test_ori_val := state_after_R.corner_ori test_slot
#eval test_ori_val

-- 5. What is the result of applying this orientation value (1) to the canonical colors ((D, R, F))
--    for the target sticker index (0)?
-- Expected: F (Green) - Because ori=1, idx=0 should return c2, which is F in (D, R, F)
def test_final_orientation := applyCornerOrientation test_canonical_colors test_ori_val test_sticker_idx
#eval test_final_orientation

-- 6. What Visual.Color does the final Orientation (F) map to?
-- Expected: Color.green
def test_final_visual_color := mapOrientationToVisualColor test_final_orientation
#eval test_final_visual_color

-- 7. What is the final result of the complete getStickerVisualColor function?
-- Expected: Color.green
#eval getStickerVisualColor state_after_R loc_U33

#eval "--- End Tracing ---"
end FourRubik
