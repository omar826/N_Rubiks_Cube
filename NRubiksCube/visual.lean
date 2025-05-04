inductive Color
| white | yellow | red | orange | blue | green | black
deriving Repr
def repeatString (s : String) (n : Nat) : String :=
  String.join (List.replicate n s)
structure Sticker where
  color : Color
deriving Repr

structure Face (n : Nat) where
  stickers : Array (Array Sticker)
deriving Repr

structure Cube (n : Nat) where
  front  : Face n
  back   : Face n
  left   : Face n
  right  : Face n
  top    : Face n
  bottom : Face n
deriving Repr

def colorToEmoji (c : Color) : String :=
  match c with
  | Color.white  => "⬜"
  | Color.yellow => "🟨"
  | Color.red    => "🟥"
  | Color.orange => "🟧"
  | Color.blue   => "🟦"
  | Color.green  => "🟩"
  | Color.black  => "⬛"

def listToFace (n : Nat) (lst : List (List Color)) : Face n :=
  { stickers := (lst.map (fun (row : List Color) =>
      (row.map (fun (c : Color) => { color := c })).toArray)).toArray }

-- define solved n x n cube

def solvedCube (n : Nat) : Cube n :=
  { front  := listToFace n (List.replicate n (List.replicate n Color.green)),
    back   := listToFace n (List.replicate n (List.replicate n Color.blue)),
    left   := listToFace n (List.replicate n (List.replicate n Color.orange)),
    right  := listToFace n (List.replicate n (List.replicate n Color.red)),
    top    := listToFace n (List.replicate n (List.replicate n Color.white)),
    bottom := listToFace n (List.replicate n (List.replicate n Color.yellow)) }

  def flipRow (row : List Sticker) : List Sticker :=
    row.reverse

-- should work for any n
def printUnfoldedCube {n : Nat} (cube : Cube n) : IO Unit := do
  -- Print the top face
  let spacer := repeatString "⬛" n
  for row in cube.top.stickers do
    let rowstr := String.intercalate "" (row.toList.map (fun s => colorToEmoji s.color))
    IO.println (spacer ++ " " ++ rowstr)

-- Print blank line
  IO.println ""

  -- Print the middle row: left, front, right, and back faces side-by-side.
  let faces := [
  cube.left.stickers.map (·.toList),
  cube.front.stickers.map (·.toList),
  cube.right.stickers.map (fun row => flipRow (row.toList)),
  cube.back.stickers.map (fun row => flipRow (row.toList))
  ]
  for i in List.range n do
    let row := faces.map (fun face => face[i]!.map (fun s => colorToEmoji s.color))
    IO.println (String.intercalate " " (row.map (String.intercalate "")))

  -- Print blank line
  IO.println ""

  -- Print the bottom face (left-aligned)
  for row in cube.bottom.stickers.toList.reverse do
    let rowstr := row.toList |>.map (fun s => colorToEmoji s.color)
    IO.println (spacer ++ " " ++ String.intercalate "" rowstr)

#eval printUnfoldedCube (solvedCube 2)

#eval printUnfoldedCube (solvedCube 3)

#eval printUnfoldedCube (solvedCube 9)
