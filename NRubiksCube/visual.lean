inductive Color
| white | yellow | red | orange | blue | green
deriving Repr

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

def listToFace (n : Nat) (lst : List (List Color)) : Face n :=
  { stickers := (lst.map (fun (row : List Color) =>
      (row.map (fun (c : Color) => { color := c })).toArray)).toArray }

def custom2Cube : Cube 2 :=
  { front  := listToFace 2 [[Color.green, Color.green],
                            [Color.green, Color.green]],
    back   := listToFace 2 [[Color.blue, Color.blue],
                            [Color.blue, Color.blue]],
    left   := listToFace 2 [[Color.orange, Color.orange],
                            [Color.orange, Color.orange]],
    right  := listToFace 2 [[Color.red, Color.red],
                            [Color.red, Color.red]],
    top    := listToFace 2 [[Color.white, Color.white],
                            [Color.white, Color.white]],
    bottom := listToFace 2 [[Color.yellow, Color.yellow],
                            [Color.yellow, Color.yellow]] }

def custom3Cube : Cube 3 :=
  { front  := listToFace 3 [[Color.green, Color.green, Color.red],
                            [Color.green, Color.red, Color.green],
                            [Color.red, Color.green, Color.green]],
    back   := listToFace 3 [[Color.blue, Color.blue, Color.white],
                            [Color.blue, Color.white, Color.blue],
                            [Color.white, Color.blue, Color.blue]],
    left   := listToFace 3 [[Color.orange, Color.orange, Color.blue],
                            [Color.orange, Color.blue, Color.orange],
                            [Color.blue, Color.orange, Color.orange]],
    right  := listToFace 3 [[Color.red, Color.red, Color.yellow],
                            [Color.red, Color.yellow, Color.red],
                            [Color.yellow, Color.red, Color.red]],
    top    := listToFace 3 [[Color.white, Color.white, Color.green],
                            [Color.white, Color.green, Color.white],
                            [Color.green, Color.white, Color.white]],
    bottom := listToFace 3 [[Color.yellow, Color.yellow, Color.orange],
                            [Color.yellow, Color.orange, Color.yellow],
                            [Color.orange, Color.yellow, Color.yellow]] }

-- should work for any n
def printUnfoldedCube {n : Nat} (cube : Cube n) : IO Unit := do
  -- Print the top face (left-aligned)
  for row in cube.top.stickers do
    IO.println (String.intercalate "" (row.toList.map (fun s => colorToEmoji s.color)))

-- Print blank line
  IO.println ""

  -- Print the middle row: left, front, right, and back faces side-by-side.
  let faces := [cube.left, cube.front, cube.right, cube.back]
  for i in List.range n do
    let row := faces.map (fun f => f.stickers[i]!.toList.map (fun s => colorToEmoji s.color))
    IO.println (String.intercalate " " (row.map (String.intercalate "")))

  -- Print blank line
  IO.println ""

  -- Print the bottom face (left-aligned)
  for row in cube.bottom.stickers do
    IO.println (String.intercalate "" (row.toList.map (fun s => colorToEmoji s.color)))

#eval printUnfoldedCube custom3Cube

#eval printUnfoldedCube custom2Cube
