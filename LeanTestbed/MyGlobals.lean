import Lean

open Lean Elab Tactic

initialize optionStates : IO.Ref (Std.HashMap String SavedState) ←
  IO.mkRef {}
