/-
**Monad Interlude**
The key idea of monads is that each monad encodes a particular kind of side effect using the tools provided by the pure functional language Lean. For example, Option represents programs that can fail by returning none.

Monad <T> means a monad around type T, like Optional <T>. Monad Unit means that there are side effects happening without any result computation?

Looks like maybe monads are a way for sequential-style programming to happen in functional programming.

Example:
-/
-- We can chain option checks like so:
variable (α : Type )
variable (β : Type)
def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

-- To make less combersome, define andThen.
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none -- If we get a none, pass on a none.
  | some x => next x -- If we get something, use it to get next thing.

-- def firstThird' (xs : List α) : Option (α × α) :=
--   andThen xs[0]? fun first =>
--   andThen xs[2]? fun third =>
--   some (first, third)

-- Option is an instance of Monad because Option α represents access to α in the context of the monad Option, in this case signifying that the value may not
instance : Monad Option where
  pure x := some x -- The Pure function of a Monad must take x : α and return M α.
  -- The Bind function unwraps a from M a and applies some f to get M b.
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

/-
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β

  bind : m α >>= f


-/
