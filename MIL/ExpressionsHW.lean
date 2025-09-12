import Lean
open Lean Meta

-- Create expression 1 + 2 with Expr.app.
def one : Expr := .app (.app (.const ``Nat.add []) (mkNatLit 1)) (mkNatLit 2)
elab "one" : term => return one
#check one
#reduce one

-- Create expression 1 + 2 with Lean.mkAppN.
def two : Expr := Lean.mkAppN (.const ``Nat.add []) #[mkNatLit 1, mkNatLit 2]
elab "two" : term => return two
#check two
#reduce two

-- Create expression fun x => 1 + x.
def three : Expr :=
  .lam `x (.const ``Nat [])
  (mkAppN (.const ``Nat.add []) #[mkNatLit 1, .bvar 0])
  BinderInfo.default

elab "three" : term => return three
#check three
#reduce three 6

-- [De Bruijn Indexes] Create expression fun a, fun b, fun c, (b * a) + c.

def four : Expr :=
.lam `a (.const ``Nat [])
  (.lam `b (.const ``Nat [])
    (.lam `c (.const ``Nat [])
      (mkAppN (.const ``Nat.add [])
        #[(mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2]), .bvar 0])
      BinderInfo.default
    ) BinderInfo.default
  ) BinderInfo.default

elab "four" : term => return four
#check four
#reduce four 666 1 2

-- Create expression fun x y => x + y.
def five : Expr :=
  .lam `x (.const ``Nat [])
    (.lam `y (.const ``Nat [])
      (mkAppN (.const ``Nat.add []) #[.bvar 1, .bvar 0])
      BinderInfo.default
    )
  BinderInfo.default

elab "five" : term => return five
#check five
#reduce five 2 3

-- Create expression fun x, String.append "hello, " x.
def six : Expr :=
  .lam `x (.const ``String [])
  (mkAppN (.const ``String.append []) #[mkStrLit "hello, ", .bvar 0])
  BinderInfo.default

elab "six" : term => return six
#check six
#eval six "world"


-- Create expression ∀ x : Prop, x ∧ x.

def seven : Expr :=
  .forallE `x (.sort Lean.levelZero) (mkAppN (.const ``And []) #[.bvar 0, .bvar 0])
  BinderInfo.default

elab "seven" : term => return seven
#check seven
#reduce seven

-- Create expression Nat → String.


def eight : Expr :=
  .forallE `notUsed (.const ``Nat []) (.const ``String []) BinderInfo.default

elab "eight" : term => return eight
#check eight
#reduce eight

-- Create expression fun (p : Prop) => (λ hP : p => hP).

def nine : Expr :=
  .lam `p (.sort Lean.levelZero)
    (.lam `hp (.bvar 0) (.bvar 0) BinderInfo.default)
  BinderInfo.default

elab "nine" : term => return nine
#check nine
#reduce nine

def ten : Expr :=
  .sort (Lean.mkLevelSucc 6) -- or

elab "ten" : term => return ten
#check ten
#reduce ten
-- [Universe levels] Create expression Type 6.
