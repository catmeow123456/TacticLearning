import Batteries
open Batteries


/-!
# State Monads

* If `s` is a type, then we have a **State Monad** `State s`.
* What this means is that if `α` is a type, then `State s α` is a type so that a term of this type:
  - takes an initial state as input
  - returns a term of type `α`,
  - and a final state.
* Thus, a term of type `State s α` is essentially a function `s → α × s`.
-/
structure State (s α: Type) where
  run : s → α × s

#check StateT
#check StateT.get
#check StateT.set
#check StateM

namespace State
variable {s α: Type}
def get : State s s := ⟨fun s => (s, s)⟩
def update (f: s → s) : State s Unit := ⟨fun s => ((), f s)⟩

def run'[Inhabited s](x: State s α) (s: s := default) : α := (x.run s).1


instance : Monad (State s) where
  pure x := ⟨fun s => (x, s)⟩
  bind x f := ⟨fun s =>
    let (a, s') := x.run s
    (f a).run s'⟩

instance [rep : Repr α][Inhabited s] : Repr (State s α) :=
  ⟨fun mx n => rep.reprPrec mx.run' n⟩

end State

open State
/-!
## The `FibM` State Monad
-/
abbrev FibM := State (HashMap Nat Nat)
/-!
* We have a background state that is a `HashMap Nat Nat`, to store values already computed.
* When computing a term of type `FibM α` we can `get` and use the state and also `set` or `update` it.
* Future computations automatically use the updated state.
* Using this we can efficiently compose.
-/


def fibM (n: Nat) : FibM Nat := do
  let s ← get
  match s.find? n with
  | some y => return y
  | none =>
    match n with
    | 0 => return 1
    | 1 =>  return 1
    | k + 2 => do
      let f₁ ← fibM k
      let f₂ ← fibM (k + 1)
      let sum := f₁ + f₂
      update fun m => m.insert n sum
      return sum

#eval fibM 3
