import Lean.Elab.Tactic.Location
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import TacticLearning.Display.Basic

open Lean Meta Elab Tactic
open Polynomial

/--
  Elaborate a term `t` to `polyExpr` ensuring that it has type `Polynomial Xtype`
  Return the tuple `(polyExpr, Xtype)`
-/
def elabTermEnsuringPoly (t: TSyntax `term) : TacticM (Expr × Expr) := do
  try
    let type := Lean.Expr.sort (.succ (.zero))
    let m1 ← mkFreshExprMVar type
    let m2 ← mkFreshExprMVar (.app (.const `Semiring [.zero]) m1 : Expr)
    let expr : Expr := .app (.app (.const `Polynomial [.zero]) m1) m2
    let e ← elabTermEnsuringType t expr
    -- logInfo m!"information: {t} -> {e} : {← inferType e}"
    pure (e, m1)
  catch _ =>
    throwError m!"{t} can't be elaborated as a term of type Polynomial R"

/--
  Add a hypothesis of the form `name : poly.coeff num = RHS` to the context
  where `poly` is the polynomial represented by `t`, `RHS` will be calculated automatically by tactic.
  The polynomial must be specifically written as a sum of monomials so that the `coeff` result can be easily calculated.
-/
elab "addhyp" name:ident ":" "coeff" id:term "of" t:term: tactic => do
  let num ← elabTermEnsuringType id (mkConst ``Nat)
  let (polyExpr, Xtype) ← elabTermEnsuringPoly t
  let LHS ← mkAppM ``Polynomial.coeff #[polyExpr, num]
  let RHS ← mkFreshExprMVar Xtype
  let goal ← mkAppM ``Eq #[LHS, RHS]

  let unsolved_goal ← mkFreshExprMVar goal
  liftMetaTactic1 fun g => do
    let (_, g) ← g.note name.getId unsolved_goal
    pure g
  let goals := unsolved_goal.mvarId! :: (← getGoals)
  modify fun _ => { goals := goals }
  (← getMainGoal).withContext do
    evalTactic (← `(tactic|try simp))
    evalTactic (← `(tactic|try rw [Polynomial.coeff_eq_zero_of_degree_lt (by simp)]))
    evalTactic (← `(tactic|try conv at $name => rhs; norm_num))
    evalTactic (← `(tactic|repeat rfl))


example : (1+1+1+X : Polynomial ℤ).coeff 1 = 1 ∧ (1: Polynomial ℤ).coeff 1 = 0 := by
  addhyp banana : coeff 1 of (1+1+1 + X : ℤ[X])
  addhyp apple : coeff 1 of (1 : ℤ[X])
  simp only [banana, apple, and_self]

example : (2*X + X^2: Polynomial ℤ).coeff 1 = 2 := by
  addhyp apple : coeff 1 of (2*X + X^2 : ℤ[X])
  exact apple

example : (2*X + X^2 + X^3 - 2 * X^2 - 2 * X^3: Polynomial ℤ).coeff 2 = -1 := by
  addhyp apple0 : coeff 0 of (2*X + X^2 + X^3 - 2 * X^2 - 2 * X^3 : ℤ[X])
  addhyp apple1 : coeff 1 of (2*X + X^2 + X^3 - 2 * X^2 - 2 * X^3 : ℤ[X])
  addhyp apple2 : coeff 2 of (2*X + X^2 + X^3 - 2 * X^2 - 2 * X^3 : ℤ[X])
  addhyp apple3 : coeff 3 of (2*X + X^2 + X^3 - 2 * X^2 - 2 * X^3 : ℤ[X])
  addhyp apple4 : coeff 4 of (2*X + X^2 + X^3 - 2 * X^2 - 2 * X^3 : ℤ[X])
  exact apple2

example : (100*X^23 - 30 * X^3 + 3 : Polynomial ℤ).coeff 1 = 0
  ∧ (100*X^23 - 30 * X^3 + 3 : Polynomial ℤ).coeff 3 + 30 = 0
  ∧ 100 - (100*X^23 - 30 * X^3 + 3 : Polynomial ℤ).coeff 23 = 0 := by
  addhyp apple0 : coeff 1 of (100*X^23 - 30 * X^3 + 3 : ℤ[X])
  addhyp apple1 : coeff 3 of (100*X^23 - 30 * X^3 + 3 : ℤ[X])
  addhyp apple2 : coeff 23 of (100*X^23 - 30 * X^3 + 3 : ℤ[X])
  simp only [apple0, apple1, apple2, and_self]
  norm_num
