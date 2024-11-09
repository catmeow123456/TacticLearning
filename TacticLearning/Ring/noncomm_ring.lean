import Lean
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Group.Action.Defs

section nat_lit_mul
variable {R : Type*} [NonAssocSemiring R] (r : R) (n : ℕ)

lemma nat_lit_mul_eq_nsmul [n.AtLeastTwo] : no_index (OfNat.ofNat n) * r = n • r := by
  simp only [nsmul_eq_mul, Nat.cast_eq_ofNat]
lemma mul_nat_lit_eq_nsmul [n.AtLeastTwo] : r * no_index (OfNat.ofNat n) = n • r := by
  simp only [nsmul_eq_mul', Nat.cast_eq_ofNat]

end nat_lit_mul

example {R : Type*} [Ring R] (a b c : R) : a * (b + c + c - b) = 2 * a * c := by
  noncomm_ring
  sorry
