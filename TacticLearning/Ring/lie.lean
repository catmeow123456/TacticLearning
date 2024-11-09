import Mathlib.Algebra.Lie.Basic

variable {R L: Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable {a b c: L}

#synth LieRingModule L L

example : ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by
  simp only [add_lie]

example : ⁅a + b, c⁆ = -⁅c, a⁆ +(- ⁅c, b⁆) := by
  simp only [add_lie, lie_skew]

example : ⁅a + b, c⁆ = -⁅c, a⁆ - ⁅c, b⁆ := by
  simp only [add_lie, lie_skew]
  sorry

variable {x y z w: L}
example : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  sorry

example : ⁅⁅x, y⁆, ⁅z, w⁆⁆ = ⁅⁅⁅x, y⁆, z⁆, w⁆ - ⁅⁅⁅x, y⁆, w⁆, z⁆ := by
  sorry
