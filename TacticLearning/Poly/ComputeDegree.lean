import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas

open Polynomial

example : (1 + X : ℤ[X]).degree = 1 := by compute_degree!
