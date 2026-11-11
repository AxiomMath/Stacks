module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import StacksCore.Tactic.StacksAttribute

/-!
# Wedderburn's theorem for finite-dimensional simple algebras

A simple finite-dimensional algebra `A` over a field `k` is isomorphic to a matrix algebra
`Mat(n × n, D)`, `n ≥ 1`, over a division algebra `D` finite-dimensional over `k`
(Stacks Theorem 11.3.5, tag 0747).

## Main results

* `IsSimpleRing.exists_algEquiv_matrix_divisionRing_of_finite`: Stacks 0747.
-/

@[expose] public section

namespace IsSimpleRing

universe u v

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [Module.Finite k A]

/-- **Wedderburn's theorem**: a simple finite-dimensional algebra `A` over a field `k` is
isomorphic to a matrix algebra `Mat(n × n, D)`, `n ≥ 1`, over a division algebra `D` which is
finite-dimensional over `k`. -/
@[stacks 0747]
theorem exists_algEquiv_matrix_divisionRing_of_finite [IsSimpleRing A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type v) (_ : DivisionRing D) (_ : Algebra k D)
      (_ : Module.Finite k D), Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) := by
  have : IsArtinianRing A := .of_finite k A
  exact exists_algEquiv_matrix_divisionRing_finite k A

end IsSimpleRing
