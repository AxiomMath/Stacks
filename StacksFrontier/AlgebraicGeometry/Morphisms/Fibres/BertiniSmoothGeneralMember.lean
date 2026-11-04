module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmoothIrreducibleMember

/-!
# A smooth general member over an infinite field

Over an infinite base field, if the divisors of a general member of a linear system are smooth
(a `Stacks.Bertini.FamilyDivisors.ForGeneral` statement), then the divisor on `X` of some nonzero
vector of the system is smooth.

## Main results

* `Stacks.Bertini.FamilyDivisors.exists_ne_zero_smooth_divisor_of_forGeneral`: over an infinite
  field, smoothness of the general member gives a nonzero vector whose divisor is smooth.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Bertini

namespace FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-- Over an infinite base field `k`, if the linear system `V` has positive dimension and the
specialized divisor of a general member of it is smooth, then some nonzero vector `w` of `V` has
its divisor on `X` smooth over the base. -/
theorem exists_ne_zero_smooth_divisor_of_forGeneral [Infinite D.k]
    (hr : 0 < Module.finrank D.k D.V)
    (h : D.ForGeneral fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :
    ∃ w : D.V, w ≠ 0 ∧ Smooth ((D.divisor w).subschemeι ≫ D.toBase) := by
  obtain ⟨U, hUne, hU⟩ := h
  obtain ⟨c, hc0, hcU⟩ := D.exists_parameterPoint_mem hr U hUne
  exact ⟨∑ i, c i • D.basis i,
    fun hw => hc0 (funext (Fintype.linearIndependent_iff.mp D.basis.linearIndependent c hw)),
    D.smooth_divisor_of_smooth_specializedDivisor c (hU D.k c hcU c rfl)⟩

end FamilyDivisors

end Stacks.Bertini

end
