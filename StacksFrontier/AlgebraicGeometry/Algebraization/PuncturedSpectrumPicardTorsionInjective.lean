module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardTorsion

/-!
# `Pic(U) → Pic(U₀)` is injective on torsion

Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪` be a nonzerodivisor with
`depth(A/fA) ≥ 2`. Let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. Then
`Pic(U) → Pic(U₀)` is injective on torsion. This is [Stacks, Tag 0F2A].

`StacksFrontier/AlgebraicGeometry/Algebraization/PuncturedSpectrumPicardTorsion.lean` proves this as
`Stacks.Algebraization.picRestrictionInjOnTorsion`, from the polynomiality of the Euler
characteristics of the twists of a coherent triple, [Stacks, Tag 0F27], proved as
`Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp`. This file names it
`Stacks.Algebraization.puncturedClosedFibreRestriction_injOn_torsion`, an alias.

## Main results

* `Stacks.Algebraization.puncturedClosedFibreRestriction_injOn_torsion`:
  **[Stacks, Tag 0F2A]**.

## References

* [Stacks Project, Tag 0F2A](https://stacks.math.columbia.edu/tag/0F2A)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0F2A.** Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪` be a
nonzerodivisor with `depth(A/fA) ≥ 2`. Let `U` be the punctured spectrum of `A` and `U₀` the
punctured spectrum of `A/fA`. Then `Pic(U) → Pic(U₀)` is injective on torsion.

The map is pullback of invertible modules along the restriction `U₀ ⟶ U` of the closed immersion
`Spec(A/fA) ⟶ Spec A`. This is an alias of `Stacks.Algebraization.picRestrictionInjOnTorsion`. -/
@[stacks 0F2A]
alias puncturedClosedFibreRestriction_injOn_torsion := picRestrictionInjOnTorsion

end Stacks.Algebraization

end
