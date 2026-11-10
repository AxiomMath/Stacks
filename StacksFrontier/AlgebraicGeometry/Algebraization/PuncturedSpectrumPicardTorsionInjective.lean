module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInductionStep
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardTorsion

/-!
# `Pic(U) → Pic(U₀)` is injective on torsion

Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪` be a nonzerodivisor with
`depth(A/fA) ≥ 2`. Let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. Then
`Pic(U) → Pic(U₀)` is injective on torsion. This is [Stacks, Tag 0F2A].

`StacksFrontier/AlgebraicGeometry/Algebraization/PuncturedSpectrumPicardTorsion.lean` deduces this
from the polynomiality of the Euler characteristics of the twists of a coherent triple, which it
takes as the argument `Stacks.Algebraization.IsCoherentTripleHilbertPolynomial`. That polynomiality
is [Stacks, Tag 0F27], proved as `Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp`.
This file supplies it, so the statement here stands at exactly the hypotheses of the source.

## Main results

* `Stacks.Algebraization.isCoherentTripleHilbertPolynomial`: [Stacks, Tag 0F27] in the
  degree-free reading `Stacks.Algebraization.IsCoherentTripleHilbertPolynomial`.
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

/-- **[Stacks, Tag 0F27]**, in the degree-free reading
`Stacks.Algebraization.IsCoherentTripleHilbertPolynomial`: for a coherent triple `T` and an
invertible coherent triple `L` over a Noetherian local ring, `n ↦ χ(T ⊗ L^{⊗ n})` is a rational
polynomial on `ℤ`. This is `Stacks.Algebraization.exists_polynomial_natDegree_le_dim_supp` with
its bound on the degree forgotten. -/
public theorem isCoherentTripleHilbertPolynomial : IsCoherentTripleHilbertPolynomial.{u} :=
  by
    rintro A _ _ _ f hf - T L hL
    obtain ⟨P, -, hP⟩ := exists_polynomial_natDegree_le_dim_supp hf L hL T
    exact ⟨P, hP⟩

/-- **Stacks Project, Tag 0F2A.** Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪` be a
nonzerodivisor with `depth(A/fA) ≥ 2`. Let `U` be the punctured spectrum of `A` and `U₀` the
punctured spectrum of `A/fA`. Then `Pic(U) → Pic(U₀)` is injective on torsion.

The map is pullback of invertible modules along the restriction `U₀ ⟶ U` of the closed immersion
`Spec(A/fA) ⟶ Spec A`. This is `Stacks.Algebraization.picRestrictionInjOnTorsion` with its
polynomiality argument supplied by `Stacks.Algebraization.isCoherentTripleHilbertPolynomial`. -/
@[stacks 0F2A]
public theorem puncturedClosedFibreRestriction_injOn_torsion (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hfm : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hb : 2 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f})) :
    Set.InjOn (Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f))
      {x : Stacks.Picard.ofScheme (Stacks.Divisors.puncturedSpectrum A).toScheme |
        IsOfFinAddOrder x} :=
  picRestrictionInjOnTorsion A f hfm hreg hb isCoherentTripleHilbertPolynomial

end Stacks.Algebraization

end
