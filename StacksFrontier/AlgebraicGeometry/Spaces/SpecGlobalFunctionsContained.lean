module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare

/-!
# The spectrum of the global functions of a quasi-compact algebraic space is in the site

The big fppf site of `S` is bounded by a size cutoff, so the spectrum of a `u`-ring need not be an
object of it. For the ring of global regular functions of an algebraic space with a *surjective*
étale scheme chart it is: restriction to the chart is injective, so the ring injects into the
regular functions of a scheme already in the site, and
`AlgebraicGeometry.Scheme.size_Spec_lt_of_injective_sections` bounds the size of its spectrum by
that of the chart. The same bound then carries to the spectrum of any algebra of finite type over
it, by `AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType`.

These are the two containments the concluding descent step of the proof of Stacks 07SQ needs: the
ring `A_i = Γ(X_i, 𝒪)` of a stage and the presentation `B_i = A_i[x₁, …, xₙ] ⧸ (g₁, …, gₙ)` over
it both have spectra in the site, so the fppf covering `Spec B_i ⟶ Spec A_i` along which
affineness is descended is a covering *of the site*.

## Main results

* `AlgebraicGeometry.Space.contains_spec_of_globalFunctionsEquiv`: the spectrum of a `u`-model of
  the global functions of an algebraic space with a surjective étale chart is contained in the
  site.
* `AlgebraicGeometry.Space.contains_spec_presentationAlgebra`: so is the spectrum of a polynomial
  presentation over such a model.

## Implementation notes

`AlgebraicGeometry.BigFppfSite.Contains` is by definition the size bound, so no conversion lemma
intervenes; the two size results are applied with `κ := B.cutoff` and the site's own
`aleph0_lt_cutoff` and `cutoff_isStrongPrelimit`. The size bound for the chart itself is the
defining property of its underlying object of the site.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The spectrum of a `u`-model of the global functions of an algebraic space with a surjective
étale chart is contained in the site.** -/
theorem contains_spec_of_globalFunctionsEquiv (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) (hV : IsSurjective B S hS V.1.hom) (A : Type u) [CommRing A]
    (e : A ≃+* globalFunctions B S hS X.1) :
    B.Contains (Spec (CommRingCat.of A)) :=
  Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (p := CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp e.toRingHom))
    ((injective_globalFunctionsChartRestriction_of_isSurjective B S hS X V hV).comp
      e.injective)
    ((SmallEtale.toOver B S hS X.1).obj V).left.property

/-- **The spectrum of a polynomial presentation over a `u`-model of the global functions of an
algebraic space with a surjective étale chart is contained in the site.** -/
theorem contains_spec_presentationAlgebra (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) (hV : IsSurjective B S hS V.1.hom) (A : Type u) [CommRing A]
    (e : A ≃+* globalFunctions B S hS X.1) {n : ℕ} (g : Fin n → MvPolynomial (Fin n) A) :
    B.Contains (Spec (CommRingCat.of (presentationAlgebra g))) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A
    (presentationAlgebra g)
    (contains_spec_of_globalFunctionsEquiv B S hS X V hV A e)

end AlgebraicGeometry.Space

end
