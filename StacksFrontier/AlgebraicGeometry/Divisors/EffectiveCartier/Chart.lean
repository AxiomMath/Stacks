module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# Closed subschemes of an affine open, as quotients of its ring of sections

Let `X` be a scheme, `I` a closed subscheme of `X` recorded as an
`AlgebraicGeometry.Scheme.IdealSheafData`, and `U ⊆ X` an affine open. Intersecting `I` with `U`
gives a closed immersion into `U ≅ Spec Γ(X, U)`, so the intersection is `Spec` of a quotient of
`Γ(X, U)`; the ideal by which one quotients is `I.ideal U`, and nothing else.

A *chart* for `I` over `U` by an ideal `K ⊆ Γ(X, U)` is an isomorphism
`e : I ×_X U ≅ Spec (Γ(X, U) ⧸ K)` making the triangle with
`AlgebraicGeometry.IsAffineOpen.isoSpec` and `Spec` of the quotient map commute, which is how
[Stacks, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS) phrases "`U ∩ D` is cut out by `K`".
That a chart by `K` forces `I.ideal U = K` is `Stacks.Divisors.ideal_eq_quotient_of_chart`; this
file proves the converse, that `I.ideal U = K` produces a chart by `K`.

## The argument

No computation is needed: `AlgebraicGeometry.IsClosedImmersion.Spec_iff` produces a chart by
*some* ideal, and `Stacks.Divisors.ideal_eq_quotient_of_chart` identifies that ideal with
`I.ideal U`, which is `K`.

## Main results

* `Stacks.Divisors.exists_chart_of_ideal_eq`: `I.ideal U = K` produces a chart by `K`.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- **The ideal determines a chart.** If the closed subscheme `I` cuts out the ideal `K` on an
affine open `U`, then its intersection with `U` is `Spec (Γ(X, U) ⧸ K)`, compatibly with
`AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
theorem exists_chart_of_ideal_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) (hU : IsAffineOpen U) (K : Ideal Γ(X, U))
    (hgen : I.ideal ⟨U, hU⟩ = K) :
    ∃ e : pullback I.subschemeι U.ι ≅ Spec (.of (Γ(X, U) ⧸ K)),
      pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) := by
  obtain ⟨K₀, e₀, he₀⟩ := (IsClosedImmersion.Spec_iff
    (f := pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom)).mp inferInstance
  obtain rfl : K₀ = K := (ideal_eq_quotient_of_chart I U hU K₀ e₀ he₀).symm.trans hgen
  exact ⟨e₀, he₀⟩

end Stacks.Divisors

end
