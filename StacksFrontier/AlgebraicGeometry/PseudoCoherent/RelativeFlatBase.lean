module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeComp09UT

/-!
# Stacks 0CSP, relative pseudo-coherence over a flat base of finite presentation

Let `X ⟶ T ⟶ S` be morphisms of schemes with `T ⟶ S` flat and locally of finite presentation
and `X ⟶ T` locally of finite type. Stacks 0CSP says that an object `E` of `D(𝒪_X)` is
`m`-pseudo-coherent relative to `S` if and only if it is `m`-pseudo-coherent relative to `T`.

A flat morphism locally of finite presentation is pseudo-coherent, which is Stacks 0695 in the
form `AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation`, so this is
Stacks 09UT, `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_comp`, for the base morphism
`T ⟶ S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_iff_of_flat`: **Stacks 0CSP.**

## Implementation notes

The source argues locally on `X`, choosing a closed immersion `X ⟶ 𝔸ⁿ_T` and observing that
`𝔸ⁿ_T ⟶ S` is again flat and locally of finite presentation. That localisation is already carried
out once and for all inside Stacks 09UT, whose hypothesis on the base morphism is exactly
pseudo-coherence; here only Stacks 0695 is needed to supply it.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of this result makes the
same declaration.

## References

* [The Stacks Project, Lemma 37.70.2 (0CSP)](https://stacks.math.columbia.edu/tag/0CSP)
* [The Stacks Project, Lemma 37.59.17 (09UT)](https://stacks.math.columbia.edu/tag/09UT)
* [The Stacks Project, Definition 37.59.2 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 37.60.6 (0695)](https://stacks.math.columbia.edu/tag/0695)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0CSP.** Let `f : X ⟶ T` be locally of finite type, let `g : T ⟶ S` be flat and
locally of finite presentation, let `E` be an object of `D(𝒪_X)` and let `m` be an integer. Then
`E` is `m`-pseudo-coherent relative to `S` if and only if it is `m`-pseudo-coherent relative
to `T`. -/
@[stacks 0CSP]
public theorem isPseudoCoherentFrom_comp_iff_of_flat
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) [LocallyOfFiniteType f] [Flat g]
    [LocallyOfFinitePresentation g] (E : DerivedCategory X.Modules) (m : ℤ) :
    (f ≫ g).IsPseudoCoherentFrom E m ↔ f.IsPseudoCoherentFrom E m :=
  (isPseudoCoherentFrom_iff_comp f g E m).symm

end AlgebraicGeometry.Scheme.Hom

end
