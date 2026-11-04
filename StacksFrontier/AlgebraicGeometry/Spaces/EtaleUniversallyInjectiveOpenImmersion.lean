module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# An étale universally injective morphism of algebraic spaces is an open immersion

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is étale and universally injective. Then `f` is an open
immersion.

## Main results

* `AlgebraicGeometry.Space.mono_of_isEtale_of_universallyInjective`: an étale universally
  injective morphism of algebraic spaces over `S` is a monomorphism.
* `AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_universallyInjective`: it is an open
  immersion.

## References

* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale universally injective morphism of algebraic spaces over `S` is a monomorphism. -/
theorem mono_of_isEtale_of_universallyInjective (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (he : IsEtale B S hS f)
    (hui : UniversallyInjective B S hS f) :
    Mono f :=
  ((isUnramified_mono_iff_isUnramified_universallyInjective B S hS hX hY f).mpr
    ⟨isUnramified_of_isEtale B S hS he, hui⟩).2

/-- An étale universally injective morphism of algebraic spaces over `S` is an open immersion. -/
@[stacks 05W5 "the open immersion clause"]
theorem isOpenImmersion_of_isEtale_of_universallyInjective (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (he : IsEtale B S hS f)
    (hui : UniversallyInjective B S hS f) :
    IsOpenImmersion B S hS f :=
  isOpenImmersion_of_isEtale_of_mono B S hS f hX hY he
    (mono_of_isEtale_of_universallyInjective B S hS hX hY f he hui)

end AlgebraicGeometry.Space

end
