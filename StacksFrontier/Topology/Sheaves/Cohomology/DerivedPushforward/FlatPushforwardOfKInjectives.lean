module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward along a flat morphism preserves K-injective complexes

Let `f : X ⟶ Y` be a flat morphism of ringed spaces, that is, one whose every germ map
`𝒪_{Y, f(x)} ⟶ 𝒪_{X, x}` is a flat ring homomorphism.  Then degreewise pushforward carries a
K-injective complex of `𝒪_X`-modules to a K-injective complex of `𝒪_Y`-modules.

## Main results

* `RingedSpaceModuleAdjunction.isKInjective_modulePushforward_of_isFlat`: pushforward along a
  flat morphism of ringed spaces preserves K-injectivity of cochain complexes.

## Implementation notes

The proof is the adjoint criterion for K-injectivity [Stacks, Tag 08BJ], available as
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, applied to the adjunction
`f^* ⊣ f_*`: for a flat morphism the left adjoint `f^*` is exact, which is
`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat` together with the
unconditional right exactness `RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback`.
This is the same route as the source's, which deduces the statement from the hom-set bijection
`Hom_{K(𝒪_Y)}(ℱ^•, f_* ℐ^•) = Hom_{K(𝒪_X)}(f^* ℱ^•, ℐ^•)` of [Stacks, Tag 0096] and exactness of
`f^*`.

## References

* [Stacks Project, Tag 0D5Z](https://stacks.math.columbia.edu/tag/0D5Z)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace RingedSpaceModuleAdjunction

/-- **Stacks 0D5Z.** If `f : X ⟶ Y` is a flat morphism of ringed spaces and `ℐ^•` is a
K-injective complex of `𝒪_X`-modules, then `f_* ℐ^•` is K-injective as a complex of
`𝒪_Y`-modules. -/
@[stacks 0D5Z]
theorem isKInjective_modulePushforward_of_isFlat {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.IsFlat f)
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := preservesFiniteLimits_modulePullback_of_isFlat f hf
  have := preservesFiniteColimits_modulePullback f
  have := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (modulePushforward f)
    (modulePullback f) (modulePullbackPushforwardAdjunction f) I

end RingedSpaceModuleAdjunction

end
