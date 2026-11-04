module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfect
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackStrictlyPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of a derived internal hom out of a perfect or a pseudo-coherent object

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `K, M ∈ D(𝒪_Y)`.  The canonical
map of Tag 08I3,

`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)`,

is an isomorphism

1. if `K` is perfect, and
2. if `h` is flat, `K` is pseudo-coherent and `M` is locally bounded below.

## Main results

* `isIso_derivedPullbackSheafHomMap_of_isPerfect`: the canonical map is an isomorphism when `K` is
  perfect.
* `isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent`: the canonical map is an isomorphism when
  `h` is flat, `K` is pseudo-coherent and `M` is locally bounded below.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

/-- The canonical map of Tag 08I3 is invertible at every strictly perfect complex, along every
morphism of ringed spaces. -/
theorem strictlyPerfectInvertibility : StrictlyPerfectInvertibility.{u} :=
  fun _ _ g P hP M => isIso_derivedPullbackSheafHomMap_of_isStrictlyPerfect g P hP M

/-- **Pullback of a derived internal hom out of a perfect object.**  For a morphism of ringed
spaces `h : X ⟶ Y`, a perfect `K ∈ D(𝒪_Y)` and an arbitrary `M ∈ D(𝒪_Y)`, the canonical map
`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` is an isomorphism. -/
@[stacks 0GM7 "clause (1)"]
theorem isIso_derivedPullbackSheafHomMap_of_isPerfect
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    IsIso (derivedPullbackSheafHomMap h K M) :=
  isIso_derivedPullbackSheafHomMap_of_isPerfect_of_strictlyPerfect h strictlyPerfectInvertibility
    K hK M

/-- **Flat pullback of a derived internal hom out of a pseudo-coherent object.**  For a flat
morphism of ringed spaces `h : X ⟶ Y`, a pseudo-coherent `K ∈ D(𝒪_Y)` and a locally bounded below
`M ∈ D(𝒪_Y)`, the canonical map `Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` is an isomorphism. -/
@[stacks 0GM7 "clause (2)"]
theorem isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent (hh : AlgebraicGeometry.IsFlat h)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hM : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow Y M) :
    IsIso (derivedPullbackSheafHomMap h K M) :=
  isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_strictlyPerfect h
    strictlyPerfectInvertibility hh K hK M hM

end Stacks.Cohomology.DerivedInternalHomPullback

end
