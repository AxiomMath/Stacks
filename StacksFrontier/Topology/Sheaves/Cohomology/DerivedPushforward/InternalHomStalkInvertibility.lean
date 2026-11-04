module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a derived internal hom

Let `(X, 𝒪_X)` be a ringed space, `K, M ∈ D(𝒪_X)` and `x ∈ X`.  The canonical map

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`

is an isomorphism when `K` is perfect, and when `K` is pseudo-coherent and `M` is locally bounded
below.  The point is presented as the one-point ringed space `Y = {x}` with structure sheaf
`𝒪_{X,x}` (`pointStalkPresentation`); the inclusion `Y ⟶ X` is flat, and the displayed map is the
canonical map of Tag 08I3 along it, to which Tag 0GM7 applies.

## Main results

* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMap_of_isPerfect`: case (1).
* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMap_of_isPseudoCoherent`:
  case (2).

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cohomology.DerivedInternalHomStalk

open Stacks.Cohomology.DerivedInternalHomPullback

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

variable (K M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))

/-- The inclusion of the one-point space of the stalk presentation is flat. -/
theorem isFlat_pointStalkPresentation_hom :
    AlgebraicGeometry.IsFlat (pointStalkPresentation X x).hom :=
  isFlat_pointHom X x

/-- **Tag 0GM8, case (1).**  For a ringed space `X`, a point `x ∈ X`, a perfect `K ∈ D(𝒪_X)` and
an arbitrary `M ∈ D(𝒪_X)`, the canonical map

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`

is an isomorphism.  Here `Y = {x}` is the one-point ringed space with structure sheaf `𝒪_{X,x}`,
and the map is the canonical map of Tag 08I3 along the flat inclusion `Y ⟶ X`, read through the
identification `D(𝒪_Y) ≌ D(𝒪_{X,x})` given by the stalk. -/
@[stacks 0GM8 "case (1): K perfect, M arbitrary"]
theorem isIso_stalkSheafHomMap_of_isPerfect
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect (X := X) K) :
    IsIso (stalkSheafHomMap X x (pointStalkPresentation X x) K M) :=
  (isIso_stalkSheafHomMap_iff X x (pointStalkPresentation X x) K M).2
    (isIso_derivedPullbackSheafHomMap_of_isPerfect _ K hK M)

/-- **Tag 0GM8, case (2).**  For a ringed space `X`, a point `x ∈ X`, a pseudo-coherent
`K ∈ D(𝒪_X)` and a locally bounded below `M ∈ D(𝒪_X)`, the canonical map

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`

is an isomorphism, the map being that of `isIso_stalkSheafHomMap_of_isPerfect`. -/
@[stacks 0GM8 "case (2): K pseudo-coherent, M locally bounded below"]
theorem isIso_stalkSheafHomMap_of_isPseudoCoherent
    (hK : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) K)
    (hM : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow X M) :
    IsIso (stalkSheafHomMap X x (pointStalkPresentation X x) K M) :=
  (isIso_stalkSheafHomMap_iff X x (pointStalkPresentation X x) K M).2
    (isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent _
      (isFlat_pointStalkPresentation_hom X x) K hK M hM)

end Stacks.Cohomology.DerivedInternalHomStalk

end
