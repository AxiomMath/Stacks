module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductFromOnePointTensor
import StacksCore.Tactic.StacksAttribute

/-!
# The global Künneth map of the box product at the cup product of [Stacks, Section 0FKU]

`Stacks.Cohomology.BoxKunneth.globalBoxKunnethMap` is stated for an arbitrary morphism of
bifunctors `Stacks.Cohomology.GlobalKunneth.GlobalCupProduct` as its step (3), whereas the
source's step (3) is the cup product constructed in [Stacks, Section 0FKU]. This file states the
map with step (3) the cup product that
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.globalCupProductOfBaseTensorComparison` builds from
a comparison `Stacks.Cohomology.DerivedSectionsLeftAdjoint.BaseTensorComparison` of the two
derived tensor products along the one-point identification.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapOfBaseTensor`: **the map
  `RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`** of [Stacks, Tag 0FLR] whose
  step (3) is the global cup product of [Stacks, Section 0FKU].

## Main results

* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapOfBaseTensor_eq`: **step (3) is the cup
  product of [Stacks, Section 0FKU]** — the map is `globalBoxKunnethMap` at
  `Stacks.Cohomology.DerivedSectionsLeftAdjoint.globalCupProductOfBaseTensorComparison`, so the
  construction of [Stacks, Tag 0G4A] is reused and not repeated.
* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapOfBaseTensor_unique`: it does not depend on
  which step-(5) comparison it is built from.

## Implementation notes

*What this tightens.* `GlobalCupProduct S` is an arbitrary morphism of bifunctors, the zero
morphism included, so `globalBoxKunnethMap` is a family of maps of which only one is the
source's; by
`Stacks.Cohomology.DerivedSectionsOnAPoint.not_isGlobalCupProduct_zero` the zero member is not
it. Composing with `globalCupProductOfBaseTensorComparison` pins step (3) to the relative cup
product of [Stacks, Tag 0B68] for the morphism to the one-point space with ring `A`, which is
the source's map (3), as a function of the one-point tensor comparison.

*The one-point tensor comparison.* It is constructed, as
`Stacks.Cohomology.GlobalKunneth.baseTensorComparison`, and at it the map is
`Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapCanonical`
(`Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapOfBaseTensor_baseTensorComparison`). The
step-(5) comparison `Stacks.Cohomology.BoxKunneth.BoxTotalComparison` is constructed, as
`Stacks.Cohomology.BoxKunneth.boxTotalComparison` in
`StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparisonExists`, and is unique, so
`globalBoxKunnethMapOfBaseTensor_unique` records that the map agrees with the composite built
from any such datum.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]

/-- **The global Künneth map of the box product, with step (3) the cup product of
[Stacks, Section 0FKU]**

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

in `D(A)` for `A = Γ(S, 𝒪_S)`. It is `globalBoxKunnethMap` at the global cup product that
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.globalCupProductOfBaseTensorComparison` builds
from the one-point tensor comparison. -/
def globalBoxKunnethMapOfBaseTensor (τ : BaseTensorComparison S.toRingedSpace) :
    ((tensorBase S.toRingedSpace).obj
          ((sectionsOverBase (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((sectionsOverBase (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj (boxTotalModules a b K L n₁ n₂)) :=
  globalBoxKunnethMap a b K L n₁ n₂
    (globalCupProductOfBaseTensorComparison S.toRingedSpace τ)

/-- **Step (3) of the construction is the global cup product of [Stacks, Section 0FKU].** The
five-step composite itself is `globalBoxKunnethMap`, which is reused and not repeated. -/
theorem globalBoxKunnethMapOfBaseTensor_eq (τ : BaseTensorComparison S.toRingedSpace) :
    globalBoxKunnethMapOfBaseTensor a b K L n₁ n₂ τ =
      globalBoxKunnethMap a b K L n₁ n₂
        (globalCupProductOfBaseTensorComparison S.toRingedSpace τ) :=
  rfl

/-- **The map does not depend on which step-(5) comparison it is built from**, that datum being
unique: it is built from the constructed `Stacks.Cohomology.BoxKunneth.boxTotalComparison`, and
it agrees with the composite formed from any other step-(5) datum `c`. -/
theorem globalBoxKunnethMapOfBaseTensor_unique (τ : BaseTensorComparison S.toRingedSpace)
    (c : BoxTotalComparison a b K L n₁ n₂) :
    globalBoxKunnethMapOfBaseTensor a b K L n₁ n₂ τ =
      kunnethGlobalMap (inverseImageBaseProjection a) (inverseImageBaseProjection b)
          (fstProjection a b) (sndProjection a b)
          (inverseImageBaseProjection (pullback.fst a b ≫ a))
          (fstProjection_comp a b) (sndProjection_comp a b)
          (globalCupProductOfBaseTensorComparison S.toRingedSpace τ)
          (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
        (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (boxTotalDerivedComparison a b K L n₁ n₂ c) :=
  globalBoxKunnethMap_unique a b K L n₁ n₂
    (globalCupProductOfBaseTensorComparison S.toRingedSpace τ) c

end Stacks.Cohomology.BoxKunneth

end
