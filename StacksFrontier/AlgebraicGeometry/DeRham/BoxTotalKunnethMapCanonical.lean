module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapCanonical
import StacksCore.Tactic.StacksAttribute

/-!
# The global Künneth map of the box product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, write `f = p ∘ a = q ∘ b` and set `A = Γ(S, 𝒪_S)`. For `𝓕^•` on `X/S` and `𝓖^•` on
`Y/S` complexes of quasi-coherent modules whose differentials are differential operators of finite
order, both strictly bounded below, this file defines the global cup product

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

in `D(A)`, with step (3) the global cup product of [Stacks, Section 0FKU],
`Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical`.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapCanonical`: the map.

## Main results

* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapCanonical_eq`: it is the global Künneth map
  `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical` of [Stacks, Tag 0G7V] for the
  inverse-image ringed spaces, which is steps (1) to (3), followed by derived global sections of
  steps (4) and (5).
* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapOfBaseTensor_baseTensorComparison`: it is
  `globalBoxKunnethMapOfBaseTensor` at the one-point tensor comparison
  `Stacks.Cohomology.GlobalKunneth.baseTensorComparison`.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
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

/-- **The global cup product of the box product**

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

in `D(A)` for `A = Γ(S, 𝒪_S)`, for `𝓕^•` on `X/S` and `𝓖^•` on `Y/S` complexes of quasi-coherent
modules whose differentials are differential operators of finite order, both strictly bounded
below. It is `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMap` at the global cup product
`Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical` of [Stacks, Section 0FKU]. -/
def globalBoxKunnethMapCanonical :
    ((tensorBase S.toRingedSpace).obj
          ((sectionsOverBase (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((sectionsOverBase (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj (boxTotalModules a b K L n₁ n₂)) :=
  globalBoxKunnethMap a b K L n₁ n₂ (globalCupProductCanonical S.toRingedSpace)

/-- **The map is the five-step composite.** Steps (1) to (3), the two pullback maps on derived
global sections and the global cup product of [Stacks, Section 0FKU], are the global Künneth map
`Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical` of [Stacks, Tag 0G7V]; steps (4) and
(5) are `boxTotalDerivedComparison` at the step-(5) comparison `boxTotalComparison`. -/
theorem globalBoxKunnethMapCanonical_eq :
    globalBoxKunnethMapCanonical a b K L n₁ n₂ =
      kunnethGlobalMapCanonical (inverseImageBaseProjection a) (inverseImageBaseProjection b)
          (fstProjection a b) (sndProjection a b)
          (inverseImageBaseProjection (pullback.fst a b ≫ a))
          (fstProjection_comp a b) (sndProjection_comp a b)
          (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
        (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (boxTotalDerivedComparison a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂)) :=
  rfl

/-- **The map is the one built from the constructed one-point tensor comparison**
`Stacks.Cohomology.GlobalKunneth.baseTensorComparison`. -/
theorem globalBoxKunnethMapOfBaseTensor_baseTensorComparison :
    globalBoxKunnethMapOfBaseTensor a b K L n₁ n₂ (baseTensorComparison S.toRingedSpace) =
      globalBoxKunnethMapCanonical a b K L n₁ n₂ :=
  rfl

end Stacks.Cohomology.BoxKunneth

end
