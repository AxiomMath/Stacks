module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparisonExists
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth maps of the box product of two complexes of differential operators

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, and write `f = p ∘ a = q ∘ b`. Let `𝓕^•` on `X` and `𝓖^•` on `Y` be `ℤ`-indexed
complexes of quasi-coherent modules whose differentials are differential operators of finite
order on `X/S` and on `Y/S`, both strictly bounded below. This file assembles the two canonical
maps of [Stacks, Tag 0G4A]:

`Ra_*(𝓕^•) ⊗^𝐋_{𝒪_S} Rb_*(𝓖^•) ⟶ Rf_*(Tot(𝓕^• ⊠ 𝓖^•))`  and
`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`,

the second in `D(A)` for `A = Γ(S, 𝒪_S)`. Both are five-step composites: the two pullback maps,
the cup product, the comparison of the derived with the nonderived tensor product, and the
passage to the box product. Steps (1) to (3) are the Künneth map of [Stacks, Tag 0FLP] on the
relative side and the global Künneth map of [Stacks, Tag 0G7V] on the global side, formed for the
inverse-image ringed spaces `(X, a^{-1}𝒪_S) ⟶ (S, 𝒪_S)`, `(Y, b^{-1}𝒪_S) ⟶ (S, 𝒪_S)` and
`(W, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)`, where the pullback of modules along the projections is the inverse
image `p^{-1}`; steps (4) and (5) are `Stacks.Cohomology.BoxKunneth.boxTotalDerivedComparison`.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMap`: **the map
  `Ra_*(𝓕^•) ⊗^𝐋_{𝒪_S} Rb_*(𝓖^•) ⟶ Rf_*(Tot(𝓕^• ⊠ 𝓖^•))`.**
* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMap`: **the map
  `RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`** in `D(A)`, for an arbitrary
  global cup product on the base as its step (3).

## Main results

* `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMap_eq` and `globalBoxKunnethMap_eq`: each map
  is the Künneth map of [Stacks, Tag 0FLP], resp. [Stacks, Tag 0G7V], followed by the derived
  direct image, resp. derived global sections, of steps (4) and (5).
* `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMap_unique` and
  `globalBoxKunnethMap_unique`: **neither map depends on which step-(5) comparison it is built
  from**, that datum being unique.

## Implementation notes

*Boundedness.* Here `Tot(𝓕^• ⊠ 𝓖^•)` is formed in the category of finite-order differential
operators, which has no infinite coproducts, an infinite direct sum of operators of unbounded
order being of no finite order. Both complexes are therefore strictly bounded below, which is the
hypothesis of [Stacks, Tag 0FLT]. For arbitrary complexes the total complex is formed over
`f^{-1}𝒪_S` in `StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMapUnbounded`.

*The step-(5) comparison.* `Stacks.Cohomology.BoxKunneth.BoxTotalComparison` is constructed in
`StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparisonExists` as
`Stacks.Cohomology.BoxKunneth.boxTotalComparison` and is unique by
`Stacks.Cohomology.BoxKunneth.BoxTotalComparison.hom_unique`, so both maps below are built from
it, and `relativeBoxKunnethMap_unique` and `globalBoxKunnethMap_unique` record that building
either from any other such datum gives the same map.

*Step (3) of the global map.* `globalBoxKunnethMap` is stated for an arbitrary `A`-linear global
cup product `Stacks.Cohomology.GlobalKunneth.GlobalCupProduct` on the base. The map of
[Stacks, Tag 0FLR] is its value at the global cup product of [Stacks, Section 0FKU],
`Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical`; that is
`Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapCanonical`, and for complexes with no
boundedness condition `Stacks.Cohomology.BoxKunneth.globalBoxCupProduct`.

*Where the tensor products are formed.* On the left of the relative map it is the derived tensor
product of [Stacks, Tag 06YU] over `𝒪_S`, on the left of the global map the derived tensor
product over `A`, exactly as in the source; the tensor product inside `Tot(𝓕^• ⊠ 𝓖^•)` is the
nonderived one, which is what step (4) compares to.

*The hom universe of the derived category is pinned.* The derived direct image and the derived
global sections are formed at the hom universe `u + 1`, where
`CategoryTheory.HasDerivedCategory.standard` puts them, so that instance is given priority and
the derived direct image and the derived tensor product below carry their universes explicitly.

*No isomorphism is asserted.* [Stacks, Tag 0FLT] and [Stacks, Tag 0FU4] assert that these maps
are isomorphisms under quasi-compactness, affineness of the diagonal and flatness hypotheses;
nothing of the kind is proved here.

## References

* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
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

/-! ### The relative map -/

/-- **The relative Künneth map of the box product**

`Ra_*(𝓕^•) ⊗^𝐋_{𝒪_S} Rb_*(𝓖^•) ⟶ Rf_*(Tot(𝓕^• ⊠ 𝓖^•))`,

for `𝓕^•` on `X/S` and `𝓖^•` on `Y/S` complexes of quasi-coherent modules with differentials
differential operators of finite order, both strictly bounded below, and `f` the structure
morphism of `X ×_S Y`. It is the Künneth map of [Stacks, Tag 0FLP] for the inverse-image ringed
spaces, followed by `Rf_*` of steps (4) and (5). -/
@[stacks 0G4B "the map, corrected: `Tot(F ⊠ G)` is formed under strict boundedness below of both
  complexes, without which it does not exist in the category of finite-order differential
  operators; and steps (1) to (3) are taken with the derived inverse image `Lp^*`, the canonical
  comparison `Lp^*F ⟶ p^{-1}F` being inserted into step (4); the step-(5) comparison
  `Tot(p^{-1}F ⊗ q^{-1}G) ⟶ Tot(F ⊠ G)` is `Stacks.Cohomology.BoxKunneth.boxTotalComparison`"]
def relativeBoxKunnethMap :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      (derivedPushforward.{u, u + 1, u + 1}
          (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj (boxTotalModules a b K L n₁ n₂)) :=
  Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a))
      (fstProjection_comp a b) (sndProjection_comp a b)
      (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (boxTotalDerivedComparison a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂))

/-- **The relative map is the three-step map of [Stacks, Tag 0FLP] followed by the last two
steps.** Steps (1) to (3), the two pullback maps and the relative cup product, are the Künneth
map of [Stacks, Tag 0FLP] for the projections of `(W, f^{-1}𝒪_S)` to `(X, a^{-1}𝒪_S)` and
`(Y, b^{-1}𝒪_S)`; steps (4) and (5) are `boxTotalDerivedComparison`. -/
@[stacks 0G4B "the map is the Künneth map of Tag 0FLP for the inverse-image ringed spaces, which
  is steps (1) to (3) with `Lp^*` for `p^{-1}`, followed by `Rf_*` of steps (4) and (5)"]
theorem relativeBoxKunnethMap_eq :
    relativeBoxKunnethMap a b K L n₁ n₂ =
      Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
          (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
          (inverseImageBaseProjection (pullback.fst a b ≫ a))
          (fstProjection_comp a b) (sndProjection_comp a b)
          (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
        (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (boxTotalDerivedComparison a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂)) :=
  rfl

/-- **The relative map does not depend on which step-(5) comparison it is built from**: that
datum is unique, a morphism out of a total complex being determined by its components on the
summands, and those are prescribed to be the degreewise comparisons. So the map, which uses the
constructed `Stacks.Cohomology.BoxKunneth.boxTotalComparison`, is the same as the map built from
any other such datum `c`. -/
theorem relativeBoxKunnethMap_unique (c : BoxTotalComparison a b K L n₁ n₂) :
    relativeBoxKunnethMap a b K L n₁ n₂ =
      Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
          (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
          (inverseImageBaseProjection (pullback.fst a b ≫ a))
          (fstProjection_comp a b) (sndProjection_comp a b)
          (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
        (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (boxTotalDerivedComparison a b K L n₁ n₂ c) :=
  (relativeBoxKunnethMap_eq a b K L n₁ n₂).trans <|
    congrArg (fun m => _ ≫ (derivedPushforward _).map m)
      (boxTotalDerivedComparison_unique a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂) c)

/-! ### The global map -/

/-- **The global Künneth map of the box product**

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

in `D(A)` for `A = Γ(S, 𝒪_S)`, for `𝓕^•` on `X/S` and `𝓖^•` on `Y/S` complexes of quasi-coherent
modules with differentials differential operators of finite order, both strictly bounded below.
It is the global Künneth map of [Stacks, Tag 0G7V] for the inverse-image ringed spaces, followed
by derived global sections of steps (4) and (5). The tensor product on the left is the derived
one over `A`. Step (3) is the given global cup product `κ` on the base; at the global cup product
of [Stacks, Section 0FKU] this is `globalBoxKunnethMapCanonical`. -/
def globalBoxKunnethMap (κ : GlobalCupProduct S.toRingedSpace) :
    ((tensorBase S.toRingedSpace).obj
          ((sectionsOverBase (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((sectionsOverBase (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj (boxTotalModules a b K L n₁ n₂)) :=
  kunnethGlobalMap (inverseImageBaseProjection a) (inverseImageBaseProjection b)
      (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a))
      (fstProjection_comp a b) (sndProjection_comp a b) κ
      (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
    (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (boxTotalDerivedComparison a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂))

/-- **The global map is the map of [Stacks, Tag 0G7V] followed by the last two steps.** Steps (1)
to (3), the two pullback maps on derived global sections and the global cup product of
[Stacks, Section 0FKU], are the global Künneth map of [Stacks, Tag 0G7V]; steps (4) and (5) are
`boxTotalDerivedComparison`. -/
theorem globalBoxKunnethMap_eq (κ : GlobalCupProduct S.toRingedSpace) :
    globalBoxKunnethMap a b K L n₁ n₂ κ =
      kunnethGlobalMap (inverseImageBaseProjection a) (inverseImageBaseProjection b)
          (fstProjection a b) (sndProjection a b)
          (inverseImageBaseProjection (pullback.fst a b ≫ a))
          (fstProjection_comp a b) (sndProjection_comp a b) κ
          (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
        (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (boxTotalDerivedComparison a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂)) :=
  rfl

/-- **The global map does not depend on which step-(5) comparison it is built from**: that datum
is unique, a morphism out of a total complex being determined by its components on the summands,
and those are prescribed to be the degreewise comparisons. So the map, which uses the constructed
`Stacks.Cohomology.BoxKunneth.boxTotalComparison`, is the same as the map built from any other
such datum `c`. -/
theorem globalBoxKunnethMap_unique (κ : GlobalCupProduct S.toRingedSpace)
    (c : BoxTotalComparison a b K L n₁ n₂) :
    globalBoxKunnethMap a b K L n₁ n₂ κ =
      kunnethGlobalMap (inverseImageBaseProjection a) (inverseImageBaseProjection b)
          (fstProjection a b) (sndProjection a b)
          (inverseImageBaseProjection (pullback.fst a b ≫ a))
          (fstProjection_comp a b) (sndProjection_comp a b) κ
          (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
        (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (boxTotalDerivedComparison a b K L n₁ n₂ c) :=
  (globalBoxKunnethMap_eq a b K L n₁ n₂ κ).trans <|
    congrArg (fun m => _ ≫ (sectionsOverBase _).map m)
      (boxTotalDerivedComparison_unique a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂) c)

end Stacks.Cohomology.BoxKunneth

end
