module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietorisStageCover
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChangeDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# Extension by zero on the stages of a relative descent situation over `U₀ ∪ V₀`

Let `D` be a relative descent situation and `U₀`, `V₀` quasi-compact opens of `D.X₀` with
quasi-compact union. On each stage of `D` restricted to `U₀ ∪ V₀`, and on its limit, extension by
zero of the restriction to the open cut out by `U₀` (or by `V₀`) commutes with the derived
pullback. At a stage these opens are the open ranges of the inclusions of the stages of the
situations restricted to `U₀` and to `V₀`.

## Main definitions

* `Stacks.ExtensionByZero.precompAddEquiv`: precomposition with an isomorphism, as an additive
  equivalence of morphism groups.
* `AlgebraicGeometry.RelativeDescentSituation.restrictSupRing`, `restrictSupStageRing` and
  `restrictSupLimitRing`: the structure sheaves of `U₀ ∪ V₀`, of a stage and of the limit of the
  restricted situation.
* `AlgebraicGeometry.RelativeDescentSituation.restrictSupStageOpenLeft` and
  `restrictSupStageOpenRight`: the opens cut out by `U₀` and by `V₀` at a stage.
* `AlgebraicGeometry.RelativeDescentSituation.restrictSupStageExtensionIsoLeft`,
  `restrictSupStageExtensionIsoRight`, `restrictSupLimitExtensionIsoLeft` and
  `restrictSupLimitExtensionIsoRight`: extension by zero of the restriction to these opens
  commutes with the derived pullback to a stage and to the limit.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.restrictSupStageOpenLeft_eq_opensRange` and
  `restrictSupStageOpenRight_eq_opensRange`: the open cut out by `U₀` (resp. `V₀`) at a stage is
  the open range of the inclusion of the stage of the situation restricted to `U₀` (resp. `V₀`).

## Implementation notes

`Stacks.ExtensionByZero.derivedExtensionRestriction` is the composite `D(j^*) ⋙ D(j_!)` of the
derived functors, while
`Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.derivedPullbackExtensionRestrictionIso` is
stated for the derived functor `D(j^* ⋙ j_!)` of the composite. The isomorphisms here compose it
with `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso` on both sides.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.ExtensionByZero (derivedExtensionRestriction derivedRestriction)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryCompIso)
open Stacks.Cohomology.ExtensionByZeroBaseChangeDerived (derivedPullbackExtensionRestrictionIso)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.ExtensionByZero

/-- Precomposition with an isomorphism, as an additive equivalence of morphism groups. -/
def precompAddEquiv {C : Type*} [Category* C] [Preadditive C] {A B : C} (Z : C) (i : A ≅ B) :
    (B ⟶ Z) ≃+ (A ⟶ Z) where
  toFun f := i.hom ≫ f
  invFun g := i.inv ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

end Stacks.ExtensionByZero

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

section Sup

variable (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (hV₀ : IsCompact (V₀ : Set D.X₀.left))
  (hsup : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))

/-! ### The structure sheaves and the opens cut out at a stage -/

/-- The structure sheaf of `U₀ ∪ V₀`, as a sheaf of rings. -/
abbrev restrictSupRing :
    Sheaf (Opens.grothendieckTopology
      (U₀ ⊔ V₀ : D.X₀.left.Opens).toScheme.toRingedSpace.carrier) RingCat.{u} :=
  structureSheafRing (U₀ ⊔ V₀ : D.X₀.left.Opens).toScheme.toRingedSpace

/-- The structure sheaf of the stage of the situation restricted to `U₀ ∪ V₀`. -/
abbrev restrictSupStageRing (i : D.LaterIndex) :
    Sheaf (Opens.grothendieckTopology
      ((D.restrict (U₀ ⊔ V₀) hsup).schemeAt i).toRingedSpace.carrier) RingCat.{u} :=
  structureSheafRing ((D.restrict (U₀ ⊔ V₀) hsup).schemeAt i).toRingedSpace

/-- The structure sheaf of the limit of the situation restricted to `U₀ ∪ V₀`. -/
abbrev restrictSupLimitRing :
    Sheaf (Opens.grothendieckTopology
      (D.restrict (U₀ ⊔ V₀) hsup).limitScheme.toRingedSpace.carrier) RingCat.{u} :=
  structureSheafRing (D.restrict (U₀ ⊔ V₀) hsup).limitScheme.toRingedSpace

/-- The open cut out by `U₀` at a stage of the situation restricted to `U₀ ∪ V₀`: the preimage of
`D.restrictSupOpenLeft U₀ V₀` under the map from the stage. -/
abbrev restrictSupStageOpenLeft (i : D.LaterIndex) :
    TopologicalSpace.Opens
      ((D.restrict (U₀ ⊔ V₀) hsup).schemeAt i).toRingedSpace.carrier :=
  (TopologicalSpace.Opens.map
    ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom.hom.base).obj
      (D.restrictSupOpenLeft U₀ V₀)

/-- The open cut out by `V₀` at a stage of the situation restricted to `U₀ ∪ V₀`: the preimage of
`D.restrictSupOpenRight U₀ V₀` under the map from the stage. -/
abbrev restrictSupStageOpenRight (i : D.LaterIndex) :
    TopologicalSpace.Opens
      ((D.restrict (U₀ ⊔ V₀) hsup).schemeAt i).toRingedSpace.carrier :=
  (TopologicalSpace.Opens.map
    ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom.hom.base).obj
      (D.restrictSupOpenRight U₀ V₀)

/-- **The open cut out by `U₀` at a stage is the open range of the inclusion of the stage of the
situation restricted to `U₀`.** -/
theorem restrictSupStageOpenLeft_eq_opensRange (i : D.LaterIndex) :
    D.restrictSupStageOpenLeft U₀ V₀ hsup i =
      (D.restrictToLarger (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i).opensRange :=
  D.preimage_restrictSupOpenLeft U₀ V₀ hU₀ hsup i

/-- **The open cut out by `V₀` at a stage is the open range of the inclusion of the stage of the
situation restricted to `V₀`.** -/
theorem restrictSupStageOpenRight_eq_opensRange (i : D.LaterIndex) :
    D.restrictSupStageOpenRight U₀ V₀ hsup i =
      (D.restrictToLarger (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i).opensRange :=
  D.preimage_restrictSupOpenRight U₀ V₀ hV₀ hsup i

/-! ### Extension by zero commutes with the derived pullback to a stage -/

/-- **Extension by zero of the restriction to the open cut out by `U₀` commutes with the derived
pullback to a stage.** -/
def restrictSupStageExtensionIsoLeft (i : D.LaterIndex) :
    derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenLeft U₀ V₀) ⋙
        derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom ≅
      derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom ⋙
        derivedExtensionRestriction (D.restrictSupStageRing U₀ V₀ hsup i)
          (D.restrictSupStageOpenLeft U₀ V₀ hsup i) :=
  Functor.isoWhiskerRight
      (mapDerivedCategoryCompIso (jStar (D.restrictSupOpenLeft U₀ V₀) (D.restrictSupRing U₀ V₀))
        (jShriek (D.restrictSupOpenLeft U₀ V₀) (D.restrictSupRing U₀ V₀))).symm
      (derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom) ≪≫
    derivedPullbackExtensionRestrictionIso
      ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom
      (D.restrictSupOpenLeft U₀ V₀) ≪≫
    Functor.isoWhiskerLeft
      (derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom)
      (mapDerivedCategoryCompIso _ _)

/-- **Extension by zero of the restriction to the open cut out by `V₀` commutes with the derived
pullback to a stage.** -/
def restrictSupStageExtensionIsoRight (i : D.LaterIndex) :
    derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenRight U₀ V₀) ⋙
        derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom ≅
      derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom ⋙
        derivedExtensionRestriction (D.restrictSupStageRing U₀ V₀ hsup i)
          (D.restrictSupStageOpenRight U₀ V₀ hsup i) :=
  Functor.isoWhiskerRight
      (mapDerivedCategoryCompIso (jStar (D.restrictSupOpenRight U₀ V₀) (D.restrictSupRing U₀ V₀))
        (jShriek (D.restrictSupOpenRight U₀ V₀) (D.restrictSupRing U₀ V₀))).symm
      (derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom) ≪≫
    derivedPullbackExtensionRestrictionIso
      ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom
      (D.restrictSupOpenRight U₀ V₀) ≪≫
    Functor.isoWhiskerLeft
      (derivedPullback ((D.restrict (U₀ ⊔ V₀) hsup).toFixedStage i).toLRSHom.toShHom)
      (mapDerivedCategoryCompIso _ _)

/-- **Extension by zero of the restriction to the open cut out by `U₀` commutes with the derived
pullback to the limit.** -/
def restrictSupLimitExtensionIsoLeft :
    derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenLeft U₀ V₀) ⋙
        derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom ≅
      derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom ⋙
        derivedExtensionRestriction (D.restrictSupLimitRing U₀ V₀ hsup)
          ((TopologicalSpace.Opens.map
            (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom.hom.base).obj
              (D.restrictSupOpenLeft U₀ V₀)) :=
  Functor.isoWhiskerRight
      (mapDerivedCategoryCompIso (jStar (D.restrictSupOpenLeft U₀ V₀) (D.restrictSupRing U₀ V₀))
        (jShriek (D.restrictSupOpenLeft U₀ V₀) (D.restrictSupRing U₀ V₀))).symm
      (derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom) ≪≫
    derivedPullbackExtensionRestrictionIso
      (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom
      (D.restrictSupOpenLeft U₀ V₀) ≪≫
    Functor.isoWhiskerLeft
      (derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom)
      (mapDerivedCategoryCompIso _ _)

/-- **Extension by zero of the restriction to the open cut out by `V₀` commutes with the derived
pullback to the limit.** -/
def restrictSupLimitExtensionIsoRight :
    derivedExtensionRestriction (D.restrictSupRing U₀ V₀) (D.restrictSupOpenRight U₀ V₀) ⋙
        derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom ≅
      derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom ⋙
        derivedExtensionRestriction (D.restrictSupLimitRing U₀ V₀ hsup)
          ((TopologicalSpace.Opens.map
            (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom.hom.base).obj
              (D.restrictSupOpenRight U₀ V₀)) :=
  Functor.isoWhiskerRight
      (mapDerivedCategoryCompIso (jStar (D.restrictSupOpenRight U₀ V₀) (D.restrictSupRing U₀ V₀))
        (jShriek (D.restrictSupOpenRight U₀ V₀) (D.restrictSupRing U₀ V₀))).symm
      (derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom) ≪≫
    derivedPullbackExtensionRestrictionIso
      (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom
      (D.restrictSupOpenRight U₀ V₀) ≪≫
    Functor.isoWhiskerLeft
      (derivedPullback (D.restrict (U₀ ⊔ V₀) hsup).limitToFixedStage.toLRSHom.toShHom)
      (mapDerivedCategoryCompIso _ _)

end Sup

end AlgebraicGeometry.RelativeDescentSituation

end
