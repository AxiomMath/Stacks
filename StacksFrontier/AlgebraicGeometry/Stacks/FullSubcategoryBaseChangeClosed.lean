module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack

/-!
# A closed substack from closed base changes

Let `𝒳` be an algebraic stack over `S` and let `P` be a property of its objects inherited along
morphisms: `P b` and `a ⟶ b` give `P a`. The base change of the inclusion of the full subcategory
cut out by `P` along a scheme-valued point `z` of `𝒳` with values in `V` is the subfunctor
`AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` of `yoneda V` on the site of `V`.
This file shows that `P` cuts out a **closed substack** of `𝒳` in the sense of **Stacks 04YM**,
part (2), as soon as each of those subfunctors is a closed subspace of `V` (**Stacks 02YU**,
part (3)).

## Main results

* `AlgebraicGeometry.Stack.isClosedImmersion_algebraicSpaceMap_of_isClosedSubspace`: a closed
  subspace of the terminal object of the big fppf site of `U` has closed immersion structural
  morphism over `S`.
* `AlgebraicGeometry.Stack.isClosedSubstack_of_isClosedSubspace`: the closed-substack criterion.

## Implementation notes

This is the closed counterpart of the open construction of
`StacksFrontier/AlgebraicGeometry/Stacks/PointsWithinOpenSubstack.lean` and is proved the same way:
algebraicity of the full subcategory is **Stacks 05UM** in the form
`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces`, and the
closed-immersion clause of **Stacks 04XB** is tested on the one representing algebraic space
`AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` by
`AlgebraicGeometry.Stack.hasRelativeProperty_of_exists_representing`, whose locality input is
**Stacks 0420** at the fppf precoverage.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed subspace of the terminal object of the big fppf site of `U` has closed immersion
structural morphism over `S`.** The structural morphism of **Stacks 04SG** is, up to the
isomorphism `AlgebraicGeometry.isIso_relocalizeToYoneda_yonedaId`, the lower-shriek extension of
the inclusion of the subfunctor, and the lower-shriek extension carries a representable morphism
with a property to one with that property by
`CategoryTheory.OverShriek.presheaf_map_relocalize`. -/
theorem isClosedImmersion_algebraicSpaceMap_of_isClosedSubspace (U : BigFppfOver B S hS)
    (G : Subfunctor (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))) :
      (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u))
    (hG : Space.IsClosedSubspace B U.left.1 U.left.2 G) :
    Space.IsClosedImmersion B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
          ⟨G.toFunctor, hG.1⟩)).hom := by
  have : (Space.closedImmersionProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (prop_algebraicSpaceMap_iff B S hS (Space.closedImmersionProperty B S hS) U
    G.toFunctor hG.1).mpr ?_
  change Space.IsClosedImmersion B S hS (OverShriek.relocalizeToYoneda U.hom G.toFunctor)
  have _ := isIso_relocalizeToYoneda_yonedaId B U.left.1 S U.left.2 hS U.hom
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) := MorphismProperty.RespectsIso.inverseImage _ _
  rw [← relocalizeToYoneda_eq_map_toYonedaId B U.left.1 S U.left.2 hS U.hom G.toFunctor]
  refine (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr ?_
  refine OverShriek.presheaf_map_relocalize U.hom (fun _ hm => hm) ?_
  rw [← subfunctor_ι_eq_toYonedaId B U.left.1 U.left.2 G]
  exact hG.2

variable {B S hS} (𝒳 : AlgebraicStacks.{u, w} B S hS) {P : ObjectProperty 𝒳.val.val.obj}
  (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)

include hP in
/-- **The criterion for a closed substack.** Let `P` be a property of the objects of an algebraic
stack `𝒳` over `S` inherited along morphisms. If for every scheme-valued point `z` of `𝒳` with
values in `V` the subfunctor `AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` of
`yoneda V` cut out by `P` is a closed subspace of `V`, then `P` cuts out a closed substack of `𝒳`
(**Stacks 04YM**, part (2)). -/
theorem isClosedSubstack_of_isClosedSubspace
    (hclosed : ∀ (V : BigFppfOver B S hS)
      (z : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)
      (_hz : z ⋙ 𝒳.val.val.p = Over.map V.hom),
      Space.IsClosedSubspace B V.left.1 V.left.2 (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z)) :
    IsClosedSubstack 𝒳 P := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) :=
    isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion 𝒳 hP
      (fun V z hz => (hclosed V z hz).1)
  have halg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P) :=
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces.{u, w} B S hS
      (𝒳 := CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P)
        (isFiberedInGroupoids_fullSubcategoryBased 𝒳 hP))
      (𝒴 := 𝒳.val)
      (Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 P)) hrep 𝒳.property
  refine ⟨⟨fun e h => hP e.inv h⟩, halg, hrep, ?_⟩
  have : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isClosedImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  refine hasRelativeProperty_of_exists_representing B S hS
    (Space.closedImmersionProperty B S hS)
    (fullSubcategoryInclusion 𝒳 P halg).hom hrep (fun V z hz => ?_)
  refine ⟨(fullSubcategoryBaseChangeSubfunctor 𝒳 hP z).toFunctor, (hclosed V z hz).1,
    nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳 hP z hz, ?_⟩
  exact isClosedImmersion_algebraicSpaceMap_of_isClosedSubspace B S hS V _ (hclosed V z hz)

end AlgebraicGeometry.Stack

end
