module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Extension of sheaves to the spaces-étale site under relocalization

Let `g : T ⟶ S` be a morphism of a big fppf site and `X` an algebraic space over `T`. A presheaf
on the small étale site of `X` extends to the spaces-étale site by the right Kan extension along
the comparison functor of Stacks 03G1. This file shows that the extension commutes with the
relocalization `Λ`: extending the restriction `e_X^* G` of a presheaf `G` on the small étale site
of `Λ X` is the same as extending `G` and restricting along `Λ`.

The extension along `cmp_{Λ X}` composed with `Λ` is a pointwise right Kan extension along
`cmp_X`, because the charts of `Λ W` above which the limit is taken are exactly the relocalized
charts of `W`: `Λ` is fully faithful on spaces-étale sites
(`AlgebraicGeometry.Space.relocalizeSpacesEtaleFullyFaithful`) and the small étale sites are
equivalent.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeRanIso`: `Λ ⋙ Ran_{cmp_{Λ X}} G ≅ Ran_{cmp_X} (e_X^* G)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : AlgebraicSpaces B T hT)

/-- Right Kan extensions along the comparison functor of `Λ X` exist; this is
`AlgebraicGeometry.Space.hasPointwiseRightKanExtension_comparisonFunctor` at `Λ X`, which
instance search cannot find through the projection of `relocalizeSpace`. -/
instance hasPointwiseRightKanExtension_comparisonFunctor_relocalize
    (G : (SmallEtale B S hS ((relocalizeSpace B hT hS g X).1))ᵒᵖ ⥤ Type u) :
    (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.HasPointwiseRightKanExtension G :=
  hasPointwiseRightKanExtension_comparisonFunctor B S hS _ G

/-- The comparison `cmp_X ⋙ Λ ≅ e_X ⋙ cmp_{Λ X}` on opposite categories. -/
abbrev relocalizeComparisonOpIso :
    (comparisonFunctor B T hT X).op ⋙ (relocalizeSpacesEtale B hT hS g X).op ≅
      (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op ⋙
        (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op :=
  NatIso.op (relocalizeComparisonIso B hT hS g X)

/-- The charts above `W` are the charts above `Λ W`: the functor between the indexing
categories of the two right Kan extensions. -/
abbrev relocalizeRanIndex (W : SpacesEtale B T hT X) :
    StructuredArrow (op W) (comparisonFunctor B T hT X).op ⥤
      StructuredArrow (op ((relocalizeSpacesEtale B hT hS g X).obj W))
        (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op :=
  StructuredArrow.post (op W) (comparisonFunctor B T hT X).op
      (relocalizeSpacesEtale B hT hS g X).op ⋙
    (StructuredArrow.mapNatIso (relocalizeComparisonOpIso B hT hS g X)).functor ⋙
    StructuredArrow.pre _ (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op
      (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op

/-- The functor between the indexing categories is an equivalence: `Λ` is fully faithful on
spaces-étale sites and the small étale sites are equivalent. -/
instance isEquivalence_relocalizeRanIndex (W : SpacesEtale B T hT X) :
    (relocalizeRanIndex B hT hS g X W).IsEquivalence := by
  have : (relocalizeSpacesEtale B hT hS g X).op.Full := inferInstance
  have : (relocalizeSpacesEtale B hT hS g X).op.Faithful := inferInstance
  have : (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op.IsEquivalence := inferInstance
  infer_instance

variable (G : (SmallEtale B S hS ((relocalizeSpace B hT hS g X).1))ᵒᵖ ⥤ Type u)

/-- The counit exhibiting `Λ ⋙ Ran_{cmp_{Λ X}} G` as a right extension of `e_X^* G` along
`cmp_X`. -/
def relocalizeRanCounit :
    (comparisonFunctor B T hT X).op ⋙ ((relocalizeSpacesEtale B hT hS g X).op ⋙
        (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G) ⟶
      (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op ⋙ G :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (relocalizeComparisonOpIso B hT hS g X).hom
      ((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op
      ((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ranCounit.app G)

/-- **`Λ ⋙ Ran_{cmp_{Λ X}} G` is a pointwise right Kan extension of `e_X^* G` along `cmp_X`.** -/
def relocalizeRan_isPointwiseRightKanExtension :
    (Functor.RightExtension.mk _
      (relocalizeRanCounit B hT hS g X G)).IsPointwiseRightKanExtension :=
  fun W => IsLimit.ofIsoLimit
    ((ranChartIsLimit B S hS (relocalizeSpace B hT hS g X) G
      ((relocalizeSpacesEtale B hT hS g X).obj W.unop)).whiskerEquivalence
        (relocalizeRanIndex B hT hS g X W.unop).asEquivalence)
    (Cones.ext (Iso.refl _) (fun j => by
      dsimp [relocalizeRanCounit]
      rw [Category.id_comp, ← Functor.map_comp_assoc]
      rfl))

/-- **Extension to the spaces-étale site commutes with relocalization**:
`Λ ⋙ Ran_{cmp_{Λ X}} G ≅ Ran_{cmp_X} (e_X^* G)`. -/
def relocalizeRanIso :
    (relocalizeSpacesEtale B hT hS g X).op ⋙
        (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G ≅
      (comparisonFunctor B T hT X).op.ran.obj
        ((SmallEtale.relocalize B hT hS g X.1 X.2).functor.op ⋙ G) :=
  have : ((relocalizeSpacesEtale B hT hS g X).op ⋙
      (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G).IsRightKanExtension
        (relocalizeRanCounit B hT hS g X G) :=
    (relocalizeRan_isPointwiseRightKanExtension B hT hS g X G).isRightKanExtension
  Functor.rightKanExtensionUnique _ (relocalizeRanCounit B hT hS g X G) _
    ((comparisonFunctor B T hT X).op.ranCounit.app _)

/-- The comparison `relocalizeRanIso` composed with the counit of `Ran_{cmp_X}` is the counit
`relocalizeRanCounit`. -/
theorem relocalizeRanIso_hom_fac :
    Functor.whiskerLeft (comparisonFunctor B T hT X).op (relocalizeRanIso B hT hS g X G).hom ≫
        (comparisonFunctor B T hT X).op.ranCounit.app
          ((SmallEtale.relocalize B hT hS g X.1 X.2).functor.op ⋙ G) =
      relocalizeRanCounit B hT hS g X G := by
  have : ((relocalizeSpacesEtale B hT hS g X).op ⋙
      (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.obj G).IsRightKanExtension
        (relocalizeRanCounit B hT hS g X G) :=
    (relocalizeRan_isPointwiseRightKanExtension B hT hS g X G).isRightKanExtension
  simp [relocalizeRanIso]

/-- The comparison `relocalizeRanIso` is natural in the presheaf. -/
theorem relocalizeRanIso_hom_naturality
    {G G' : (SmallEtale B S hS ((relocalizeSpace B hT hS g X).1))ᵒᵖ ⥤ Type u} (φ : G ⟶ G') :
    Functor.whiskerLeft (relocalizeSpacesEtale B hT hS g X).op
        ((comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ran.map φ) ≫
        (relocalizeRanIso B hT hS g X G').hom =
      (relocalizeRanIso B hT hS g X G).hom ≫
        (comparisonFunctor B T hT X).op.ran.map
          (Functor.whiskerLeft (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op φ) := by
  apply Functor.hom_ext_of_isRightKanExtension _
    ((comparisonFunctor B T hT X).op.ranCounit.app
      ((SmallEtale.relocalize B hT hS g X.1 X.2).functor.op ⋙ G'))
  have h₁ := relocalizeRanIso_hom_fac B hT hS g X G
  have h₂ := relocalizeRanIso_hom_fac B hT hS g X G'
  have h₃ := (comparisonFunctor B T hT X).op.ranCounit.naturality
    (Functor.whiskerLeft (SmallEtale.relocalize B hT hS g X.1 X.2).functor.op φ)
  have h₄ := (comparisonFunctor B S hS (relocalizeSpace B hT hS g X)).op.ranCounit.naturality φ
  simp only [Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.id_map] at h₃ h₄
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, Category.assoc, Category.assoc, h₂, h₃,
    ← Category.assoc, h₁]
  refine NatTrans.ext (funext fun U => ?_)
  simp only [relocalizeRanCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Functor.comp_obj]
  rw [← NatTrans.naturality_assoc]
  exact congrArg (_ ≫ ·) (NatTrans.congr_app h₄ _)

end AlgebraicGeometry.Space

end
