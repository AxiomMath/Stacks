module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteRingedSite
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# The lower shriek of the small `τ`-site, localized at an object

Let `S` be a scheme of a big fppf site, `τ ∈ {smooth, syntomic, fppf}`, and let
`ι : S_τ ⊆ (Sch/S)_τ` be the inclusion of the small `τ`-site of `S`
(`AlgebraicGeometry.SmallFlatSite`) into the big one, with lower shriek
`ι_! : Mod(S_τ, 𝒪) ⥤ Mod((Sch/S)_τ, 𝒪)`.  For an object `V` of `S_τ` the inclusion localizes to
`ι_V : S_τ/V ⊆ (Sch/S)_τ/V`, again fully faithful, continuous and cocontinuous, and `ι_!`
commutes with localization:

    `(ι_! 𝓝)|_V ≅ ι_{V,!}(𝓝|_V)`.

The localized lower shriek `ι_{V,!}` is again fully faithful, preserves colimits and carries the
structure sheaf to the structure sheaf.

## Main definitions

* `AlgebraicGeometry.SmallFlatSite.starIso`: `ι(W ×_S V) ≅ ι W ×_S ι V`, naturally in `W`.
* `AlgebraicGeometry.SmallFlatSite.overLowerShriek`: the localized lower shriek `ι_{V,!}`.
* `AlgebraicGeometry.SmallFlatSite.lowerShriekOverIso`: `(ι_! 𝓝)|_V ≅ ι_{V,!}(𝓝|_V)`.

## Main results

* `AlgebraicGeometry.SmallFlatSite.fullyFaithfulOverLowerShriek`: `ι_{V,!}` is fully faithful.
* `AlgebraicGeometry.SmallFlatSite.overLowerShriekUnitIso`: `ι_{V,!} 𝒪 ≅ 𝒪`.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- The small `τ`-site of `S` has binary products: fibre products over `S`, computed in the big
site. -/
instance hasBinaryProducts : HasBinaryProducts (SmallFlatSite B S hS κ) := inferInstance

/-- The inclusion of the small `τ`-site into the big site preserves binary products. -/
instance preservesLimitsOfShape_pair :
    PreservesLimitsOfShape (Discrete WalkingPair) (inclusion B S hS κ) := inferInstance

variable (V : SmallFlatSite B S hS κ)

/-- The structure morphism of `X ⨯ Y` over `X` is the first projection. -/
theorem _root_.CategoryTheory.Over.star_obj_hom_eq_fst {C : Type*} [Category* C]
    [HasBinaryProducts C] (X Y : C) :
    ((Over.star X).obj Y).hom = (prod.fst : X ⨯ Y ⟶ X) := by
  simp only [Over.star_obj_hom]
  exact prod.lift_fst _ _

/-- The product comparison map `ι(V ×_S W) ⟶ ι V ×_S ι W` of the inclusion is an isomorphism. -/
instance isIso_prodComparison (W : SmallFlatSite B S hS κ) :
    IsIso (prodComparison (inclusion B S hS κ) V W) := by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

/-- `ι(W ×_S V) ≅ ι W ×_S ι V`, naturally in `W`: the inclusion of the small `τ`-site commutes
with the fibre product with `V`. -/
noncomputable def starIso :
    Over.star V ⋙ Over.post (inclusion B S hS κ) ≅
      inclusion B S hS κ ⋙ Over.star ((inclusion B S hS κ).obj V) :=
  NatIso.ofComponents
    (fun W ↦ Over.isoMk (@asIso _ _ _ _ (prodComparison (inclusion B S hS κ) V W)
      (isIso_prodComparison B S hS κ V W)) (by
      refine (congrArg (prodComparison (inclusion B S hS κ) V W ≫ ·)
        (Over.star_obj_hom_eq_fst _ _)).trans ?_
      refine (prodComparison_fst (inclusion B S hS κ) V W).trans ?_
      exact congrArg (inclusion B S hS κ).map (Over.star_obj_hom_eq_fst V W).symm))
    (fun {W W'} g ↦ Over.OverMorphism.ext (by
      have h := prodComparison_natural (inclusion B S hS κ) (𝟙 V) g
      rw [CategoryTheory.Functor.map_id] at h
      have h1 : ((Over.star V).map g).left = prod.map (𝟙 V) g := by simp; rfl
      have h2 : ((Over.star ((inclusion B S hS κ).obj V)).map ((inclusion B S hS κ).map g)).left =
          prod.map (𝟙 ((inclusion B S hS κ).obj V)) ((inclusion B S hS κ).map g) := by simp; rfl
      change (inclusion B S hS κ).map ((Over.star V).map g).left ≫
          prodComparison (inclusion B S hS κ) V W' =
        prodComparison (inclusion B S hS κ) V W ≫
          ((Over.star ((inclusion B S hS κ).obj V)).map ((inclusion B S hS κ).map g)).left
      rw [h1, h2]
      exact h))

/-- The component of `starIso` at `W` is the product comparison map of the inclusion. -/
theorem starIso_hom_app_left (W : SmallFlatSite B S hS κ) :
    ((starIso B S hS κ V).hom.app W).left = prodComparison (inclusion B S hS κ) V W := rfl

/-- Taking the fibre product with `V` and then including into the localized big site is
continuous. -/
instance isContinuous_inclusionStar :
    (inclusion B S hS κ ⋙ Over.star ((inclusion B S hS κ).obj V)).IsContinuous
      (topology B S hS κ)
      ((BigFppfOver.baseOverTopology B S hS κ.toSiteKind).over ((inclusion B S hS κ).obj V)) :=
  Functor.isContinuous_comp _ _ _ (BigFppfOver.baseOverTopology B S hS κ.toSiteKind) _

/-- Taking the fibre product with `V` in the small site and then including into the localized big
site is continuous. -/
instance isContinuous_starPost :
    (Over.star V ⋙ Over.post (inclusion B S hS κ)).IsContinuous (topology B S hS κ)
      ((BigFppfOver.baseOverTopology B S hS κ.toSiteKind).over ((inclusion B S hS κ).obj V)) :=
  Functor.isContinuous_of_iso (starIso B S hS κ V).symm _ _

/-- The localized inclusion `ι_V : S_τ/V ⊆ (Sch/S)_τ/V` is continuous. -/
instance isContinuous_overPost :
    (Over.post (X := V) (inclusion B S hS κ)).IsContinuous ((topology B S hS κ).over V)
      ((BigFppfOver.baseOverTopology B S hS κ.toSiteKind).over ((inclusion B S hS κ).obj V)) :=
  Functor.isContinuous_overPost _ _ _ V

/-- The comparison of sheaves of rings of the localized inclusion. -/
noncomputable abbrev overComparison :
    (ringStructureSheaf B S hS κ).over V ⟶
      ((Over.post (inclusion B S hS κ)).sheafPushforwardContinuous RingCat.{u}
        ((topology B S hS κ).over V)
        ((BigFppfOver.baseOverTopology B S hS κ.toSiteKind).over
          ((inclusion B S hS κ).obj V))).obj
        ((FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind).over
          ((inclusion B S hS κ).obj V)) :=
  SheafOfModules.overComparison (𝟙 (ringStructureSheaf B S hS κ)) V

/-- The comparison of sheaves of rings of the localized inclusion is the identity. -/
theorem overComparison_eq_id :
    overComparison B S hS κ V = 𝟙 ((ringStructureSheaf B S hS κ).over V) :=
  CategoryTheory.Functor.map_id _ _

/-- Pushforward of presheaves of modules along the localized inclusion is a right adjoint. -/
instance presheafPushforward_overComparison_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := Over.post (X := V) (inclusion B S hS κ))
      (overComparison B S hS κ V).hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall _

/-- Pushforward of sheaves of modules along the localized inclusion is a right adjoint. -/
instance sheafPushforward_overComparison_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (overComparison B S hS κ V)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (overComparison B S hS κ V)).isRightAdjoint

/-- The localized lower shriek `ι_{V,!} : Mod(S_τ/V, 𝒪) ⥤ Mod((Sch/S)_τ/V, 𝒪)`. -/
noncomputable def overLowerShriek :
    SheafOfModules.{u} ((ringStructureSheaf B S hS κ).over V) ⥤
      SheafOfModules.{u} ((FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind).over
        ((inclusion B S hS κ).obj V)) :=
  SheafOfModules.pullback.{u} (overComparison B S hS κ V)

/-- The localized lower shriek is left adjoint to restriction along the localized inclusion. -/
noncomputable def overLowerShriekAdjunction :
    overLowerShriek B S hS κ V ⊣ SheafOfModules.pushforward.{u} (overComparison B S hS κ V) :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (overComparison B S hS κ V)

/-- The localized lower shriek preserves all colimits. -/
noncomputable instance preservesColimitsOfSize_overLowerShriek.{w, w'} :
    PreservesColimitsOfSize.{w, w'} (overLowerShriek B S hS κ V) :=
  (overLowerShriekAdjunction B S hS κ V).leftAdjoint_preservesColimits

/-- The localized lower shriek is fully faithful. -/
noncomputable def fullyFaithfulOverLowerShriek : (overLowerShriek B S hS κ V).FullyFaithful :=
  have adj := (overLowerShriekAdjunction B S hS κ V).ofNatIsoRight
    (SheafOfModules.pushforwardCongr (overComparison_eq_id B S hS κ V))
  have : IsIso adj.unit := Stacks.SheafOfModules.isIso_unit_of_restriction
    (Over.post (X := V) (inclusion B S hS κ)) ((topology B S hS κ).over V)
    ((BigFppfOver.baseOverTopology B S hS κ.toSiteKind).over ((inclusion B S hS κ).obj V))
    ((FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind).over ((inclusion B S hS κ).obj V))
    adj
  adj.fullyFaithfulLOfIsIsoUnit

/-- The localized lower shriek is full. -/
instance : (overLowerShriek B S hS κ V).Full := (fullyFaithfulOverLowerShriek B S hS κ V).full

/-- The localized lower shriek is faithful. -/
instance : (overLowerShriek B S hS κ V).Faithful :=
  (fullyFaithfulOverLowerShriek B S hS κ V).faithful

/-- The localized inclusion is final. -/
instance final_overPost : (Over.post (X := V) (inclusion B S hS κ)).Final := by
  refine ⟨fun Y ↦ isConnected_of_isTerminal _ (x := StructuredArrow.mk (Y := Over.mk (𝟙 V))
    (Over.homMk Y.hom : Y ⟶ (Over.post (inclusion B S hS κ)).obj (Over.mk (𝟙 V)))) ?_⟩
  refine IsTerminal.ofUniqueHom
    (fun W ↦ StructuredArrow.homMk (Over.homMk W.right.hom) ?_)
    (fun W m ↦ StructuredArrow.ext _ _ (Over.OverMorphism.ext ?_))
  · exact Over.OverMorphism.ext (Over.w W.hom)
  · simpa using Over.w m.right

/-- The localized lower shriek carries the structure sheaf to the structure sheaf. -/
noncomputable def overLowerShriekUnitIso :
    (overLowerShriek B S hS κ V).obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} (overComparison B S hS κ V))
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)

/-- The lower shriek commutes with localization at an object of the small `τ`-site:
`(ι_! 𝓝)|_V ≅ ι_{V,!}(𝓝|_V)`, naturally in `𝓝`. -/
noncomputable def lowerShriekOverIso :
    SheafOfModules.overFunctor.{u} (ringStructureSheaf B S hS κ) V ⋙
        overLowerShriek B S hS κ V ≅
      lowerShriek B S hS κ ⋙
        SheafOfModules.overFunctor.{u} (FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind)
          ((inclusion B S hS κ).obj V) :=
  SheafOfModules.overFunctorPullbackIso.{u} (𝟙 (ringStructureSheaf B S hS κ)) V
    (starIso B S hS κ V) (starIso_hom_app_left B S hS κ V)

end AlgebraicGeometry.SmallFlatSite

end
