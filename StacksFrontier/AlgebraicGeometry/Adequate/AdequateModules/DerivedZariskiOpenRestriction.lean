module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedPushforwardAdequate
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedBigSiteHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMapEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackToSmallZariski

/-!
# Restricting a chosen big site to an open subscheme of its base

Let `𝒮` be a big `τ`-site of schemes, `S` and `T` schemes below its cutoff and `g : T ⟶ S` a
morphism, and let `(Sch/S)_τ` and `(Sch/T)_τ` be the localizations of `𝒮` at `S` and at `T`
(`Stacks.Adequate.BigSite.ofAmbient`). Viewing a scheme over `T` as a scheme over `S` through `g`
is `Over.map g`, and base change `X ↦ X ×_S T` is `Over.pullback g`, its right adjoint. On
`𝒪`-modules they give the restriction `j^* : Mod((Sch/S)_τ) ⟶ Mod((Sch/T)_τ)`, `F ↦ F|_T`, and the
direct image `j_*`, `(j_*G)(X) = G(X ×_S T)`, with `j^* ⊣ j_*`.

This file records the properties of `j^*` that the localization arguments of
[Stacks, Tag 070W] use: it is exact, it carries K-injective complexes to K-injective complexes
([Stacks, Tag 08FI]), its unit is restriction along the projections `X ×_S T ⟶ X`, and it is the
pullback of [Stacks, Tag 06VJ], so that adequacy of an `𝒪`-module can be tested on the
restrictions to an open covering of the base ([Stacks, Tag 06VK]).

## Main definitions

* `Stacks.Adequate.openRestrict`: the restriction `j^*`.
* `Stacks.Adequate.openPushforward`: the direct image `j_*`.
* `Stacks.Adequate.openRestrictAdjunction`: the adjunction `j^* ⊣ j_*`.
* `Stacks.Adequate.openRingedToposSiteHom`: base change as a morphism of ringed topoi, whose direct
  image is `j_*`.

## Main results

* `Stacks.Adequate.isKInjective_openRestrict`: `j^*` preserves K-injective complexes.
* `Stacks.Adequate.isAdequate_of_openRestrict`: an `𝒪`-module whose restrictions to the members of
  an open covering of the base are adequate is adequate.

## References

* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 06VJ](https://stacks.math.columbia.edu/tag/06VJ)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} (𝒮 : AlgebraicGeometry.BigSite.{u} τ) {S T : Scheme.{u}}
  (hS : S.size < AlgebraicGeometry.cutoff τ 𝒮) (hT : T.size < AlgebraicGeometry.cutoff τ 𝒮)
  (g : T ⟶ S)

/-- The morphism `T ⟶ S` of the ambient category of schemes. -/
abbrev ambientHom : (⟨T, hT⟩ : SchemeBelow (AlgebraicGeometry.cutoff τ 𝒮)) ⟶ ⟨S, hS⟩ :=
  ObjectProperty.homMk g

/-- `Over.map` along `T ⟶ S` is continuous from the big site over `T` to the big site over `S`. -/
instance isContinuous_overMap_ofAmbient :
    (Over.map (ambientHom 𝒮 hS hT g)).IsContinuous (BigSite.ofAmbient 𝒮 T hT).topology
      (BigSite.ofAmbient 𝒮 S hS).topology := by
  change (Over.map _).IsContinuous (overTopology τ 𝒮 T hT) (overTopology τ 𝒮 S hS)
  rw [overTopology_eq_over' 𝒮 S hS, overTopology_eq_over' 𝒮 T hT]
  infer_instance

/-- Base change `X ↦ X ×_S T` is continuous from the big site over `S` to the big site over
`T`. -/
instance isContinuous_overPullback_ofAmbient :
    (Over.pullback (ambientHom 𝒮 hS hT g)).IsContinuous (BigSite.ofAmbient 𝒮 S hS).topology
      (BigSite.ofAmbient 𝒮 T hT).topology :=
  isContinuous_bigSiteBaseChange 𝒮 (ambientHom 𝒮 hS hT g)

/-- `isContinuous_overMap_ofAmbient`, read with the underlying categories of the two chosen big
sites. -/
instance isContinuous_overMap_ofAmbient' :
    Functor.IsContinuous (C := (BigSite.ofAmbient 𝒮 T hT).category)
      (D := (BigSite.ofAmbient 𝒮 S hS).category) (Over.map (ambientHom 𝒮 hS hT g))
      (BigSite.ofAmbient 𝒮 T hT).topology (BigSite.ofAmbient 𝒮 S hS).topology :=
  isContinuous_overMap_ofAmbient 𝒮 hS hT g

/-- `isContinuous_overPullback_ofAmbient`, read with the underlying categories of the two chosen
big sites. -/
instance isContinuous_overPullback_ofAmbient' :
    Functor.IsContinuous (C := (BigSite.ofAmbient 𝒮 S hS).category)
      (D := (BigSite.ofAmbient 𝒮 T hT).category) (Over.pullback (ambientHom 𝒮 hS hT g))
      (BigSite.ofAmbient 𝒮 S hS).topology (BigSite.ofAmbient 𝒮 T hT).topology :=
  isContinuous_overPullback_ofAmbient 𝒮 hS hT g

/-- Restriction `j^*` of `𝒪`-modules from the big site over `S` to the big site over `T`. -/
def openRestrict :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 T hT).ringedSite.toRingedTopos.O) :=
  SheafOfModules.pushforward.{u} (F := Over.map (ambientHom 𝒮 hS hT g))
    (𝟙 (BigSite.ofAmbient 𝒮 T hT).structureSheaf)

/-- The structure map of the base change `j_*`. -/
def openPushforwardStructureMap :
    (BigSite.ofAmbient 𝒮 S hS).structureSheaf ⟶
      ((Over.pullback (ambientHom 𝒮 hS hT g)).sheafPushforwardContinuous RingCat.{u}
        (BigSite.ofAmbient 𝒮 S hS).topology (BigSite.ofAmbient 𝒮 T hT).topology).obj
        (BigSite.ofAmbient 𝒮 T hT).structureSheaf :=
  ObjectProperty.homMk (Functor.whiskerRight
    (NatTrans.op (Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).counit)
    (BigSite.ofAmbient 𝒮 S hS).structureSheaf.obj)

/-- The direct image `j_*` of `𝒪`-modules along `T ⟶ S`. -/
def openPushforward :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 T hT).ringedSite.toRingedTopos.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O) :=
  SheafOfModules.pushforward.{u} (F := Over.pullback (ambientHom 𝒮 hS hT g))
    (openPushforwardStructureMap 𝒮 hS hT g)

/-- `j^* ⊣ j_*`. -/
def openRestrictAdjunction : openRestrict 𝒮 hS hT g ⊣ openPushforward 𝒮 hS hT g :=
  @SheafOfModules.pushforwardPushforwardAdj.{u} _ _ _ _ (BigSite.ofAmbient 𝒮 T hT).topology
    (BigSite.ofAmbient 𝒮 S hS).topology (Over.map (ambientHom 𝒮 hS hT g))
    (Over.pullback (ambientHom 𝒮 hS hT g)) (BigSite.ofAmbient 𝒮 T hT).structureSheaf
    (BigSite.ofAmbient 𝒮 S hS).structureSheaf (isContinuous_overMap_ofAmbient 𝒮 hS hT g)
    (isContinuous_overPullback_ofAmbient 𝒮 hS hT g) (Over.mapPullbackAdj (ambientHom 𝒮 hS hT g))
    (𝟙 (BigSite.ofAmbient 𝒮 T hT).structureSheaf) (openPushforwardStructureMap 𝒮 hS hT g)
    (by
      ext X : 2
      exact (Category.comp_id _).symm)
    (by
      ext X : 2
      change (Sites.structurePresheaf S (BigSite.ofAmbient 𝒮 S hS).toOver).map
          ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).counit.app
            ((Over.map (ambientHom 𝒮 hS hT g)).obj X.unop)).op ≫
        (Sites.structurePresheaf S (BigSite.ofAmbient 𝒮 S hS).toOver).map
          ((Over.map (ambientHom 𝒮 hS hT g)).map
            ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).unit.app X.unop)).op = 𝟙 _
      have h := congrArg (fun k => (Sites.structurePresheaf S (BigSite.ofAmbient 𝒮 S hS).toOver).map
        k.op) ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).left_triangle_components X.unop)
      simp only [op_comp, op_id] at h
      exact h)

/-- The restriction `j^*` is additive. -/
instance additive_openRestrict : (openRestrict 𝒮 hS hT g).Additive where
  map_add := rfl

/-- The restriction `j^*` preserves finite limits. -/
instance preservesFiniteLimits_openRestrict : PreservesFiniteLimits (openRestrict 𝒮 hS hT g) :=
  @SheafOfModules.preservesFiniteLimits_pushforward _ _ _ _ (Over.map (ambientHom 𝒮 hS hT g))
    (BigSite.ofAmbient 𝒮 T hT).topology (BigSite.ofAmbient 𝒮 S hS).topology
    (isContinuous_overMap_ofAmbient 𝒮 hS hT g) (BigSite.ofAmbient 𝒮 T hT).structureSheaf
    (BigSite.ofAmbient 𝒮 S hS).structureSheaf (𝟙 _)

/-- The restriction `j^*` preserves colimits indexed by categories in `Type`. -/
instance preservesColimits_openRestrict :
    PreservesColimitsOfSize.{0, 0} (openRestrict 𝒮 hS hT g) :=
  (openRestrictAdjunction 𝒮 hS hT g).leftAdjoint_preservesColimits

/-- The restriction `j^*` preserves finite colimits. -/
instance preservesFiniteColimits_openRestrict :
    PreservesFiniteColimits (openRestrict 𝒮 hS hT g) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Restriction to the big site over `T` carries K-injective complexes to K-injective
complexes** ([Stacks, Tag 08FI]): it is restriction along `Over.map` between two slices of one
essentially small site. -/
theorem isKInjective_openRestrict
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos.O)) ℤ)
    [hI : I.IsKInjective] :
    CochainComplex.IsKInjective
      (((openRestrict 𝒮 hS hT g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have hs : EssentiallySmall.{u} (Over (base 𝒮 S hS)) :=
    (BigSite.ofAmbient 𝒮 S hS).essentiallySmall_category
  have hs' : EssentiallySmall.{u} (Over (Over.mk (ambientHom 𝒮 hS hT g))) := by
    show EssentiallySmall.{u} (CostructuredArrow (𝟭 _) _)
    infer_instance
  exact Stacks.Cohomology.Localization.isKInjective_restriction_overMap_of_essentiallySmall
    (siteTopology τ 𝒮) (ambientHom 𝒮 hS hT g) (BigSite.ofAmbient 𝒮 S hS).topology
    (BigSite.ofAmbient 𝒮 T hT).topology (overTopology_eq_over' 𝒮 S hS)
    (overTopology_eq_over' 𝒮 T hT) (isContinuous_overMap_ofAmbient 𝒮 hS hT g)
    (BigSite.ofAmbient 𝒮 S hS).structureSheaf hs
    (BigSite.hasSheafify_addCommGrpCat.{u, u} _).isRightAdjoint
    (BigSite.wEqualsLocallyBijective_addCommGrpCat.{u, u} _)
    (BigSite.hasSheafify_addCommGrpCat.{u, u} _).isRightAdjoint
    (BigSite.wEqualsLocallyBijective_addCommGrpCat.{u, u} _)
    (GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _).isRightAdjoint
    (GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u} _) I hI

/-- The unit of `j^* ⊣ j_*` on sections over an object `X` of the site over `S` is restriction
along the projection `X ×_S T ⟶ X`. -/
theorem openRestrictAdjunction_unit_app_val_app (M : SheafOfModules.{u}
    (BigSite.ofAmbient 𝒮 S hS).structureSheaf) (X : (BigSite.ofAmbient 𝒮 S hS).categoryᵒᵖ) :
    ((openRestrictAdjunction 𝒮 hS hT g).unit.app M).val.app X =
      M.val.map ((Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).counit.app X.unop).op := rfl

/-- The base change `X ↦ X ×_S T`, as a morphism of ringed topoi from the big site over `T` to
the big site over `S`; its direct image is `openPushforward`. -/
def openRingedToposSiteHom :
    RingedToposSiteHom (BigSite.ofAmbient 𝒮 T hT).ringedSite.toRingedTopos
      (BigSite.ofAmbient 𝒮 S hS).ringedSite.toRingedTopos where
  u := Over.pullback (ambientHom 𝒮 hS hT g)
  isContinuous := isContinuous_overPullback_ofAmbient 𝒮 hS hT g
  fSharp := ObjectProperty.homMk (Functor.whiskerRight
    (NatTrans.op (Over.mapPullbackAdj (ambientHom 𝒮 hS hT g)).counit)
    (BigSite.ofAmbient 𝒮 S hS).commStructureSheaf.obj)

/-- The direct image of `Stacks.Adequate.openRingedToposSiteHom` is `j_*`. -/
theorem openRingedToposSiteHom_pushforwardTopos :
    (openRingedToposSiteHom 𝒮 hS hT g).pushforwardTopos = openPushforward 𝒮 hS hT g := rfl

/-- Restriction to the big site over `T` is the pullback `pullbackSheafOfAmbient` of
[Stacks, Tag 06VJ]. -/
def openRestrictObjIso (F : SheafOfModules.{u} (BigSite.ofAmbient 𝒮 S hS).structureSheaf) :
    (openRestrict 𝒮 hS hT g).obj F ≅ pullbackSheafOfAmbient 𝒮 hS hT g F :=
  Iso.refl _

/-- **Adequacy is detected by restriction to the big sites over an open covering of the base.**
If `{gᵢ : Tᵢ ⟶ S}` is a jointly surjective family of open immersions and every restriction
`gᵢ^*𝓕` is adequate on the big site over `Tᵢ`, then `𝓕` is adequate. -/
theorem isAdequate_of_openRestrict {ι : Type (u + 1)} (T : ι → Scheme.{u})
    (hT : ∀ i, (T i).size < AlgebraicGeometry.cutoff τ 𝒮) (g : ∀ i, T i ⟶ S)
    [∀ i, IsOpenImmersion (g i)] (hsurj : (⋃ i, Set.range (g i)) = Set.univ)
    (F : SheafOfModules.{u} (BigSite.ofAmbient 𝒮 S hS).structureSheaf)
    (hF : ∀ i, IsAdequate (BigSite.ofAmbient 𝒮 (T i) (hT i))
      ((openRestrict 𝒮 hS (hT i) (g i)).obj F)) :
    IsAdequate (BigSite.ofAmbient 𝒮 S hS) F :=
  isAdequate_of_coveringPullback _ F ι T g (fun _ ↦ coveringMorphismProperty_of_isOpenImmersion τ _)
    hsurj fun i ↦ ⟨hT i, _, _, _, isSheaf_pullbackVal 𝒮 hS (hT i) (g i) F,
      (adequate.{u, u} _).prop_of_iso (openRestrictObjIso 𝒮 hS (hT i) (g i) F) (hF i)⟩

end Stacks.Adequate

end
