module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocalSliceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelDerivedPullbackSquarePaste
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleDerivedComparison
public import StacksFrontier.CategoryTheory.Triangulated.RestrictionSquareGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.CategoryTheory.Triangulated.SupportedGlue

/-!
# Glueing along elementary distinguished squares on the spaces-étale models

Let `(U ⊆ W, V ⟶ W)` be an elementary distinguished square of algebraic spaces with intersection
`P`. On the small étale sites, Stacks 08HB glues objects and morphisms along the square
(`AlgebraicGeometry.Space.exists_glued_object_and_hom`), and objects restricting to zero on `U` and
on `V` are zero. This file records these as the properties
`CategoryTheory.RestrictionSquare.ObjectsGlue`, `…HomsGlue` and `…ReflectsIso` of the square of
restriction functors, and carries them to the models of the spaces-étale sites, where the
restrictions are the derived pullbacks along the morphisms of models and the identification over
`P` is the square of derived pullbacks
(`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackSquareIso`).

The transport goes through the equivalences of Stacks 03G1 and the comparisons
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackOfEtaleTransportIso` of the derived étale
pullbacks; it uses that these comparisons are compatible with composition,
`AlgebraicGeometry.Space.SpacesEtaleModelEtaleTransportCoherent`, which is an explicit hypothesis
of the transported glueing statements here.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtaleModelEtaleTransportCoherent`: the comparisons of derived
  étale pullbacks on the models and on the small étale sites are compatible with composition.
* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackSquareIso`: the square of derived
  pullbacks around a commutative square, as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.objectsGlue_eds`, `…homsGlue_eds`, `…reflectsIso_eds`: on the small
  étale sites.
* `AlgebraicGeometry.Space.objectsGlue_spacesEtaleModel_eds`, `…homsGlue_spacesEtaleModel_eds`,
  `…reflectsIso_spacesEtaleModel_eds`: on the models.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparisons of derived étale pullbacks on the models and on the small étale sites are
compatible with composition**: for étale `f : X ⟶ Y` and `g : Y ⟶ Z`, the comparison
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackOfEtaleTransportIso` along `f ≫ g`, read
through `Lf^* Lg^* ≅ L(f ≫ g)^*` on the models and `D(g^*) ⋙ D(f^*) ≅ D((f ≫ g)^*)` on the small
étale sites, is the composite of the comparisons along `g` and `f`. -/
def SpacesEtaleModelEtaleTransportCoherent : Prop :=
  ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom)
    (hg : IsEtale B S hS g.hom) (hfg : IsEtale B S hS (f ≫ g).hom)
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS Z).Modules),
    (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.map
        ((spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom.app K) ≫
      (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (f ≫ g) hfg).hom.app K =
    (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS f hf).hom.app
        ((derivedPullback (spacesEtaleModelHom B S hS g)).obj K) ≫
      (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.map
        ((spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS g hg).hom.app K) ≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (etaleModulePullback.{u, u} B S hS g hg) (etaleModulePullback.{u, u} B S hS f hf)).inv.app
          ((spacesEtaleModelModulesEquiv B S hS Z).functor.mapDerivedCategory.obj K) ≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (etaleModulePullbackComp B S hS f g hf hg hfg)).hom.app
          ((spacesEtaleModelModulesEquiv B S hS Z).functor.mapDerivedCategory.obj K)

/-- **The comparisons of derived étale pullbacks on the models and on the small étale sites are
compatible with composition** (`AlgebraicGeometry.Space.SpacesEtaleModelEtaleTransportCoherent`):
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackOfEtaleTransportIso_comp`. -/
theorem spacesEtaleModelEtaleTransportCoherent : SpacesEtaleModelEtaleTransportCoherent B S hS :=
  fun f g hf hg hfg K =>
    spacesEtaleModelDerivedPullbackOfEtaleTransportIso_comp B S hS f g hf hg hfg K

section Small

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The identification of the two iterated restrictions to the intersection of an elementary
distinguished square on the small étale sites, `D(j_U^*) ⋙ D(pr₁^*) ≅ D(j_V^*) ⋙ D(pr₂^*)`. -/
def edsDerivedRestrictSquareIso :
    (edsRestrictOpen B S hS hsq).mapDerivedCategory ⋙
        (edsRestrictFst B S hS hsq).mapDerivedCategory ≅
      (edsRestrictEtale B S hS hsq).mapDerivedCategory ⋙
        (edsRestrictSnd B S hS hsq).mapDerivedCategory :=
  edsDerivedRestrictCompOpen B S hS hsq ≪≫ (edsDerivedRestrictCompEtale B S hS hsq).symm

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat

/-- **Stacks 08HB, glueing of objects, on the small étale sites.** -/
theorem objectsGlue_eds :
    RestrictionSquare.ObjectsGlue (edsRestrictOpen B S hS hsq).mapDerivedCategory
      (edsRestrictEtale B S hS hsq).mapDerivedCategory
      (edsRestrictFst B S hS hsq).mapDerivedCategory
      (edsRestrictSnd B S hS hsq).mapDerivedCategory (edsDerivedRestrictSquareIso B S hS hsq) :=
  fun A Bo c => by
    obtain ⟨F, f, g, hc, -⟩ := exists_glued_object_and_hom B S hS hsq A Bo c
    refine ⟨F, f, g, hc.trans ?_⟩
    simp [edsDerivedRestrictSquareIso]

/-- **Stacks 08HB, glueing of morphisms, on the small étale sites.** -/
theorem homsGlue_eds :
    RestrictionSquare.HomsGlue (edsRestrictOpen B S hS hsq).mapDerivedCategory
      (edsRestrictEtale B S hS hsq).mapDerivedCategory
      (edsRestrictFst B S hS hsq).mapDerivedCategory
      (edsRestrictSnd B S hS hsq).mapDerivedCategory (edsDerivedRestrictSquareIso B S hS hsq) := by
  intro F E φU φV hφ
  obtain ⟨φ, h₁, h₂⟩ := exists_hom_of_glueData_of_isElementaryDistinguishedSquare B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)) F E (Iso.refl _) (Iso.refl _)
    ((edsDerivedRestrictSquareIso B S hS hsq).app F) (by simp [edsDerivedRestrictSquareIso])
    φU φV (by
      simp only [edsDerivedRestrictSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Iso.app_hom] at hφ ⊢
      simp only [Category.assoc] at hφ ⊢
      rw [← reassoc_of% hφ]
      simp)
  exact ⟨φ, h₁.trans (Category.id_comp _), h₂.trans (Category.id_comp _)⟩

/-- **On the small étale sites the restrictions to the two members of an elementary distinguished
square jointly reflect isomorphisms.** -/
theorem reflectsIso_eds :
    RestrictionSquare.ReflectsIso (edsRestrictOpen B S hS hsq).mapDerivedCategory
      (edsRestrictEtale B S hS hsq).mapDerivedCategory :=
  RestrictionSquare.reflectsIso_of_isZero fun M hU hV =>
    isZero_of_isZero_edsDerivedRestrict B S hS hsq M hU hV

end Small

section Model

variable {W W' Y Y' : AlgebraicSpaces B S hS} (g : W' ⟶ W) (h : Y' ⟶ Y) (j : Y ⟶ W)
  (j' : Y' ⟶ W') (comm : h ≫ j = j' ≫ g)

/-- **The square of derived pullbacks around a commutative square** `h ≫ j = j' ≫ g` on the
models, as an isomorphism `Lj^* ⋙ Lh^* ≅ Lg^* ⋙ Lj'^*`; its morphism is
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackSquare`. -/
def spacesEtaleModelDerivedPullbackSquareIso :=
  spacesEtaleModelDerivedPullbackCompIso B S hS h j ≪≫
    spacesEtaleModelDerivedPullbackCongr B S hS comm ≪≫
      (spacesEtaleModelDerivedPullbackCompIso B S hS j' g).symm

/-- The component at `Z` of `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackSquareIso` is
the composite of the identifications
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq` along `h ≫ j` and along
`j' ≫ g`. -/
theorem spacesEtaleModelDerivedPullbackSquareIso_hom_app
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS W).O))) :
    (spacesEtaleModelDerivedPullbackSquareIso B S hS g h j j' comm).hom.app Z =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS h j comm Z).hom ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS j' g rfl Z).inv :=
  spacesEtaleModelDerivedPullbackSquare_app B S hS g h j j' comm Z

end Model

section Bridge

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]

/-- The derived isomorphism `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` of a
natural isomorphism of exact functors is the derived natural transformation of its morphism. -/
theorem mapDerivedCategoryIsoOfNatIso_hom_eq (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom =
      NatTrans.mapDerivedCategory e.hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    NatTrans.mapDerivedCategory_app_Q]
  rfl

/-- The inverse of the derived isomorphism
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` of a natural isomorphism `e` of
exact functors is the derived natural transformation of `e.inv`. -/
theorem mapDerivedCategoryIsoOfNatIso_inv_eq (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).inv =
      NatTrans.mapDerivedCategory e.inv := by
  refine Iso.inv_ext ?_
  rw [mapDerivedCategoryIsoOfNatIso_hom_eq, ← NatTrans.mapDerivedCategory_comp, e.hom_inv_id,
    NatTrans.mapDerivedCategory_id]

end Bridge

/-- **The comparisons of derived étale pullbacks along equal morphisms agree**, through the
identifications of the pullbacks along equal morphisms. -/
theorem spacesEtaleModelDerivedPullbackOfEtaleTransportIso_congr {X Y : AlgebraicSpaces B S hS}
    {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂) (h₁ : IsEtale B S hS k₁.hom) (h₂ : IsEtale B S hS k₂.hom)
    (F : DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules) :
    (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.map
        ((spacesEtaleModelDerivedPullbackCongr B S hS hk).hom.app F) ≫
      (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS k₂ h₂).hom.app F =
    (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS k₁ h₁).hom.app F ≫
      (NatTrans.mapDerivedCategory (etaleModulePullbackCongr B S hS h₁ h₂ hk).hom).app
        ((spacesEtaleModelModulesEquiv B S hS Y).functor.mapDerivedCategory.obj F) := by
  subst hk
  show (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.map (𝟙 _) ≫ _ =
    _ ≫ (NatTrans.mapDerivedCategory (𝟙 _)).app _
  rw [CategoryTheory.Functor.map_id, NatTrans.mapDerivedCategory_id, Category.id_comp,
    NatTrans.id_app, Category.comp_id]

section ModelSquare

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The square of derived pullbacks of an elementary distinguished square on the models,
`Lj_U^* ⋙ Lpr₁^* ≅ Lj_V^* ⋙ Lpr₂^*`. -/
abbrev spacesEtaleModelEdsSquareIso :=
  spacesEtaleModelDerivedPullbackSquareIso B S hS (edsEtaleHom B S hS hsq) (edsFst B S hS hsq)
    (edsOpenHom B S hS hsq) (edsSnd B S hS hsq) (isPullback_edsInter B S hS hsq).w

/-- The small-étale comparison `D(g^*) ⋙ D(f^*) ≅ D((f ≫ g)^*)` in the form of the hypothesis
`AlgebraicGeometry.Space.SpacesEtaleModelEtaleTransportCoherent`. -/
abbrev smallEtaleDerivedEtalePullbackCompIso {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hfg : IsEtale B S hS (f ≫ g).hom) :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (etaleModulePullback.{u, u} B S hS g hg) (etaleModulePullback.{u, u} B S hS f hf)).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModulePullbackComp B S hS f g hf hg hfg)

/-- The identification `D(pr₁^*) ∘ D(j_U^*) ≅ D((pr₁ ≫ j_U)^*)` of an elementary distinguished
square on the small étale sites is the isomorphism
`AlgebraicGeometry.Space.smallEtaleDerivedEtalePullbackCompIso` for `pr₁` and `j_U`. -/
theorem edsDerivedRestrictCompOpen_eq_smallEtaleDerivedEtalePullbackCompIso :
    edsDerivedRestrictCompOpen B S hS hsq =
      smallEtaleDerivedEtalePullbackCompIso B S hS (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
        (isEtale_edsFst B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) := by
  ext1
  simp only [edsDerivedRestrictCompOpen, smallEtaleDerivedEtalePullbackCompIso, Iso.trans_hom,
    Iso.symm_hom, asIso_hom, mapDerivedCategoryIsoOfNatIso_hom_eq,
    Functor.mapDerivedCategoryComp_eq]
  rfl

/-- The identification of `D(pr₂^*) ∘ D(j_V^*)` with the derived pullback to the intersection of an
elementary distinguished square on the small étale sites is the isomorphism
`AlgebraicGeometry.Space.smallEtaleDerivedEtalePullbackCompIso` for `pr₂` and `j_V`, followed by
the derived identification of the pullbacks along the two equal morphisms to `W`. -/
theorem edsDerivedRestrictCompEtale_eq_smallEtaleDerivedEtalePullbackCompIso :
    edsDerivedRestrictCompEtale B S hS hsq =
      smallEtaleDerivedEtalePullbackCompIso B S hS (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq)
        (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
        (isEtale_comp B S hS (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)) ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (etaleModulePullbackCongr B S hS (isEtale_edsInterHom B S hS hsq)
          (isEtale_comp B S hS (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
          (isPullback_edsInter B S hS hsq).w)).symm := by
  have hc : ∀ {X Y : AlgebraicSpaces B S hS} {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂)
      (h₁ : IsEtale B S hS k₁.hom) (h₂ : IsEtale B S hS k₂.hom),
      (etaleModulePullbackCongr B S hS h₂ h₁ hk.symm).hom =
        (etaleModulePullbackCongr B S hS h₁ h₂ hk).inv := by
    intro X Y k₁ k₂ hk h₁ h₂
    subst hk
    rfl
  ext1
  simp only [edsDerivedRestrictCompEtale, edsRestrictCompEtale,
    smallEtaleDerivedEtalePullbackCompIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, mapDerivedCategoryIsoOfNatIso_hom_eq,
    Functor.mapDerivedCategoryComp_eq, NatTrans.mapDerivedCategory_comp, Category.assoc]
  rw [mapDerivedCategoryIsoOfNatIso_inv_eq]
  congr 3
  exact hc (isPullback_edsInter B S hS hsq).w _ _

variable {B S hS} in
/-- **The comparisons of Stacks 03G1 are compatible with the identifications over the
intersection** of an elementary distinguished square, given their compatibility with
composition. -/
theorem coherent_spacesEtaleModel_eds (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) :
    RestrictionSquare.Coherent
      (eX := (spacesEtaleModelModulesEquiv B S hS W).functor.mapDerivedCategory)
      (spacesEtaleModelEdsSquareIso B S hS hsq) (edsDerivedRestrictSquareIso B S hS hsq)
      (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsFst B S hS hsq)
        (isEtale_edsFst B S hS hsq))
      (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)) := by
  have hVe := isEtale_comp B S hS (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
  have hUe : IsEtale B S hS (edsFst B S hS hsq ≫ edsOpenHom B S hS hsq).hom :=
    isEtale_edsInterHom B S hS hsq
  refine RestrictionSquare.Coherent.of_comp
    (spacesEtaleModelDerivedPullbackCompIso B S hS (edsFst B S hS hsq) (edsOpenHom B S hS hsq))
    (spacesEtaleModelDerivedPullbackCompIso B S hS (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq))
    (spacesEtaleModelDerivedPullbackCongr B S hS (isPullback_edsInter B S hS hsq).w)
    (smallEtaleDerivedEtalePullbackCompIso B S hS (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
      (isEtale_edsFst B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
      hUe)
    (smallEtaleDerivedEtalePullbackCompIso B S hS (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq)
      (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) hVe)
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModulePullbackCongr B S hS hUe hVe
        (isPullback_edsInter B S hS hsq).w))
    (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS
      (edsFst B S hS hsq ≫ edsOpenHom B S hS hsq) hUe)
    (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS
      (edsSnd B S hS hsq ≫ edsEtaleHom B S hS hsq) hVe) (fun _ => rfl) (fun F => ?_)
    (fun F => hT _ _ _ _ _ F) (fun F => hT _ _ _ _ _ F) (fun F => ?_)
  · rw [edsDerivedRestrictSquareIso,
      edsDerivedRestrictCompOpen_eq_smallEtaleDerivedEtalePullbackCompIso,
      edsDerivedRestrictCompEtale_eq_smallEtaleDerivedEtalePullbackCompIso]
    rfl
  · rw [mapDerivedCategoryIsoOfNatIso_hom_eq]
    exact spacesEtaleModelDerivedPullbackOfEtaleTransportIso_congr B S hS _ _ _ F

variable {B S hS} in
/-- **Stacks 08HB, glueing of morphisms, on the models of the spaces-étale sites**, given the
compatibility of the comparisons of Stacks 03G1 with composition. -/
theorem homsGlue_spacesEtaleModel_eds (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) :
    RestrictionSquare.HomsGlue _ _ _ _ (spacesEtaleModelEdsSquareIso B S hS hsq) :=
  (homsGlue_eds B S hS hsq).transport (coherent_spacesEtaleModel_eds hsq hT)

variable {B S hS} in
/-- **Stacks 08HB, glueing of objects, on the models of the spaces-étale sites**, given the
compatibility of the comparisons of Stacks 03G1 with composition. -/
theorem objectsGlue_spacesEtaleModel_eds (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) :
    RestrictionSquare.ObjectsGlue _ _ _ _ (spacesEtaleModelEdsSquareIso B S hS hsq) :=
  (objectsGlue_eds B S hS hsq).transport (coherent_spacesEtaleModel_eds hsq hT)

/-- **On the models of the spaces-étale sites the derived pullbacks to the two members of an
elementary distinguished square jointly reflect isomorphisms.** -/
theorem reflectsIso_spacesEtaleModel_eds :
    RestrictionSquare.ReflectsIso
      (derivedPullback.{u} (spacesEtaleModelHom B S hS (edsOpenHom B S hS hsq)))
      (derivedPullback.{u} (spacesEtaleModelHom B S hS (edsEtaleHom B S hS hsq))) :=
  (reflectsIso_eds B S hS hsq).transport
    (eX := (spacesEtaleModelModulesEquiv B S hS W).functor.mapDerivedCategory)
    (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))

/-- **Perfectness on the models may be checked on the two members of an elementary
distinguished square** (Stacks 08G8 on the small étale sites, transported through Stacks 03G1). -/
theorem isPerfect_of_isPerfect_spacesEtaleModel_eds
    (F : DerivedCategory (spacesEtaleModelRingedTopos B S hS W).Modules)
    (hU : (spacesEtaleModelRingedSite B S hS (edsOpen B S hS hsq)).IsPerfect
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS (edsOpenHom B S hS hsq))).obj F))
    (hV : (spacesEtaleModelRingedSite B S hS (edsEtale B S hS hsq)).IsPerfect
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS (edsEtaleHom B S hS hsq))).obj F)) :
    (spacesEtaleModelRingedSite B S hS W).IsPerfect F := by
  have hs : ∀ {Y : AlgebraicSpaces B S hS} {K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)}
      (e : K ≅ L), (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K →
        (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect L := fun e ⟨E, hE, ⟨i⟩⟩ =>
    ⟨E, hE, ⟨i ≪≫ e⟩⟩
  have hm : ∀ {K L : DerivedCategory (spacesEtaleModelRingedTopos B S hS W).Modules}
      (e : K ≅ L), (spacesEtaleModelRingedSite B S hS W).IsPerfect K →
        (spacesEtaleModelRingedSite B S hS W).IsPerfect L := fun e ⟨E, hE, ⟨i⟩⟩ =>
    ⟨E, hE, ⟨i ≪≫ e⟩⟩
  have hU' := hs
    ((spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).app F)
    (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS _ _ hU)
  have hV' := hs
    ((spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).app F)
    (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS _ _ hV)
  have hW := isPerfect_of_isPerfect_eds B S hS hsq _ hU' hV'
  exact hm ((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
      (spacesEtaleModelModulesEquiv B S hS W)).unitIso.app F).symm
    (isPerfect_spacesEtaleModelModulesEquiv_inverse B S hS _ _ hW)

end ModelSquare

end AlgebraicGeometry.Space

end
