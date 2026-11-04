module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardOverRingEquivalenceAnyModel
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.QuasicoherentConservativeOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.QuasicoherentEquivalenceOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunctionRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.FinitePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelowPlus
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso

/-!
# The twisted inverse image of a finite pseudo-coherent morphism

Let `f : Y ⟶ X` be a finite pseudo-coherent morphism of schemes with `X` quasi-compact and
quasi-separated, let `a : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` be the right adjoint of `Rf_*` of
Stacks, Tag 0A9E, and let `Φ : D_QCoh(𝒪_Y) ⥤ D_QCoh(f₊ 𝒪_Y)` be the equivalence of Tag 0AVW.
Then `Φ ∘ a` and `R ℰom(f₊ 𝒪_Y, -)` agree on `D⁺_QCoh(𝒪_X)` (Stacks, Tag 0AX2).

Following the source, both functors are right adjoint to restriction of scalars
`D⁺_QCoh(f₊ 𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`: the first because `Rf_* = res ∘ Φ` with `Φ` an equivalence,
and `a` preserves `D⁺` (Tag 0A9I); the second by Tag 0BV0 together with the first assertion of
Tag 0AX2. Right adjoints are unique.

The functors `a` and `Φ` live at the locally small model of the derived categories, at which
Brown representability holds, and `R ℰom(f₊ 𝒪_Y, -)` at the standard model; the comparison is
along `Stacks.Injectives.grothendieckModelEquiv`, which is the identity on objects.

## Main results

* `AlgebraicGeometry.derivedPushforwardOverRingCompTwistedInverseImageIso`:
  `Φ ∘ a ≅ R ℰom(f₊ 𝒪_Y, -)` on `D⁺_QCoh(𝒪_X)`.
* `AlgebraicGeometry.derivedHomSheaf_finite_pseudoCoherent`: Stacks, Tag 0AX2.
* `AlgebraicGeometry.ι_map_twistedInverseImageAdjunction_counit_app_eq`: through this
  isomorphism, the counit of `Rf_* ⊣ a` is the counit of `res ⊣ R ℰom(f₊ 𝒪_Y, -)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.DerivedAffinePushforward
  Stacks.AlgebraicGeometry.AffineQcohPushforward

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The comparison of the standard model of `D(f₊ 𝒪_Y)` with the locally small one. -/
abbrev pushforwardRingModelEquiv :=
  Stacks.Injectives.grothendieckModelEquiv.{u}
    (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf))

/-- The comparison of the standard model of `D(𝒪_X)` with the locally small one. -/
abbrev structureSheafModelEquiv (X : Scheme.{u}) :=
  Stacks.Injectives.grothendieckModelEquiv.{u} (SheafOfModules.{u} X.ringCatSheaf)

/-- Restriction of scalars commutes with the comparison of the two models. -/
def derivedRestrictionOfScalarsModelIso :
    derivedRestrictionOfScalars f ⋙ (structureSheafModelEquiv X).functor ≅
      (pushforwardRingModelEquiv f).functor ⋙ (scalarRestriction f).mapDerivedCategory :=
  Stacks.Injectives.mapDerivedCategoryTargetModelIso (SheafOfModules.{u} X.ringCatSheaf)
      (hd₁ := HasDerivedCategory.standard _) (scalarRestriction f) ≪≫
    Stacks.Injectives.mapDerivedCategoryModelIso
      (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf)) (scalarRestriction f)

/-- Restriction of scalars computed at the standard models and compared with the locally small
ones is restriction of scalars at the locally small models. -/
def derivedRestrictionOfScalarsModelCompIso :
    ((pushforwardRingModelEquiv f).inverse ⋙ derivedRestrictionOfScalars f) ⋙
        (structureSheafModelEquiv X).functor ≅ (scalarRestriction f).mapDerivedCategory :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedRestrictionOfScalarsModelIso f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pushforwardRingModelEquiv f).counitIso _ ≪≫
    Functor.leftUnitor _

/-- **Stacks, Tag 0BV0, at the locally small model.** `R ℰom(f₊ 𝒪_Y, -)`, read at the locally
small models, is right adjoint to restriction of scalars. -/
def scalarRestrictionAdjunctionLS :
    (scalarRestriction f).mapDerivedCategory ⊣
      (structureSheafModelEquiv X).inverse ⋙ derivedHomSheaf f ⋙
        (pushforwardRingModelEquiv f).functor :=
  (((pushforwardRingModelEquiv f).symm.toAdjunction.comp
      (derivedRestrictScalarsHomAdjunction f)).comp
      (structureSheafModelEquiv X).toAdjunction).ofNatIsoLeft
    (derivedRestrictionOfScalarsModelCompIso f)

/-- The counit of an adjunction conjugated by equivalences on both sides. -/
private theorem counit_app_ofNatIsoLeft_comp_comp {A A' B B' : Type*} [Category A] [Category A']
    [Category B] [Category B'] (eA : A ≌ A') {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (eB : B ≌ B') {L : A' ⥤ B'} (iso : (eA.symm.functor ⋙ F) ⋙ eB.functor ≅ L) (K : B') :
    (((eA.symm.toAdjunction.comp adj).comp eB.toAdjunction).ofNatIsoLeft iso).counit.app K =
      iso.inv.app _ ≫ eB.functor.map (F.map (eA.unitIso.inv.app (G.obj (eB.inverse.obj K))) ≫
        adj.counit.app (eB.inverse.obj K)) ≫ eB.counitIso.hom.app K := by
  simp

/-- The counit of `scalarRestrictionAdjunctionLS` is the counit of
`derivedRestrictScalarsHomAdjunction` (evaluation at `1`,
`derivedRestrictScalarsHomAdjunction_counit_fac`) carried along the comparison of the models. -/
theorem scalarRestrictionAdjunctionLS_counit_app
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :
    (scalarRestrictionAdjunctionLS f).counit.app K =
      (derivedRestrictionOfScalarsModelCompIso f).inv.app _ ≫
        (structureSheafModelEquiv X).functor.map
          ((derivedRestrictionOfScalars f).map ((pushforwardRingModelEquiv f).unitIso.inv.app
              ((derivedHomSheaf f).obj ((structureSheafModelEquiv X).inverse.obj K))) ≫
            (derivedRestrictScalarsHomAdjunction f).counit.app
              ((structureSheafModelEquiv X).inverse.obj K)) ≫
        (structureSheafModelEquiv X).counitIso.hom.app K :=
  counit_app_ofNatIsoLeft_comp_comp _ _ _ _ K

/-- `D_QCoh(f₊ 𝒪_Y)`, at the locally small model. -/
abbrev pushforwardRingQCoh : Type (u + 1) :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf))).FullSubcategory

/-- Restriction of scalars carries `D_QCoh(f₊ 𝒪_Y)` into `D_QCoh(𝒪_X)`, for `f` affine
(Stacks, Tag 01SB). -/
theorem derivedCategoryB_scalarRestriction_mapDerivedCategory_obj [IsAffineHom f]
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf)))
    (hM : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf)) M) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((scalarRestriction f).mapDerivedCategory.obj M) := fun n =>
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((scalarRestriction f).mapDerivedCategoryHomologyIso n).app M).symm
    ((Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff f _).2 (hM n))

/-- Restriction of scalars `D_QCoh(f₊ 𝒪_Y) ⥤ D_QCoh(𝒪_X)`, for `f` affine. -/
def quasicoherentScalarRestriction [IsAffineHom f] :
    pushforwardRingQCoh f ⥤ Stacks.Duality.quasiCoherentDerivedCategory X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (scalarRestriction f).mapDerivedCategory)
    fun M => derivedCategoryB_scalarRestriction_mapDerivedCategory_obj f M.obj M.property

section QCoh

variable [IsAffineHom f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]

/-- The twisted inverse image `a` of Stacks, Tag 0A9E, for `f`. -/
abbrev twistedInverseImageQcqs :
    Stacks.Duality.quasiCoherentDerivedCategory X ⥤ Stacks.Duality.quasiCoherentDerivedCategory Y :=
  Stacks.Duality.twistedInverseImage f
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)

/-- The equivalence `Φ : D_QCoh(𝒪_Y) ≌ D_QCoh(f₊ 𝒪_Y)` of Stacks, Tag 0AVW. -/
abbrev derivedQuasicoherentPushforwardOverRingEquivalence :
    Stacks.Duality.quasiCoherentDerivedCategory Y ≌ pushforwardRingQCoh f :=
  haveI := isEquivalence_derivedQuasicoherentPushforwardOverRing_anyModel.{u} f
  (derivedQuasicoherentPushforwardOverRing.{u} f).asEquivalence

/-- `Φ⁻¹` followed by `Rf_*` is restriction of scalars on `D_QCoh(f₊ 𝒪_Y)`: `Rf_* = res ∘ Φ`
(Stacks, Tag 0AVW). -/
def inverseCompDerivedPushforwardIso :
    (derivedQuasicoherentPushforwardOverRingEquivalence f).inverse ⋙
        Stacks.Duality.quasiCoherentDerivedPushforward f
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f) ≅
      quasicoherentScalarRestriction f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedQuasicoherentPushforwardOverRingEquivalence f).inverse
        (Functor.isoWhiskerLeft (ObjectProperty.ι _)
          (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f)) ≪≫
      id (α := (derivedQuasicoherentPushforwardOverRingEquivalence f).inverse ⋙
          ObjectProperty.ι _ ⋙ derivedPushforwardOverRing.{u} f ⋙
            (scalarRestriction f).mapDerivedCategory ≅
        ((derivedQuasicoherentPushforwardOverRingEquivalence f).inverse ⋙
          (derivedQuasicoherentPushforwardOverRingEquivalence f).functor) ⋙
            ObjectProperty.ι _ ⋙ (scalarRestriction f).mapDerivedCategory) (Iso.refl _) ≪≫
      Functor.isoWhiskerRight (derivedQuasicoherentPushforwardOverRingEquivalence f).counitIso _ ≪≫
      Functor.leftUnitor _)

/-- `Φ ∘ a` is right adjoint to restriction of scalars `D_QCoh(f₊ 𝒪_Y) ⥤ D_QCoh(𝒪_X)`. -/
def quasicoherentScalarRestrictionAdjunction :
    quasicoherentScalarRestriction f ⊣
      twistedInverseImageQcqs f ⋙ (derivedQuasicoherentPushforwardOverRingEquivalence f).functor :=
  ((derivedQuasicoherentPushforwardOverRingEquivalence f).symm.toAdjunction.comp
      (Stacks.Duality.twistedInverseImageAdjunction f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f))).ofNatIsoLeft
    (inverseCompDerivedPushforwardIso f)

omit [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The components of `inverseCompDerivedPushforwardIso`: the factorisation `Rf_* = res ∘ Φ`
followed by the counit of `Φ`. -/
theorem ι_map_inverseCompDerivedPushforwardIso_hom_app (M : pushforwardRingQCoh f) :
    (ObjectProperty.ι _).map ((inverseCompDerivedPushforwardIso f).hom.app M) =
      (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).inverse.obj M).obj ≫
        (scalarRestriction f).mapDerivedCategory.map ((ObjectProperty.ι _).map
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).counitIso.hom.app M)) := by
  have hp : ∀ {F G : pushforwardRingQCoh f ⥤ Stacks.Duality.quasiCoherentDerivedCategory X}
      (τ : F ⋙ ObjectProperty.ι _ ⟶ G ⋙ ObjectProperty.ι _) (M : pushforwardRingQCoh f),
      (ObjectProperty.ι _).map ((((ObjectProperty.fullyFaithfulι _).whiskeringRight
        (pushforwardRingQCoh f)).preimage τ).app M) = τ.app M := fun τ M =>
    NatTrans.congr_app (((ObjectProperty.fullyFaithfulι _).whiskeringRight
      (pushforwardRingQCoh f)).map_preimage τ) M
  refine (hp _ M).trans ?_
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp]
  congr 1
  exact (Category.id_comp _).trans (Category.comp_id _)

omit [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- `Rf_*` of the unit of `Φ`, followed by `inverseCompDerivedPushforwardIso`, is the
factorisation `Rf_* = res ∘ Φ`. -/
theorem ι_map_unit_comp_inverseCompDerivedPushforwardIso_hom_app
    (Z : Stacks.Duality.quasiCoherentDerivedCategory Y) :
    (ObjectProperty.ι _).map ((Stacks.Duality.quasiCoherentDerivedPushforward f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).unitIso.hom.app Z)) ≫
      (ObjectProperty.ι _).map ((inverseCompDerivedPushforwardIso f).hom.app
        ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj Z)) =
      (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app Z.obj := by
  have h : (ObjectProperty.ι _).map ((Stacks.Duality.quasiCoherentDerivedPushforward f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).unitIso.hom.app Z)) ≫
      (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
        ((derivedQuasicoherentPushforwardOverRingEquivalence f).inverse.obj
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj Z)).obj =
      (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app Z.obj ≫
        (scalarRestriction f).mapDerivedCategory.map ((derivedPushforwardOverRing.{u} f).map
          ((ObjectProperty.ι _).map
            ((derivedQuasicoherentPushforwardOverRingEquivalence f).unitIso.hom.app Z))) :=
    (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.naturality
      ((ObjectProperty.ι _).map
        ((derivedQuasicoherentPushforwardOverRingEquivalence f).unitIso.hom.app Z))
  have ht : (derivedPushforwardOverRing.{u} f).map ((ObjectProperty.ι _).map
        ((derivedQuasicoherentPushforwardOverRingEquivalence f).unitIso.hom.app Z)) ≫
      (ObjectProperty.ι _).map
        ((derivedQuasicoherentPushforwardOverRingEquivalence f).counitIso.hom.app
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj Z)) = 𝟙 _ :=
    ((ObjectProperty.ι _).map_comp _ _).symm.trans
      ((congrArg (ObjectProperty.ι _).map
        ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor_unit_comp Z)).trans
        ((ObjectProperty.ι _).map_id _))
  rw [ι_map_inverseCompDerivedPushforwardIso_hom_app]
  refine (Category.assoc _ _ _).symm.trans ((eq_whisker h _).trans
    ((Category.assoc _ _ _).trans ?_))
  refine (congrArg ((derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app Z.obj ≫ ·)
    (((scalarRestriction f).mapDerivedCategory.map_comp _ _).symm.trans
      ((congrArg (scalarRestriction f).mapDerivedCategory.map ht).trans
        ((scalarRestriction f).mapDerivedCategory.map_id _)))).trans (Category.comp_id _)

/-- The counit of `quasicoherentScalarRestrictionAdjunction`: the inverse of
`inverseCompDerivedPushforwardIso`, `Rf_*` of the inverse unit of `Φ`, and the counit of
`Rf_* ⊣ a`. -/
theorem quasicoherentScalarRestrictionAdjunction_counit_app
    (M : Stacks.Duality.quasiCoherentDerivedCategory X) :
    (quasicoherentScalarRestrictionAdjunction f).counit.app M =
      (inverseCompDerivedPushforwardIso f).inv.app
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj
            ((twistedInverseImageQcqs f).obj M)) ≫
        (Stacks.Duality.quasiCoherentDerivedPushforward f
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
            ((derivedQuasicoherentPushforwardOverRingEquivalence f).unitIso.inv.app
              ((twistedInverseImageQcqs f).obj M)) ≫
        (Stacks.Duality.twistedInverseImageAdjunction f
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app M := by
  simp only [quasicoherentScalarRestrictionAdjunction, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app]
  rfl

/-- The counit of `Rf_* ⊣ a` on `D_QCoh`, through the factorisation `Rf_* = res ∘ Φ`, is the counit
of `quasicoherentScalarRestrictionAdjunction`. -/
theorem ι_map_twistedInverseImageAdjunction_counit_app
    (M : Stacks.Duality.quasiCoherentDerivedCategory X) :
    (ObjectProperty.ι _).map ((Stacks.Duality.twistedInverseImageAdjunction f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app M) =
      (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
          ((twistedInverseImageQcqs f).obj M).obj ≫
        (ObjectProperty.ι _).map ((quasicoherentScalarRestrictionAdjunction f).counit.app M) := by
  have h : (Stacks.Duality.twistedInverseImageAdjunction f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app M =
      ((Stacks.Duality.quasiCoherentDerivedPushforward f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).unitIso.hom.app
            ((twistedInverseImageQcqs f).obj M)) ≫
        (inverseCompDerivedPushforwardIso f).hom.app
          ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj
            ((twistedInverseImageQcqs f).obj M))) ≫
        (quasicoherentScalarRestrictionAdjunction f).counit.app M := by
    rw [quasicoherentScalarRestrictionAdjunction_counit_app]
    simp [← Functor.map_comp_assoc]
  rw [h, Functor.map_comp, Functor.map_comp,
    ι_map_unit_comp_inverseCompDerivedPushforwardIso_hom_app]
  rfl

end QCoh

/-- `D⁺_QCoh(f₊ 𝒪_Y)`, at the locally small model. -/
abbrev pushforwardRingQCohPlus : Type (u + 1) :=
  (DerivedCategoryB.derivedCategoryBPlus
    (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf))).FullSubcategory

/-- Restriction of scalars preserves bounded-below objects: it is exact. -/
theorem isBoundedBelow_scalarRestriction_mapDerivedCategory_obj
    (M : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf)))
    (hM : DerivedCategoryB.IsBoundedBelow M) :
    DerivedCategoryB.IsBoundedBelow ((scalarRestriction f).mapDerivedCategory.obj M) := by
  obtain ⟨n₀, hn₀⟩ := hM
  exact ⟨n₀, fun n hn => ((scalarRestriction f).map_isZero (hn₀ n hn)).of_iso
    (((scalarRestriction f).mapDerivedCategoryHomologyIso n).app M)⟩

/-- Restriction of scalars `D⁺_QCoh(f₊ 𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`, for `f` affine. -/
def quasicoherentPlusScalarRestriction [IsAffineHom f] :
    pushforwardRingQCohPlus f ⥤ Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel X :=
  ObjectProperty.lift _
    (ObjectProperty.ιOfLE (fun _ h => h.2) ⋙ quasicoherentScalarRestriction f)
    fun M => isBoundedBelow_scalarRestriction_mapDerivedCategory_obj f M.obj M.property.1

section Plus

variable [IsFinite f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]

/-- `Φ ∘ a` carries `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(f₊ 𝒪_Y)`: `a` preserves `D⁺` (Stacks,
Tag 0A9I) and `Φ` kills the degrees where the cohomology vanishes. -/
theorem derivedCategoryBPlus_twistedInverseImageQcqs_obj
    (K : Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel X) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf))
      ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj
        ((twistedInverseImageQcqs f).obj K.obj)).obj := by
  refine ⟨?_, ((derivedQuasicoherentPushforwardOverRingEquivalence f).functor.obj
    ((twistedInverseImageQcqs f).obj K.obj)).property⟩
  obtain ⟨n₀, hn₀⟩ := Stacks.Duality.isBoundedBelow_twistedInverseImage_obj f K.obj K.property
  exact ⟨n₀, fun n hn =>
    (isZero_homologyFunctor_derivedPushforwardOverRing_iff_of_isAffineHom.{u} f _
      ((twistedInverseImageQcqs f).obj K.obj).property n).2 (hn₀ n hn)⟩

/-- `Φ ∘ a : D⁺_QCoh(𝒪_X) ⥤ D⁺_QCoh(f₊ 𝒪_Y)`. -/
def twistedInverseImagePlus :
    Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel X ⥤ pushforwardRingQCohPlus f :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ twistedInverseImageQcqs f ⋙
      (derivedQuasicoherentPushforwardOverRingEquivalence f).functor ⋙ ObjectProperty.ι _)
    fun K => derivedCategoryBPlus_twistedInverseImageQcqs_obj f K

/-- `Φ ∘ a` is right adjoint to restriction of scalars `D⁺_QCoh(f₊ 𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`. -/
def twistedInverseImagePlusAdjunction :
    quasicoherentPlusScalarRestriction f ⊣ twistedInverseImagePlus f :=
  (quasicoherentScalarRestrictionAdjunction f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

end Plus

section HomSheaf

variable [IsFinite f] [PseudoCoherent f]

/-- Membership in `D⁺_B` is unchanged by the comparison of the standard and the locally small
models, which commutes with cohomology. -/
private theorem derivedCategoryBPlus_modelEquiv_functor_obj_iff {C : Type (u + 1)} [Category.{u} C]
    [Abelian C] [IsGrothendieckAbelian.{u} C] (B : ObjectProperty C) [B.IsClosedUnderIsomorphisms]
    (E : @DerivedCategory C _ _ (HasDerivedCategory.standard C)) :
    @DerivedCategoryB.derivedCategoryBPlus C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) B
        ((Stacks.Injectives.grothendieckModelEquiv.{u} C).functor.obj E) ↔
      @DerivedCategoryB.derivedCategoryBPlus C _ _ (HasDerivedCategory.standard C) B E :=
  and_congr (exists_congr fun _ => forall_congr' fun n => imp_congr_right fun _ =>
      ((Stacks.Duality.homologyFunctorModelIso C n).app E).isZero_iff)
    (forall_congr' fun n =>
      B.prop_iff_of_iso ((Stacks.Duality.homologyFunctorModelIso C n).app E))

/-- `R ℰom(f₊ 𝒪_Y, -)`, read at the locally small models, carries `D⁺_QCoh(𝒪_X)` into
`D⁺_QCoh(f₊ 𝒪_Y)`: the first assertion of Stacks, Tag 0AX2, and the comparison of the models is
the identity on objects and commutes with cohomology. -/
theorem derivedCategoryBPlus_derivedHomSheafLS_obj
    (K : Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel X) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf))
      (((structureSheafModelEquiv X).inverse ⋙ derivedHomSheaf f ⋙
        (pushforwardRingModelEquiv f).functor).obj K.obj.obj) := by
  have hK := derivedCategoryBPlus_derivedHomSheaf_obj f
    ((structureSheafModelEquiv X).inverse.obj K.obj.obj)
    ((derivedCategoryBPlus_modelEquiv_functor_obj_iff _ _).1 ⟨K.property, K.obj.property⟩)
  exact (derivedCategoryBPlus_modelEquiv_functor_obj_iff _ _).2 hK

/-- `R ℰom(f₊ 𝒪_Y, -) : D⁺_QCoh(𝒪_X) ⥤ D⁺_QCoh(f₊ 𝒪_Y)`, at the locally small models. -/
def derivedHomSheafPlus :
    Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel X ⥤ pushforwardRingQCohPlus f :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (structureSheafModelEquiv X).inverse ⋙
      derivedHomSheaf f ⋙ (pushforwardRingModelEquiv f).functor)
    fun K => derivedCategoryBPlus_derivedHomSheafLS_obj f K

/-- **Stacks, Tag 0BV0, on `D⁺_QCoh`.** `R ℰom(f₊ 𝒪_Y, -)` is right adjoint to restriction of
scalars `D⁺_QCoh(f₊ 𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`. -/
def derivedHomSheafPlusAdjunction :
    quasicoherentPlusScalarRestriction f ⊣ derivedHomSheafPlus f :=
  (scalarRestrictionAdjunctionLS f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _)
    ((ObjectProperty.fullyFaithfulι (fun K : Stacks.Duality.quasiCoherentDerivedCategory X =>
        DerivedCategoryB.IsBoundedBelow K.obj)).comp
      (ObjectProperty.fullyFaithfulι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))))
    (Iso.refl _) (Iso.refl _)

end HomSheaf

section Comparison

variable [IsFinite f] [PseudoCoherent f] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **`Φ ∘ a = R ℰom(f₊ 𝒪_Y, -)` on `D⁺_QCoh(𝒪_X)`** (Stacks, Tag 0AX2): both are right adjoint to
restriction of scalars `D⁺_QCoh(f₊ 𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`. Here `a` is the right adjoint of
Stacks, Tag 0A9E and `Φ` the equivalence of Tag 0AVW, at the locally small models, and
`R ℰom(f₊ 𝒪_Y, -)` is compared with them along the comparison of the models. -/
def derivedPushforwardOverRingCompTwistedInverseImageIso :
    ObjectProperty.ι (fun K : Stacks.Duality.quasiCoherentDerivedCategory X =>
        DerivedCategoryB.IsBoundedBelow K.obj) ⋙ twistedInverseImageQcqs f ⋙
        (derivedQuasicoherentPushforwardOverRingEquivalence f).functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι (fun K : Stacks.Duality.quasiCoherentDerivedCategory X =>
          DerivedCategoryB.IsBoundedBelow K.obj) ⋙ ObjectProperty.ι _ ⋙
        (structureSheafModelEquiv X).inverse ⋙ derivedHomSheaf f ⋙
          (pushforwardRingModelEquiv f).functor :=
  Functor.isoWhiskerRight ((twistedInverseImagePlusAdjunction f).rightAdjointUniq
    (derivedHomSheafPlusAdjunction f)) (ObjectProperty.ι _)

/-- **The counit of `Rf_* ⊣ a` through `Φ ∘ a ≅ R ℰom(f₊ 𝒪_Y, -)`.** On `D⁺_QCoh(𝒪_X)`, the
counit of `Rf_* ⊣ a` is the factorisation `Rf_* = res ∘ Φ`, followed by restriction of scalars of
the isomorphism of Stacks, Tag 0AX2, and the counit of `res ⊣ R ℰom(f₊ 𝒪_Y, -)` (Tag 0BV0). -/
theorem ι_map_twistedInverseImageAdjunction_counit_app_eq
    (K : Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel X) :
    (ObjectProperty.ι _).map ((Stacks.Duality.twistedInverseImageAdjunction f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app K.obj) =
      (derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
          ((twistedInverseImageQcqs f).obj K.obj).obj ≫
        (scalarRestriction f).mapDerivedCategory.map
          ((derivedPushforwardOverRingCompTwistedInverseImageIso f).hom.app K) ≫
        (scalarRestrictionAdjunctionLS f).counit.app K.obj.obj := by
  have k1 := (quasicoherentScalarRestrictionAdjunction f).map_restrictFullyFaithful_counit_app
    (L := quasicoherentPlusScalarRestriction f) (R := twistedInverseImagePlus f)
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _)
    (Iso.refl _) K
  have k2 := (scalarRestrictionAdjunctionLS f).map_restrictFullyFaithful_counit_app
    (L := quasicoherentPlusScalarRestriction f) (R := derivedHomSheafPlus f)
    (ObjectProperty.fullyFaithfulι _)
    ((ObjectProperty.fullyFaithfulι (fun K : Stacks.Duality.quasiCoherentDerivedCategory X =>
        DerivedCategoryB.IsBoundedBelow K.obj)).comp
      (ObjectProperty.fullyFaithfulι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))))
    (Iso.refl _) (Iso.refl _) K
  have key := (twistedInverseImagePlusAdjunction f).rightAdjointUniq_hom_app_counit
    (derivedHomSheafPlusAdjunction f) K
  have k1' : (ObjectProperty.ι _).map ((twistedInverseImagePlusAdjunction f).counit.app K) =
      (quasicoherentScalarRestrictionAdjunction f).counit.app K.obj :=
    k1.trans ((Category.id_comp _).trans ((eq_whisker
      ((quasicoherentScalarRestriction f).map_id _) _).trans (Category.id_comp _)))
  have k2' : (ObjectProperty.ι _).map ((ObjectProperty.ι _).map
      ((derivedHomSheafPlusAdjunction f).counit.app K)) =
      (scalarRestrictionAdjunctionLS f).counit.app K.obj.obj :=
    k2.trans ((Category.id_comp _).trans ((eq_whisker
      ((scalarRestriction f).mapDerivedCategory.map_id _) _).trans (Category.id_comp _)))
  rw [ι_map_twistedInverseImageAdjunction_counit_app, ← k1', ← key, ← k2', Functor.map_comp]
  exact congrArg ((derivedPushforwardOverRingCompRestrictScalarsIso.{u} f).hom.app
    ((twistedInverseImageQcqs f).obj K.obj).obj ≫ ·) ((ObjectProperty.ι _).map_comp _ _)

end Comparison

/-- **Stacks, Tag 0AX2.** Let `f : Y ⟶ X` be a finite pseudo-coherent morphism of schemes. The
functor `R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)` maps `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(f₊ 𝒪_Y)`.
If `X` is quasi-compact and quasi-separated, then on `D⁺_QCoh(𝒪_X)` the functor `Φ ∘ a` agrees
with `R ℰom(f₊ 𝒪_Y, -)`, where `a` is the right adjoint of Stacks, Tag 0A9E for `f` and `Φ` is
the equivalence of Stacks, Tag 0AVW. The functors `a` and `Φ` are taken at the locally small
models and `R ℰom(f₊ 𝒪_Y, -)` at the standard one, compared along the identity-on-objects
equivalence of the two models. -/
@[stacks 0AX2]
theorem derivedHomSheaf_finite_pseudoCoherent [IsFinite f] [PseudoCoherent f] :
    (∀ K : @DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) _ _
          (HasDerivedCategory.standard _),
        @DerivedCategoryB.derivedCategoryBPlus _ _ _ (HasDerivedCategory.standard _)
            (SheafOfModules.isQuasicoherent X.ringCatSheaf) K →
          @DerivedCategoryB.derivedCategoryBPlus _ _ _ (HasDerivedCategory.standard _)
            (SheafOfModules.isQuasicoherent (pushforwardRingCatSheaf f))
            ((derivedHomSheaf f).obj K)) ∧
      ∀ [CompactSpace X] [QuasiSeparatedSpace X],
        haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
        haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated f
        Nonempty (ObjectProperty.ι (fun K : Stacks.Duality.quasiCoherentDerivedCategory X =>
              DerivedCategoryB.IsBoundedBelow K.obj) ⋙ twistedInverseImageQcqs f ⋙
            (derivedQuasicoherentPushforwardOverRingEquivalence f).functor ⋙
              ObjectProperty.ι _ ≅
          ObjectProperty.ι (fun K : Stacks.Duality.quasiCoherentDerivedCategory X =>
              DerivedCategoryB.IsBoundedBelow K.obj) ⋙ ObjectProperty.ι _ ⋙
            (structureSheafModelEquiv X).inverse ⋙ derivedHomSheaf f ⋙
              (pushforwardRingModelEquiv f).functor) :=
  ⟨derivedCategoryBPlus_derivedHomSheaf_obj f, fun {_ _} =>
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
    have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated f
    ⟨derivedPushforwardOverRingCompTwistedInverseImageIso f⟩⟩

end AlgebraicGeometry
