module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonExactPairing
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapTransport
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackBraided

/-!
# The projection formula for the monoidal structure of `Lf^*` on `D_QCoh`

For `f : X ⟶ Y` quasi-compact and quasi-separated, the projection-formula map
`K ⊗ᴸ Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ E)` of `Stacks.Duality.projectionFormulaMap`, built from the tensor
comparison `Stacks.Duality.quasiCoherentDerivedPullbackTensorIso` of the monoidal structure of
`Lf^*` on `D_QCoh`, is reduced to [Stacks, Tag 08EU] at the standard model
(`Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh`) in three steps:

* restriction from `D_QCoh` to `D(𝒪)` together with the braidings, which turns the map into the
  projection-formula map `Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)` of the ambient adjunction built from the
  oplax tensorator of `Lf^*` (`isIso_projectionFormulaMap_iff`, using that `Lf^*` is braided,
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal_δ_braiding`);
* transport from the standard to the locally small model through the comparisons of `Lf^*`,
  `Rf_*` and `⊗ᴸ` of the two models (`isIso_of_isIso_standard`, needs the tensorator to be the
  transported comparison of [Stacks, Tag 079U]);
* [Stacks, Tag 08EU] at the standard model.

The one input taken as an explicit hypothesis is `hB3`, the identification of the oplax tensorator
at the locally small model with the transported comparison of [Stacks, Tag 079U]
(`Stacks.Duality.derivedPullbackCanonicalMonoidal_δ_model`).

## Main results

* `Stacks.Duality.ProjectionFormulaMonoidal.ι_map_projectionFormulaMap`,
  `Stacks.Duality.ProjectionFormulaMonoidal.modelFunctor_map_adjunctionTensorMap` — the first two
  steps, as identities of morphisms.
* `Stacks.Duality.ProjectionFormulaMonoidal.isIso_projectionFormulaMap_of_comparison`
* `Stacks.Duality.ProjectionFormulaMonoidal.isIso_projectionMap_of_comparison`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality.ProjectionFormulaMonoidal

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The oplax tensorator of `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)`, at the locally small model, as a
transformation `Lf^*(- ⊗ᴸ -) ⟶ Lf^*(-) ⊗ᴸ Lf^*(-)` of functors on `D(𝒪_Y) × D(𝒪_Y)`. -/
def tensorComparison :
    @tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) ⋙ derivedPullback f ⟶
      (derivedPullback f).prod (derivedPullback f) ⋙
        @tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := Scheme.Modules.canonicalDerivedMonoidal Y
  letI : (derivedPullback f).Monoidal :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f.toLRSHom.toShHom
  (Functor.Monoidal.μNatIso (derivedPullback f)).inv

/-- The component of `tensorComparison f` at `(P, Q)` is the oplax tensorator
`δ : Lf^*(P ⊗ᴸ Q) ⟶ Lf^*P ⊗ᴸ Lf^*Q`. -/
theorem tensorComparison_app (P Q : DerivedCategory Y.Modules) :
    (tensorComparison f).app (P, Q) =
      letI := Scheme.Modules.canonicalDerivedMonoidal X
      letI := Scheme.Modules.canonicalDerivedMonoidal Y
      letI : (derivedPullback f).Monoidal :=
        Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f.toLRSHom.toShHom
      Functor.OplaxMonoidal.δ (derivedPullback f) P Q :=
  rfl

/-- The braiding of `D(𝒪_Z)`, as an isomorphism `ι P ⊗ᴸ ι Q ≅ ι (Q ⊗ᴸ P)` of functors on
`D_QCoh(𝒪_Z) × D_QCoh(𝒪_Z)`. -/
def swapIso (Z : Scheme.{u}) :
    (ObjectProperty.ι _).prod (ObjectProperty.ι _) ⋙
        @tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Z) ≅
      quasiCoherentDerivedTensorSwap Z ⋙ ObjectProperty.ι _ :=
  letI := Scheme.Modules.canonicalDerivedMonoidal Z
  letI : SymmetricCategory (DerivedCategory Z.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Z.sheaf
  NatIso.ofComponents (fun PQ => β_ PQ.1.obj PQ.2.obj) (by
    rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨p, q⟩
    have e : (quasiCoherentDerivedTensorSwap Z ⋙ ObjectProperty.ι _).map (p, q) =
        ((derivedTensor Z).map q.hom).app P.obj ≫ ((derivedTensor Z).obj Q'.obj).map p.hom := by
      change (((quasiCoherentDerivedTensor Z).map q).app P ≫
        ((quasiCoherentDerivedTensor Z).obj Q').map p).hom = _
      rw [ObjectProperty.FullSubcategory.comp_hom, quasiCoherentDerivedTensor_map_app_hom,
        quasiCoherentDerivedTensor_obj_map_hom]
      rfl
    rw [e]
    change (p.hom ⊗ₘ q.hom) ≫ (β_ P'.obj Q'.obj).hom = (β_ P.obj Q.obj).hom ≫ _
    refine (BraidedCategory.braiding_naturality p.hom q.hom).trans ?_
    rw [MonoidalCategory.tensorHom_def]
    rfl)

/-- The comparison `quasiCoherentDerivedPullbackTensorIso` on `D_QCoh` is `tensorComparison`, read
through the braidings. -/
private lemma tensorIso_hom_comm
    (P Q : quasiCoherentDerivedCategory Y) :
    (quasiCoherentDerivedPullbackCompιIso f
          (isQuasicoherent_homology_derivedPullback' f)).symm.hom.app
          ((quasiCoherentDerivedTensorSwap Y).obj (P, Q)) ≫
        (ObjectProperty.ι _).map ((quasiCoherentDerivedPullbackTensorIso f).hom.app (P, Q)) =
      (derivedPullback f).map ((swapIso Y).inv.app (P, Q)) ≫
        (tensorComparison f).app (P.obj, Q.obj) ≫
          (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
            ((quasiCoherentDerivedPullbackCompιIso f
                (isQuasicoherent_homology_derivedPullback' f)).symm.hom.app P ×ₘ
              (quasiCoherentDerivedPullbackCompιIso f
                (isQuasicoherent_homology_derivedPullback' f)).symm.hom.app Q) ≫
            (swapIso X).hom.app ((quasiCoherentDerivedPullback' f).obj P,
              (quasiCoherentDerivedPullback' f).obj Q) := by
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let := Scheme.Modules.canonicalDerivedMonoidal Y
  let : SymmetricCategory (DerivedCategory X.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf
  let : SymmetricCategory (DerivedCategory Y.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.sheaf
  let : (derivedPullback f).Monoidal :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f.toLRSHom.toShHom
  have hb : Functor.OplaxMonoidal.δ (derivedPullback f) P.obj Q.obj ≫
        (β_ ((derivedPullback f).obj P.obj) ((derivedPullback f).obj Q.obj)).hom =
      (derivedPullback f).map (β_ P.obj Q.obj).hom ≫
        Functor.OplaxMonoidal.δ (derivedPullback f) Q.obj P.obj :=
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal_δ_braiding
      f.toLRSHom.toShHom P.obj Q.obj).symm
  refine Eq.trans (?_ : _ = Functor.OplaxMonoidal.δ (derivedPullback f) Q.obj P.obj) ?_
  · rw [quasiCoherentDerivedPullbackTensorIso_hom_app]
    have ha : (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) Q P).hom =
        (derivedPullback f).map (𝟙 _) ≫ Functor.OplaxMonoidal.δ (derivedPullback f) Q.obj P.obj :=
      rfl
    have hb1 : (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P).hom = 𝟙 _ := rfl
    have hb2 : (((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
        ((quasiCoherentDerivedPullback' f).obj Q)).app
          ((quasiCoherentDerivedPullback' f).obj P)).hom =
          𝟙 _ := rfl
    show 𝟙 _ ≫ ((derivedPullback f).map
        (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P).hom ≫
      (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) Q P).hom ≫
      (((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
        ((quasiCoherentDerivedPullback' f).obj Q)).app
          ((quasiCoherentDerivedPullback' f).obj P)).hom) = _
    rw [ha, hb1, hb2]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    show (derivedPullback f).map (𝟙 (Q.obj ⊗ P.obj)) ≫
      Functor.OplaxMonoidal.δ (derivedPullback f) Q.obj P.obj ≫
        𝟙 ((derivedPullback f).obj Q.obj ⊗ (derivedPullback f).obj P.obj) = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · show _ = (derivedPullback f).map (β_ P.obj Q.obj).inv ≫
      Functor.OplaxMonoidal.δ (derivedPullback f) P.obj Q.obj ≫ (𝟙 _ ⊗ₘ 𝟙 _) ≫ (β_ _ _).hom
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp, hb, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The projection-formula map on `D_QCoh` is the projection-formula map of `D(𝒪)`**, read
through the braidings: the inclusion of `D_QCoh` carries the map `K ⊗ᴸ Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ E)`
built from `quasiCoherentDerivedPullbackTensorIso` to the map `Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)` of
the ambient adjunction `Lf^* ⊣ Rf_*` built from the oplax tensorator of `Lf^*`, conjugated by the
braidings and the inclusions. -/
theorem ι_map_projectionFormulaMap
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    (ObjectProperty.ι _).map
        (projectionFormulaMap f hpush (quasiCoherentDerivedPullbackTensorIso f).hom E K) =
      (swapIso Y).inv.app ((quasiCoherentDerivedPushforward f hpush).obj E, K) ≫
        (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
          ((DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm.inv.app E ×ₘ
            𝟙 ((ObjectProperty.ι _).obj K)) ≫
        adjunctionTensorMap (derivedAdjunction f)
          (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y))
          (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)) (tensorComparison f)
          ((ObjectProperty.ι _).obj E) ((ObjectProperty.ι _).obj K) ≫
        (derivedPushforward f).map ((@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
            (𝟙 ((ObjectProperty.ι _).obj E) ×ₘ (quasiCoherentDerivedPullbackCompιIso f
              (isQuasicoherent_homology_derivedPullback' f)).symm.hom.app K) ≫
          (swapIso X).hom.app (E, (quasiCoherentDerivedPullback' f).obj K)) ≫
        (DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm.hom.app
          ((quasiCoherentDerivedTensorSwap X).obj (E, (quasiCoherentDerivedPullback' f).obj K)) :=
  map_adjunctionTensorMap_of_counit_comm
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
    (derivedAdjunction f)
    (quasiCoherentDerivedPullbackCompιIso f (isQuasicoherent_homology_derivedPullback' f)).symm
    (DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm
    (swapIso Y) (swapIso X) (quasiCoherentDerivedPullbackTensorIso f).hom (tensorComparison f)
    (counit_comm_quasiCoherentDerivedAdjunction f _ hpush) (tensorIso_hom_comm f) E K

/-- **The projection-formula map on `D_QCoh` is the projection-formula map of `D(𝒪)`**, read
through the braidings: the map `K ⊗ᴸ Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ E)` built from
`quasiCoherentDerivedPullbackTensorIso` is invertible exactly when the map
`Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)` of the ambient adjunction `Lf^* ⊣ Rf_*`, built from the oplax
tensorator of `Lf^*`, is. -/
theorem isIso_projectionFormulaMap_iff
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    IsIso (projectionFormulaMap f hpush
        (quasiCoherentDerivedPullbackTensorIso f).hom E K) ↔
      IsIso (adjunctionTensorMap (derivedAdjunction f)
        (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y))
        (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)) (tensorComparison f)
        E.obj K.obj) := by
  refine Iff.trans ?_ (isIso_map_adjunctionTensorMap_iff_of_counit_comm
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
    (derivedAdjunction f)
    (quasiCoherentDerivedPullbackCompιIso f (isQuasicoherent_homology_derivedPullback' f)).symm
    (DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm
    (swapIso Y) (swapIso X) (quasiCoherentDerivedPullbackTensorIso f).hom (tensorComparison f)
    (counit_comm_quasiCoherentDerivedAdjunction f _ hpush) (tensorIso_hom_comm f) E K)
  exact ⟨fun h => @Functor.map_isIso _ _ _ _ _ _ _ _ h,
    fun h => @isIso_of_reflects_iso _ _ _ _ _ _ _ (ObjectProperty.ι _) h _⟩

/-! ### The standard model -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- The derived tensor product of `D(𝒪_Z)` at the standard model. -/
abbrev standardTensorBifunctor (Z : Scheme.{u}) :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf

/-- The derived tensor product of `D(𝒪_Z)` at the standard model, uncurried. -/
abbrev standardTensor (Z : Scheme.{u}) := Functor.uncurry.obj (standardTensorBifunctor Z)

/-- `Lf^*` at the standard model. -/
abbrev standardPullback :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom

/-- The adjunction `Lf^* ⊣ Rf_*` at the standard model. -/
abbrev standardAdjunction :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f.toLRSHom.toShHom

/-- The comparison of [Stacks, Tag 079U] at the standard model. -/
abbrev standardComparison :=
  Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f.toLRSHom.toShHom

/-- [Stacks, Tag 08EU] at the standard model, as the canonical map of `standardAdjunction`. -/
theorem isIso_standard [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    IsIso (adjunctionTensorMap (standardAdjunction f) (standardTensor Y) (standardTensor X)
      (standardComparison f) E K) :=
  Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f E K hE hK

end Standard

/-- The comparison `G_Z` of the standard and the locally small model of `D(𝒪_Z)`. -/
abbrev modelFunctor (Z : Scheme.{u}) := (StacksDraft.DerivedModel.schemeModulesComparison Z).functor

/-- The derived tensor products at the two models agree through `G_Z`, as an isomorphism of
functors on pairs. -/
def tensorModelIso (Z : Scheme.{u}) :
    (modelFunctor Z).prod (modelFunctor Z) ⋙
        @tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Z) ≅
      standardTensor Z ⋙ modelFunctor Z :=
  NatIso.ofComponents
    (fun PQ => ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
      Z.sheaf).app PQ.1).app PQ.2) (by
    rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨p, q⟩
    letI := Scheme.Modules.canonicalDerivedMonoidal Z
    have h := (Functor.uncurry.map
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Z.sheaf).hom).naturality
        (X := (P, Q)) (Y := (P', Q')) (p, q)
    have hL : (modelFunctor Z).map p ⊗ₘ (modelFunctor Z).map q =
        ((@Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _ _ _ Z.sheaf _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
            (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)) _ _ _).map
              ((modelFunctor Z).map p)).app ((modelFunctor Z).obj Q) ≫
          ((@Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _ _ _ Z.sheaf _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
            (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)) _ _ _).obj
              ((modelFunctor Z).obj P')).map ((modelFunctor Z).map q) := by
      rw [MonoidalCategory.tensorHom_def]
      rfl
    change ((modelFunctor Z).map p ⊗ₘ (modelFunctor Z).map q) ≫ _ =
      _ ≫ (modelFunctor Z).map (_ ≫ _)
    refine (congrArg (· ≫ _) hL).trans (h.trans ?_)
    exact congrArg (_ ≫ ·) ((modelFunctor Z).map_comp _ _).symm)

/-- Cancelling the comparison isomorphisms around a tensorator. -/
lemma comp_eq_of_eq_conj {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (L : C ⥤ D) {A B : C} (i : A ≅ B) {M N P₁ P₂ Q₁ Q₂ : D} (p : L.obj B ⟶ M) (g : M ⟶ N)
    (t : P₁ ⊗ Q₁ ≅ N) (u : P₁ ≅ P₂) (v : Q₁ ≅ Q₂) (δ : L.obj A ⟶ P₂ ⊗ Q₂)
    (hδ : δ = L.map i.hom ≫ p ≫ g ≫ t.inv ≫ u.hom ▷ Q₁ ≫ P₂ ◁ v.hom) :
    p ≫ g = L.map i.inv ≫ δ ≫ (u.inv ⊗ₘ v.inv) ≫ t.hom := by
  rw [hδ]
  simp only [Category.assoc]
  rw [← tensorHom_def_assoc]
  simp

/-- **The projection-formula map of `D(𝒪)` at the two models**: if the oplax tensorator of `Lf^*`
at the locally small model is, on objects coming from the standard model, the comparison of
[Stacks, Tag 079U] transported through the comparisons of the two models (`hB3`), then the
comparison `G_Y` of the models carries the projection-formula map `Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K)`
of the standard model to that of the locally small model at `(G_X E, G_Y K)`, conjugated by the
comparisons of `Rf_*`, `Lf^*` and `⊗ᴸ`. -/
theorem modelFunctor_map_adjunctionTensorMap
    (hB3 : ∀ K L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _),
      @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            f.toLRSHom.toShHom).toOplaxMonoidal
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj K)
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj L) =
        (derivedPullback f).map
            (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              Y.sheaf).hom.app K).app L) ≫
          (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv.app _ ≫
          (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map
            ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
              f.toLRSHom.toShHom).app (K, L)) ≫
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              X.sheaf).inv.app _).app _) ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso
              f.toLRSHom.toShHom).hom.app K)).app _ ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app L))
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules))
    (K : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard Y.Modules)) :
    (modelFunctor Y).map (adjunctionTensorMap (standardAdjunction f) (standardTensor Y)
        (standardTensor X) (standardComparison f) E K) =
      (tensorModelIso Y).inv.app ((ProjectionFormulaLocallySmall.standardPushforward f).obj E, K) ≫
        (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)).map
          ((show (modelFunctor Y).obj
                ((ProjectionFormulaLocallySmall.standardPushforward f).obj E) ⟶
              (derivedPushforward f).obj ((modelFunctor X).obj E) from
            (StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).hom.app E) ×ₘ
            𝟙 ((modelFunctor Y).obj K)) ≫
        adjunctionTensorMap (derivedAdjunction f)
          (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y))
          (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)) (tensorComparison f)
          ((modelFunctor X).obj E) ((modelFunctor Y).obj K) ≫
        (derivedPushforward f).map ((@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
            (𝟙 ((modelFunctor X).obj E) ×ₘ
              (StacksDraft.DerivedModel.derivedPullbackModelIso
                f.toLRSHom.toShHom).symm.hom.app K) ≫
          (tensorModelIso X).hom.app (E, (standardPullback f).obj K)) ≫
        (show (derivedPushforward f).obj ((modelFunctor X).obj ((standardTensor X).obj
              (E, (standardPullback f).obj K))) ⟶
            (modelFunctor Y).obj ((ProjectionFormulaLocallySmall.standardPushforward f).obj
              ((standardTensor X).obj (E, (standardPullback f).obj K))) from
          (StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).inv.app
          ((standardTensor X).obj (E, (standardPullback f).obj K))) := by
  refine map_adjunctionTensorMap_of_counit_comm (standardAdjunction f) (derivedAdjunction f)
    (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).symm
    (StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).symm
    (tensorModelIso Y) (tensorModelIso X) (standardComparison f) (tensorComparison f)
    (fun Y₀ => (StacksDraft.DerivedModel.map_derivedPushforwardModelIso_comp_counit
      f.toLRSHom.toShHom Y₀).symm) ?_ E K
  intro P Q
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let i := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Y.sheaf).app
    P).app Q
  let p := (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv.app
    ((standardTensor Y).obj (P, Q))
  let g := (modelFunctor X).map ((standardComparison f).app (P, Q))
  let t := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso X.sheaf).app
    ((standardPullback f).obj P)).app ((standardPullback f).obj Q)
  let u : (modelFunctor X).obj ((standardPullback f).obj P) ≅
      (derivedPullback f).obj ((modelFunctor Y).obj P) :=
    (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).app P
  let v : (modelFunctor X).obj ((standardPullback f).obj Q) ≅
      (derivedPullback f).obj ((modelFunctor Y).obj Q) :=
    (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).app Q
  exact comp_eq_of_eq_conj (derivedPullback f) i p g t u v _ (hB3 P Q)

/-- **The projection-formula map of `D(𝒪)` at the locally small model, from the standard one**:
if the oplax tensorator of `Lf^*` at the locally small model is, on objects coming from the
standard model, the comparison of [Stacks, Tag 079U] transported through the comparisons of the
two models (`hB3`), then the projection-formula map at the locally small model is invertible at
such objects whenever the one at the standard model is. -/
theorem isIso_of_isIso_standard
    (hB3 : ∀ K L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _),
      @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            f.toLRSHom.toShHom).toOplaxMonoidal
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj K)
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj L) =
        (derivedPullback f).map
            (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              Y.sheaf).hom.app K).app L) ≫
          (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv.app _ ≫
          (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map
            ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
              f.toLRSHom.toShHom).app (K, L)) ≫
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              X.sheaf).inv.app _).app _) ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso
              f.toLRSHom.toShHom).hom.app K)).app _ ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app L))
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules))
    (K : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard Y.Modules))
    (h : IsIso (adjunctionTensorMap (standardAdjunction f) (standardTensor Y) (standardTensor X)
      (standardComparison f) E K)) :
    IsIso (adjunctionTensorMap (derivedAdjunction f)
        (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal Y))
        (@tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)) (tensorComparison f)
        ((modelFunctor X).obj E) ((modelFunctor Y).obj K)) := by
  refine (isIso_map_adjunctionTensorMap_iff_of_counit_comm (standardAdjunction f)
    (derivedAdjunction f)
    (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).symm
    (StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom).symm
    (tensorModelIso Y) (tensorModelIso X) (standardComparison f) (tensorComparison f)
    (fun Y₀ => (StacksDraft.DerivedModel.map_derivedPushforwardModelIso_comp_counit
      f.toLRSHom.toShHom Y₀).symm) ?_ E K).1 (Functor.map_isIso _ _)
  intro P Q
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let i := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Y.sheaf).app
    P).app Q
  let p := (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv.app
    ((standardTensor Y).obj (P, Q))
  let g := (modelFunctor X).map ((standardComparison f).app (P, Q))
  let t := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso X.sheaf).app
    ((standardPullback f).obj P)).app ((standardPullback f).obj Q)
  let u : (modelFunctor X).obj ((standardPullback f).obj P) ≅
      (derivedPullback f).obj ((modelFunctor Y).obj P) :=
    (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).app P
  let v : (modelFunctor X).obj ((standardPullback f).obj Q) ≅
      (derivedPullback f).obj ((modelFunctor Y).obj Q) :=
    (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).app Q
  exact comp_eq_of_eq_conj (derivedPullback f) i p g t u v _ (hB3 P Q)

/-- **[Stacks, Tag 08EU] for the monoidal structure of `Lf^*` on `D_QCoh`**, given the comparison
`hB3` of the oplax tensorator of `Lf^*` at the locally small model with [Stacks, Tag 079U] at
the standard model: for `f` quasi-compact and quasi-separated, the projection-formula map
`K ⊗ᴸ Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ E)` built from
`quasiCoherentDerivedPullbackTensorIso` is invertible. -/
theorem isIso_projectionFormulaMap_of_comparison [QuasiCompact f] [QuasiSeparated f]
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hB3 : ∀ K L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _),
      @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            f.toLRSHom.toShHom).toOplaxMonoidal
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj K)
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj L) =
        (derivedPullback f).map
            (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              Y.sheaf).hom.app K).app L) ≫
          (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv.app _ ≫
          (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map
            ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
              f.toLRSHom.toShHom).app (K, L)) ≫
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              X.sheaf).inv.app _).app _) ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso
              f.toLRSHom.toShHom).hom.app K)).app _ ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app L))
    (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    IsIso (projectionFormulaMap f hpush
      (quasiCoherentDerivedPullbackTensorIso f).hom E K) := by
  rw [isIso_projectionFormulaMap_iff f hpush E K]
  exact isIso_of_isIso_standard f hB3 E.obj K.obj (isIso_standard f E.obj K.obj
    (fun i => (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      ((homologyFunctorModelIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).app
        E.obj) (E.property i))
    (fun i => (SheafOfModules.isQuasicoherent (structureSheafRing Y.toRingedSpace)).prop_of_iso
      ((homologyFunctorModelIso (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).app
        K.obj) (K.property i)))

/-- **The projection maps of `Lf^* ⊣ Rf_*` on `D_QCoh` are invertible**, for `f` quasi-compact and
quasi-separated, given `hB3` as in `isIso_projectionFormulaMap_of_comparison`. -/
theorem isIso_projectionMap_of_comparison [QuasiCompact f] [QuasiSeparated f]
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hB3 : ∀ K L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _),
      @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            f.toLRSHom.toShHom).toOplaxMonoidal
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj K)
          ((StacksDraft.DerivedModel.schemeModulesComparison Y).functor.obj L) =
        (derivedPullback f).map
            (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              Y.sheaf).hom.app K).app L) ≫
          (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).inv.app _ ≫
          (StacksDraft.DerivedModel.schemeModulesComparison X).functor.map
            ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
              f.toLRSHom.toShHom).app (K, L)) ≫
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso
              X.sheaf).inv.app _).app _) ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso
              f.toLRSHom.toShHom).hom.app K)).app _ ≫
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).map
            ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app L))
    (K : quasiCoherentDerivedCategory Y) (M : quasiCoherentDerivedCategory X) :
    IsIso ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      hpush).projectionMap K M) :=
  haveI := isIso_projectionFormulaMap_of_comparison f hpush hB3
  isIso_projectionMap_of_isIso_projectionFormulaMap f hpush _
    (quasiCoherentDerivedPullbackTensorIso_hom_app f) K M

end Stacks.Duality.ProjectionFormulaMonoidal

end
