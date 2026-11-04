module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DerivedPullbackMonoidalComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorExact
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonUnitCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionCommShift

/-!
# The tensorator of `Lf^*` on `D_QCoh` commutes with the shift

Let `f : X ⟶ Y` be a morphism of schemes. The oplax tensorator
`Lf^*(K ⊗ᴸ M) ⟶ Lf^*K ⊗ᴸ Lf^*M` of the monoidal functor `Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`
(`Stacks.Duality.quasiCoherentDerivedPullbackMonoidal`, [Stacks, Tag 079U]) commutes with the
shift in `K`. Here `Lf^*` carries the commutation with the shift it inherits as the left adjoint
of `Rf_*`, and `- ⊗ᴸ M` the one of the derived tensor product.

This file reduces the statement on `D_QCoh` to the same statement on `D(𝒪)`, at the locally small
model: the monoidal structures of `D_QCoh` are those of `D(𝒪)` restricted, and the commutation of
the restricted `Lf^*` with the shift is the one induced by the left derived commutation of the
ambient `Lf^*` (`Stacks.Duality.commShift_quasiCoherentDerivedPullback_eq`).

## Main results

* `Stacks.Duality.commShift_oplaxNatTransLeft_quasiCoherentDerivedPullback_of` — the reduction.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The tensorator of `Lf^*` on `D_QCoh` commutes with the shift in its first variable**, as
soon as the tensorator of `Lf^*` on `D(𝒪)` does, for the left derived commutation of `Lf^*` with
the shift and the commutation of the derived tensor product with the shift. -/
theorem commShift_oplaxNatTransLeft_quasiCoherentDerivedPullback_of
    (M : quasiCoherentDerivedCategory Y)
    (σ : (derivedTensor Y).flip.obj M.obj ⋙ derivedPullback f ⟶
      derivedPullback f ⋙ (derivedTensor X).flip.obj ((derivedPullback f).obj M.obj))
    (hσapp : ∀ K, σ.app K = @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)
      _ _ (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
      (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K M.obj)
    (hσ :
      letI : (derivedPullback f).CommShift ℤ :=
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift
          f.toLRSHom.toShHom
      letI := commShiftDerivedTensorFlipObj Y M.obj
      letI := commShiftDerivedTensorFlipObj X ((derivedPullback f).obj M.obj)
      NatTrans.CommShift σ ℤ) :
    letI := quasiCoherentDerivedMonoidal X
    letI := quasiCoherentDerivedMonoidal Y
    letI := quasiCoherentDerivedPullbackMonoidal f
    letI := commShift_quasiCoherentDerivedPullback f
      (isQuasicoherent_homology_derivedPullback' f) hpush
    NatTrans.CommShift
      (MonoidalProjectionFormula.oplaxNatTransLeft (quasiCoherentDerivedPullback' f) M) ℤ := by
  have key := commShift_quasiCoherentDerivedPullback_eq f
    (isQuasicoherent_homology_derivedPullback' f) hpush
  rw [key]
  let := quasiCoherentDerivedMonoidal X
  let := quasiCoherentDerivedMonoidal Y
  let := quasiCoherentDerivedPullbackMonoidal f
  let : (derivedPullback f).CommShift ℤ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift
      f.toLRSHom.toShHom
  let := Functor.CommShift.ofComp
    (quasiCoherentDerivedPullbackCompιIso f (isQuasicoherent_homology_derivedPullback' f)) ℤ
  let := commShiftDerivedTensorFlipObj Y M.obj
  let := commShiftDerivedTensorFlipObj X ((derivedPullback f).obj M.obj)
  let := commShiftDerivedTensorFlipObj X ((quasiCoherentDerivedPullback' f).obj M).obj
  have hpb : NatTrans.CommShift
      (quasiCoherentDerivedPullbackCompιIso f
        (isQuasicoherent_homology_derivedPullback' f)).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  have hTY : NatTrans.CommShift (quasiCoherentDerivedTensorFlipObjCompιIso Y M).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  have hTX : NatTrans.CommShift (quasiCoherentDerivedTensorFlipObjCompιIso X
      ((quasiCoherentDerivedPullback' f).obj M)).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  have hu₁ : NatTrans.CommShift (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((quasiCoherentDerivedTensor Y).flip.obj M)
        (quasiCoherentDerivedPullbackCompιIso f (isQuasicoherent_homology_derivedPullback' f)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (quasiCoherentDerivedTensorFlipObjCompιIso Y M)
        (derivedPullback f) ≪≫ Functor.associator _ _ _).hom ℤ := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have hu₂ : NatTrans.CommShift (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (quasiCoherentDerivedPullback' f)
        (quasiCoherentDerivedTensorFlipObjCompιIso X ((quasiCoherentDerivedPullback' f).obj M)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (quasiCoherentDerivedPullbackCompιIso f (isQuasicoherent_homology_derivedPullback' f))
        ((derivedTensor X).flip.obj ((derivedPullback f).obj M.obj)) ≪≫
      Functor.associator _ _ _).hom ℤ := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have hσ₀ : NatTrans.CommShift (Functor.whiskerLeft
      (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι σ) ℤ := by
    have := hσ
    infer_instance
  refine Stacks.Triangulated.natTransCommShift_of_whiskerRight_eq ℤ
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
    (MonoidalProjectionFormula.oplaxNatTransLeft (quasiCoherentDerivedPullback' f) M) _ _
    (Functor.whiskerLeft _ σ) hu₁ hu₂ hσ₀ ?_
  ext K
  have h1 : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map
        (Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) K M) =
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map
          ((quasiCoherentDerivedPullback' f).map (𝟙 _)) ≫
        @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)
          _ _ (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K.obj M.obj ≫ 𝟙 _ := by
    let := Scheme.Modules.canonicalDerivedMonoidal X
    let := Scheme.Modules.canonicalDerivedMonoidal Y
    let := quasiCoherent_isMonoidal X
    let := quasiCoherent_isMonoidal Y
    have h := @Functor.monoidalReseat_δ _ _ (ObjectProperty.fullMonoidalSubcategory _) _ _ _ _
      (ObjectProperty.fullMonoidalSubcategory _) _ _ (quasiCoherentDerivedPullback' f)
      (quasiCoherentDerivedPullbackSubcategoryMonoidal f) (quasiCoherentCurriedTensorIso Y)
      (Iso.refl _) (quasiCoherentCurriedTensorIso X) (Iso.refl _) K M
    have hμ : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map
          (@Functor.LaxMonoidal.μ _ _ (ObjectProperty.fullMonoidalSubcategory _) _ _
            (ObjectProperty.fullMonoidalSubcategory _) (quasiCoherentDerivedPullback' f)
            (quasiCoherentDerivedPullbackSubcategoryMonoidal f).toLaxMonoidal K M) =
        @Functor.LaxMonoidal.μ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)
          _ _ (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (derivedPullbackCanonicalMonoidal f).toLaxMonoidal K.obj M.obj ≫
          (derivedPullback f).map (𝟙 _) := rfl
    have hδ : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map
          (@Functor.OplaxMonoidal.δ _ _ (ObjectProperty.fullMonoidalSubcategory _) _ _
            (ObjectProperty.fullMonoidalSubcategory _) (quasiCoherentDerivedPullback' f)
            (quasiCoherentDerivedPullbackSubcategoryMonoidal f).toOplaxMonoidal K M) =
        @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)
          _ _ (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K.obj M.obj := by
      have e := congrArg (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map
          (@Functor.Monoidal.μ_δ _ _ (ObjectProperty.fullMonoidalSubcategory _) _ _
            (ObjectProperty.fullMonoidalSubcategory _) (quasiCoherentDerivedPullback' f)
            (quasiCoherentDerivedPullbackSubcategoryMonoidal f) K M)
      rw [Functor.map_comp, hμ, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
        Category.comp_id] at e
      rw [← cancel_epi (@Functor.LaxMonoidal.μ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)
          _ _ (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (derivedPullbackCanonicalMonoidal f).toLaxMonoidal K.obj M.obj), e,
        @Functor.Monoidal.μ_δ _ _ (Scheme.Modules.canonicalDerivedMonoidal Y)
          _ _ (Scheme.Modules.canonicalDerivedMonoidal X) (derivedPullback f)
          (derivedPullbackCanonicalMonoidal f)]
      rfl
    refine (congrArg (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map h).trans ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) hδ rfl)
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    MonoidalProjectionFormula.oplaxNatTransLeft_app, hσapp]
  have ha : (quasiCoherentDerivedPullbackCompιIso f
      (isQuasicoherent_homology_derivedPullback' f)).hom.app
        (((quasiCoherentDerivedTensor Y).flip.obj M).obj K) = 𝟙 _ := rfl
  have hb : (quasiCoherentDerivedTensorFlipObjCompιIso Y M).hom.app K = 𝟙 _ := rfl
  have hc : (quasiCoherentDerivedPullbackCompιIso f
      (isQuasicoherent_homology_derivedPullback' f)).inv.app K = 𝟙 _ := rfl
  have hd : (quasiCoherentDerivedTensorFlipObjCompιIso X
      ((quasiCoherentDerivedPullback' f).obj M)).inv.app
        ((quasiCoherentDerivedPullback' f).obj K) = 𝟙 _ := rfl
  refine h1.trans ?_
  simp only [ha, hb, hc, hd, CategoryTheory.Functor.map_id, Category.id_comp]
  refine (Category.comp_id _).trans ?_
  refine Eq.symm (Eq.trans (congrArg (· ≫ _) ((Category.id_comp _).trans
    ((Category.id_comp _).trans ((derivedPullback f).map_id _)))) ?_)
  refine (Category.id_comp _).trans ?_
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Category.comp_id _)

end Stacks.Duality

end
