module

public import Mathlib.CategoryTheory.Functor.KanExtension.AdjunctionPreserves
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforwardQcqs

/-!
# The canonical comparison in the hypothesis of Stacks 09TG

For an étale morphism `j : V ⟶ W` of algebraic spaces whose direct image preserves quasi-coherence,
the derived direct images on `D(QCoh)` and on `D_QCoh` sit in a square with a canonical comparison
morphism, built from the counit of the derived adjunction between the comparison functor and the
derived coherator. The hypothesis of Stacks 09TG asks that this comparison be an isomorphism
whenever the source is affine and the target a quasi-compact open.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `derivedPushforwardSquareComparison`: the canonical comparison of the square of Stacks 09TG.
* `AffineEtaleDerivedPushforwardSquareCommutes`: the hypothesis of Stacks 09TG, that this
  comparison is an isomorphism for every étale morphism from an affine space to a quasi-compact
  open.

## Main results

* `isIso_derivedModulePushforwardComplexUnit_app_of_isIso_comparison`: if the comparison is
  invertible, the derivation unit of `Rj_*` is invertible at every K-injective complex of
  quasi-coherent modules.
* `AffineEtaleDerivedPushforwardSquareCommutes.affineEtaleDerivedPushforwardCompatible`: the
  canonical form of the hypothesis implies the form with an arbitrary isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparison

variable (Z : AlgebraicSpaces B S hS)

/-- The comparison functor of Stacks 08F1 followed by the inclusion `D_QCoh(𝒪_Z) ⥤ D(𝒪_Z)` is left
adjoint to the derived coherator `RQ_Z`. -/
def comparisonCompιDerivedCoheratorAdjunction :
    quasicoherentDerivedComparison B S hS Z.1 Z.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)))).ι ⊣
      derivedCoherator B S hS Z.1 Z.2 :=
  (derivedCoheratorAdjunction B S hS Z.1 Z.2 (coherator B S hS Z.1 Z.2)
      (coheratorAdjunction B S hS Z.1 Z.2) (derivedCoherator B S hS Z.1 Z.2)
      (derivedCoheratorUnit B S hS Z.1 Z.2)).ofNatIsoLeft
    (comparisonCompιIsoDerivedFunctorOfExact B S hS Z.1 Z.2).symm

/-- On the class of a complex of quasi-coherent modules, the comparison functor followed by the
inclusion into `D(𝒪_Z)` is the class of the same complex regarded as a complex of modules. -/
def localizationCompComparisonCompιIso :
    DerivedCategory.Q ⋙ (quasicoherentDerivedComparison B S hS Z.1 Z.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Z.1 Z.2).O)))).ι) ≅
      (quasicoherentSheavesι B S hS Z).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft _ (quasicoherentDerivedComparisonCompιIso B S hS Z.1 Z.2) ≪≫
    (quasicoherentSheavesι B S hS Z).mapDerivedCategoryFactors

end Comparison

section Square

variable {V W : AlgebraicSpaces B S hS} (j : V ⟶ W)
  (hpush : PushforwardPreservesQuasicoherence B S hS j)

/-- `Φ ⋙ i_W ⋙ J_W` is a right derived functor of `j_*` on quasi-coherent modules followed by
`i_W ⋙ J_W`. -/
instance isRightDerivedFunctor_derivedQuasicoherentPushforward_comp_comparison :
    (derivedQuasicoherentPushforward B S hS j hpush ⋙
        (quasicoherentDerivedComparison B S hS W.1 W.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS W.1 W.2).O)))).ι)).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedQuasicoherentPushforwardUnit B S hS j hpush) _ ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
        (ComplexShape.up ℤ)) := by
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  have := (comparisonCompιDerivedCoheratorAdjunction B S hS W).preservesLeftKanExtension
    ((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q) DerivedCategory.Q
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension
    (derivedQuasicoherentPushforward B S hS j hpush)
    (derivedQuasicoherentPushforwardUnit B S hS j hpush)
    (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
      (ComplexShape.up ℤ))
  infer_instance

/-- The underived square `j_* ∘ ι_V = ι_W ∘ j_*`, on cochain complexes. -/
def mapHomologicalComplexQuasicoherentPushforwardCompιIso :
    (quasicoherentPushforward B S hS j hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (quasicoherentSheavesι B S hS W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (quasicoherentSheavesι B S hS V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (quasicoherentPushforwardCompιIso B S hS j hpush) _ ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm

/-- The structure map of the square of Stacks 09TG on cochain complexes: the class of `j_*K` in
`D(𝒪_W)`, which is `ι_W(j_* K) = j_*(ι_V K)`, followed by the derivation unit of `Rj_*`. -/
def derivedPushforwardSquareUnit :
    ((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙
      (quasicoherentDerivedComparison B S hS W.1 W.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS W.1 W.2).O)))).ι) ⟶
    DerivedCategory.Q ⋙ ((quasicoherentDerivedComparison B S hS V.1 V.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS V.1 V.2).O)))).ι) ⋙
      derivedModulePushforward B S hS j) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (localizationCompComparisonCompιIso B S hS W).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (mapHomologicalComplexQuasicoherentPushforwardCompιIso B S hS j hpush).hom
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (derivedModulePushforwardComplexUnit B S hS j) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (localizationCompComparisonCompιIso B S hS V).inv _ ≫
    (Functor.associator _ _ _).hom

/-- **The canonical comparison of the square of Stacks 09TG.** -/
def derivedPushforwardSquareComparison :
    derivedQuasicoherentPushforward B S hS j hpush ⋙
        (quasicoherentDerivedComparison B S hS W.1 W.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS W.1 W.2).O)))).ι) ⟶
      (quasicoherentDerivedComparison B S hS V.1 V.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS V.1 V.2).O)))).ι) ⋙
        derivedModulePushforward B S hS j :=
  Functor.rightDerivedDesc _
    (Functor.whiskerRight (derivedQuasicoherentPushforwardUnit B S hS j hpush) _ ≫
      (Functor.associator _ _ _).hom)
    (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
      (ComplexShape.up ℤ)) _ (derivedPushforwardSquareUnit B S hS j hpush)

/-- The canonical comparison precomposed with the image of the derivation unit of `Φ` at a complex
`K` is the structure map `derivedPushforwardSquareUnit` at `K`. -/
theorem derivedPushforwardSquareComparison_fac
    (K : CochainComplex (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ℤ) :
    (quasicoherentDerivedComparison B S hS W.1 W.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS W.1 W.2).O)))).ι).map
        ((derivedQuasicoherentPushforwardUnit B S hS j hpush).app K) ≫
      (derivedPushforwardSquareComparison B S hS j hpush).app (DerivedCategory.Q.obj K) =
    (derivedPushforwardSquareUnit B S hS j hpush).app K := by
  have h := Functor.rightDerived_fac_app _
    (Functor.whiskerRight (derivedQuasicoherentPushforwardUnit B S hS j hpush) _ ≫
      (Functor.associator _ _ _).hom)
    (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
      (ComplexShape.up ℤ)) _ (derivedPushforwardSquareUnit B S hS j hpush) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id] at h
  exact h

/-- The component of `derivedPushforwardSquareUnit` at a complex `K`, as the composite of its four
factors. -/
theorem derivedPushforwardSquareUnit_app
    (K : CochainComplex (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ℤ) :
    (derivedPushforwardSquareUnit B S hS j hpush).app K =
      (localizationCompComparisonCompιIso B S hS W).hom.app
          (((quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((mapHomologicalComplexQuasicoherentPushforwardCompιIso B S hS j hpush).hom.app K) ≫
        (derivedModulePushforwardComplexUnit B S hS j).app
          (((quasicoherentSheavesι B S hS V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (derivedModulePushforward B S hS j).map
          ((localizationCompComparisonCompιIso B S hS V).inv.app K) := by
  simp [derivedPushforwardSquareUnit]

open Stacks.Injectives.KInjectiveResolution in
/-- If the canonical comparison of the square is invertible, then the derivation unit of `Rj_*` is
invertible at every K-injective complex of quasi-coherent modules. -/
theorem isIso_derivedModulePushforwardComplexUnit_app_of_isIso_comparison
    [IsIso (derivedPushforwardSquareComparison B S hS j hpush)]
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedModulePushforwardComplexUnit B S hS j).app
      (((quasicoherentSheavesι B S hS V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  let : IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) :=
    quasicoherentSheaves_isGrothendieckAbelian B S hS V.1 V.2
  have hΦ : IsIso ((derivedQuasicoherentPushforwardUnit B S hS j hpush).app I) :=
    isIso_app_of_isKInjective DerivedCategory.Q _ _
      (invertsQuasiIso_mapHomologicalComplex_comp_Q (quasicoherentPushforward B S hS j hpush))
      I hI
  have h := derivedPushforwardSquareComparison_fac B S hS j hpush I
  have hτ : IsIso ((derivedPushforwardSquareUnit B S hS j hpush).app I) := by
    rw [← h]
    infer_instance
  rw [derivedPushforwardSquareUnit_app] at hτ
  simpa using hτ

end Square

/-- **The hypothesis of Stacks 09TG, with the canonical comparison.** The canonical comparison
between the two derived direct images is an isomorphism for every étale morphism from an affine
space to a quasi-compact open of `X`. -/
def AffineEtaleDerivedPushforwardSquareCommutes (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ (W : AlgebraicSpaces B S hS) (jW : W ⟶ X), IsOpenImmersion B S hS jW.hom →
    IsQuasiCompactSpace B S hS W.1 →
    ∀ (V : AlgebraicSpaces B S hS) (j : V ⟶ W), IsEtale B S hS j.hom →
      IsAffineSpace B S hS V.1 →
      ∀ hpush : PushforwardPreservesQuasicoherence B S hS j,
        IsIso (derivedPushforwardSquareComparison B S hS j hpush)

/-- The canonical form of the hypothesis of Stacks 09TG implies the form with an arbitrary
isomorphism, `AlgebraicGeometry.Space.AffineEtaleDerivedPushforwardCompatible`. -/
theorem AffineEtaleDerivedPushforwardSquareCommutes.affineEtaleDerivedPushforwardCompatible
    {X : AlgebraicSpaces B S hS} (h : AffineEtaleDerivedPushforwardSquareCommutes B S hS X) :
    AffineEtaleDerivedPushforwardCompatible B S hS X.1 X.2 := by
  intro W jW hjW hWqc V j hj hV hpush
  have := h W jW hjW hWqc V j hj hV hpush
  exact ⟨derivedModulePushforward B S hS j, derivedModulePushforwardComplexUnit B S hS j,
    derivedQuasicoherentPushforward B S hS j hpush,
    derivedQuasicoherentPushforwardUnit B S hS j hpush, inferInstance, inferInstance,
    ⟨asIso (derivedPushforwardSquareComparison B S hS j hpush)⟩⟩

end AlgebraicGeometry.Space
