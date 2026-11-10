module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism

/-!
# The connecting morphism of right derived functors, computed on a horseshoe

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` having enough
injectives, and let `0 → X₁ → X₂ → X₃ → 0` be a short exact sequence of `𝒜` resolved by a short
exact sequence `0 → I₁ → I₂ → I₃ → 0` of injective resolutions whose degreewise image under `F`
is still short exact. Identify `RⁿF(Xᵢ) = Hⁿ(RF(Xᵢ[0]))` with `Hⁿ(F(Iᵢ))` through the resolution.
Then the connecting morphism `RⁿF(X₃) → Rⁿ⁺¹F(X₁)` of the distinguished triangle of `D⁺(ℬ)`
becomes the snake-lemma connecting morphism of `0 → F(I₁) → F(I₂) → F(I₃) → 0`.

## Main definitions and results

* `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionHomologyIso`: the identification
  `RⁿF(M) ≅ Hⁿ(F(I))` through an injective resolution `I` of `M`.
* `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionHomologyIso_conj_rightDerivedPlusδ`:
  the connecting morphism, read through these identifications, is the snake-lemma connecting
  morphism of the degreewise image of the resolving sequence.
* `Stacks.Cohomology.HigherDirectImagePresheaf.toRightDerivedZero_comp_resolutionHomologyIso`:
  in degree zero the identification sends a section of `F(M)` to the class of its image in
  `F(I⁰)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace Stacks.Cohomology.HigherDirectImagePresheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- The `n`-th right derived functor of `F` at `M`, computed as the `n`-th cohomology of the
image under `F` of an injective resolution `I` of `M`. -/
def resolutionHomologyIso {M : A} (I : InjectiveResolution M) (n : ℕ) :
    (F.rightDerivedPlus (n : ℤ)).obj M ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  derivedPlusResolutionHomologyIso F I n ≪≫ extendedHomologyIso F I.cocomplex n

/-- **The connecting morphism of `RF`, in the derived-category reading, is the snake-lemma
connecting morphism of a horseshoe.** -/
theorem resolutionHomologyIso_conj_rightDerivedPlusδ {S : ShortComplex A} (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₂ : InjectiveResolution S.X₂)
    (I₃ : InjectiveResolution S.X₃)
    (f : I₁.cocomplex ⟶ I₂.cocomplex) (g : I₂.cocomplex ⟶ I₃.cocomplex) (zero : f ≫ g = 0)
    (comm_f : I₁.ι.f 0 ≫ f.f 0 = S.f ≫ I₂.ι.f 0)
    (comm_g : I₂.ι.f 0 ≫ g.f 0 = S.g ≫ I₃.ι.f 0)
    (hR : (ShortComplex.mk f g zero).ShortExact)
    (hFR : (((ShortComplex.mk f g zero)).map
      (F.mapHomologicalComplex (up ℕ))).ShortExact) (n : ℕ) :
    (resolutionHomologyIso F I₃ n).inv ≫ CechDelta.rightDerivedPlusδ F hS n ≫
        (resolutionHomologyIso F I₁ (n + 1)).hom =
      hFR.δ n (n + 1) rfl := by
  have hsq : (resolutionDerivedComparison F I₃).hom ≫
        mapExtendSESδ F (R := ShortComplex.mk f g zero) hFR =
      (DerivedCategory.Plus.ι.map ((CechDelta.derivedDeltaFunctorStructure F).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            (F.rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison F I₁).hom)⟦(1 : ℤ)⟧' :=
    (comm₃_resolutionDerivedComparison F hS I₁ I₂ I₃ f g zero comm_f comm_g hR hFR).trans
      (eq_whisker (mapδ_rightDerivedFunctorPlus_comp_ι_singlePlusδ F hS) _)
  have hA : CechDelta.rightDerivedPlusδ F hS n =
      (DerivedCategory.homologyFunctor B 0).shiftMap
        (DerivedCategory.Plus.ι.map ((CechDelta.derivedDeltaFunctorStructure F).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            (F.rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁)))
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) :=
    Functor.comp_shiftMap DerivedCategory.Plus.ι _ _ _ _ _
  have key : (resolutionDerivedComparison F I₃).inv ≫
      (DerivedCategory.Plus.ι.map ((CechDelta.derivedDeltaFunctorStructure F).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            (F.rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison F I₁).hom)⟦(1 : ℤ)⟧' =
      mapExtendSESδ F (R := ShortComplex.mk f g zero) hFR := by
    rw [Iso.inv_comp_eq]
    exact hsq.symm
  have hkey : (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (resolutionDerivedComparison F I₃).inv ≫
        (DerivedCategory.homologyFunctor B 0).shiftMap
          (DerivedCategory.Plus.ι.map ((CechDelta.derivedDeltaFunctorStructure F).δ hS) ≫
            (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
              (F.rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁)))
          (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ≫
        (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
          (resolutionDerivedComparison F I₁).hom =
      mapExtendTriangleδ F hFR n := by
    rw [mapExtendTriangleδ_eq, ← key]
    conv_rhs => rw [Functor.shiftMap_comp', Functor.shiftMap_comp]
    rfl
  have e₃ : ((DerivedCategory.quotientCompQhIso B).app
          ((F.mapHomologicalComplex (up ℤ)).obj
            (I₃.cocomplex.extend ComplexShape.embeddingUpNat))).hom ≫
        (resolutionDerivedComparison F I₃).inv =
      DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I₃).inv :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (Iso.hom_inv_id _) _).trans (Category.id_comp _))
  have e₁ : (resolutionDerivedComparison F I₁).hom ≫
        ((DerivedCategory.quotientCompQhIso B).app
          ((F.mapHomologicalComplex (up ℤ)).obj
            (I₁.cocomplex.extend ComplexShape.embeddingUpNat))).inv =
      DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I₁).hom :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (Iso.hom_inv_id _)).trans (Category.comp_id _))
  have hc₃ := (CategoryTheory.Functor.map_comp
      (DerivedCategory.homologyFunctor B (n : ℤ))
      (((DerivedCategory.quotientCompQhIso B).app
        ((F.mapHomologicalComplex (up ℤ)).obj
          (I₃.cocomplex.extend ComplexShape.embeddingUpNat))).hom)
      (resolutionDerivedComparison F I₃).inv).symm.trans
    (congrArg (fun f => (DerivedCategory.homologyFunctor B (n : ℤ)).map f) e₃)
  have hc₁ := (CategoryTheory.Functor.map_comp
      (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ))
      (resolutionDerivedComparison F I₁).hom
      (((DerivedCategory.quotientCompQhIso B).app
        ((F.mapHomologicalComplex (up ℤ)).obj
          (I₁.cocomplex.extend ComplexShape.embeddingUpNat))).inv)).symm.trans
    (congrArg (fun f =>
      (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map f) e₁)
  have hmid : (derivedPlusResolutionHomologyIso F I₃ n).inv ≫
        CechDelta.rightDerivedPlusδ F hS n ≫
        (derivedPlusResolutionHomologyIso F I₁ (n + 1)).hom =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          ((DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (up ℤ)).obj
              (I₃.cocomplex.extend ComplexShape.embeddingUpNat))) ≫
        mapExtendTriangleδ F hFR n ≫
        (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app
            ((F.mapHomologicalComplex (up ℤ)).obj
              (I₁.cocomplex.extend ComplexShape.embeddingUpNat))) := by
    rw [hA, derivedPlusResolutionHomologyIso_inv, derivedPlusResolutionHomologyIso_hom]
    refine Eq.symm ((whisker_eq _ (eq_whisker hkey.symm _)).trans ?_)
    refine (whisker_eq _ ((Category.assoc _ _ _).trans
      (whisker_eq _ (Category.assoc _ _ _)))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (eq_whisker hc₃ _).trans (whisker_eq _ (whisker_eq _ hc₁))
  have hα := extendedHomologyIso_conj_mapExtendTriangleδ F hFR n
  dsimp only at hα
  refine Eq.trans ?_ hα
  rw [← hmid]
  change ((extendedHomologyIso F I₃.cocomplex n).inv ≫
      (derivedPlusResolutionHomologyIso F I₃ n).inv) ≫ CechDelta.rightDerivedPlusδ F hS n ≫
      ((derivedPlusResolutionHomologyIso F I₁ (n + 1)).hom ≫
        (extendedHomologyIso F I₁.cocomplex (n + 1)).hom) = _
  refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact whisker_eq _ (Category.assoc _ _ _).symm

/-- **Degree-zero normalisation of `resolutionHomologyIso`.** The canonical map
`F(M) ⟶ R⁰F(M)`, carried to the derived-category reading and then computed through an injective
resolution `I`, is the class of the degree-zero cocycle `F(M) ⟶ F(I⁰)`. -/
theorem toRightDerivedZero_comp_resolutionHomologyIso {M : A} (I : InjectiveResolution M) :
    F.toRightDerivedZero.app M ≫ (derivedPlusToStandard F 0).inv.app M ≫
        (resolutionHomologyIso F I 0).hom =
      I.toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ 0 := by
  have h : (derivedPlusToStandard F 0).inv.app M ≫ (resolutionHomologyIso F I 0).hom =
      (I.isoRightDerivedObj F 0).hom := by
    rw [← Iso.app_inv, derivedPlusToStandard_app_eq F I 0]
    refine (Iso.inv_comp_eq _).2 ?_
    rw [derivedPlusToStandardObjOfResolution_eq_trans]
    exact Eq.symm ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
      ((whisker_eq _ (I.isoRightDerivedObj F 0).inv_hom_id).trans (Category.comp_id _)))))
  rw [I.toRightDerivedZero_eq F]
  refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (whisker_eq _ h)).trans ?_
  refine (whisker_eq _ (I.isoRightDerivedObj F 0).inv_hom_id).trans ?_
  exact Category.comp_id _

end Stacks.Cohomology.HigherDirectImagePresheaf
