module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism

/-!
# The connecting morphism of a right derived functor, computed on injective resolutions

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` with enough injectives,
and let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of `𝒜` covered by a short exact sequence
`0 ⟶ I₁ ⟶ I₂ ⟶ I₃ ⟶ 0` of injective resolutions whose degreewise image under `F` is again short
exact. The connecting morphism `R ⁿF(X₃) ⟶ R ⁿ⁺¹F(X₁)` attached to the distinguished triangle of
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` (`Stacks.Cohomology.CechDelta.rightDerivedPlusδ`) is, through the
identification of `R ⁿF` with the cohomology of `F(I)`, the connecting morphism of the long exact
cohomology sequence of `0 ⟶ F(I₁) ⟶ F(I₂) ⟶ F(I₃) ⟶ 0`, computed by the snake lemma.

This is the statement that `Stacks.Cohomology.CechComparison.derivedδ_eq` proves for degree-zero
Čech cohomology; the argument there is abstract in the functor, and is run here for an arbitrary
`F`.

## Main results

* `Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusδ_eq_resolutionTriangleδ`: the
  connecting morphism in the derived-category conventions, read through
  `derivedPlusResolutionHomologyIso`, is the connecting morphism of the derived-category triangle
  of the degreewise image of the resolutions.
* `Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusδ_resolution`: **the connecting
  morphism, read through `derivedPlusToStandardObjOfResolution`, is the snake-lemma connecting
  morphism of the degreewise image of the resolutions**, read through
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
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

/-- **The connecting morphism of the derived-category triangle attached to a short exact sequence
of `ℕ`-indexed complexes whose degreewise image under `F` is short exact**, in cohomology of
degree `n`: extend the sequence by zero to `ℤ`, apply `F` in each degree and take the connecting
morphism of `DerivedCategory.triangleOfSES`, read in the `Qh ∘ quotient` spelling that
`Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso` presents. -/
def resolutionTriangleδ {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (up ℕ))).ShortExact) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient B (up ℤ)).obj
            ((F.mapHomologicalComplex (up ℤ)).obj
              (R.X₃.extend ComplexShape.embeddingUpNat)))) ⟶
      (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient B (up ℤ)).obj
            ((F.mapHomologicalComplex (up ℤ)).obj
              (R.X₁.extend ComplexShape.embeddingUpNat)))) :=
  (DerivedCategory.homologyFunctor B (n : ℤ)).map
      ((DerivedCategory.quotientCompQhIso B).hom.app _) ≫
    mapExtendTriangleδ F hFR n ≫
    (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
      ((DerivedCategory.quotientCompQhIso B).inv.app _)

/-- Seven composable morphisms, bracketed in the two ways in which the comparison isomorphisms
of `rightDerivedPlusδ_resolution` produce them. Stated separately because the two presentations
of the cohomology of `F(I)` meet in the middle, where `simp` cannot rewrite with associativity. -/
private theorem reassoc_seven {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (k : X₅ ⟶ X₆)
    (l : X₆ ⟶ X₇) :
    ((a ≫ b) ≫ c) ≫ d ≫ e ≫ k ≫ l = a ≫ ((b ≫ (c ≫ d ≫ e) ≫ k) ≫ l) := by
  simp only [Category.assoc]

/-- Five composable morphisms, bracketed in the two ways in which the comparison isomorphisms
of `rightDerivedPlusδ_eq_resolutionTriangleδ` produce them, as for `reassoc_seven`. -/
private theorem reassoc_five {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) :
    (a ≫ b) ≫ c ≫ d ≫ e = a ≫ ((b ≫ c ≫ d) ≫ e) := by
  simp only [Category.assoc]

variable {S : ShortComplex A} (hS : S.ShortExact)
  (I₁ : InjectiveResolution S.X₁) (I₂ : InjectiveResolution S.X₂)
  (I₃ : InjectiveResolution S.X₃)
  (f : I₁.cocomplex ⟶ I₂.cocomplex) (g : I₂.cocomplex ⟶ I₃.cocomplex) (zero : f ≫ g = 0)
  (comm_f : I₁.ι.f 0 ≫ f.f 0 = S.f ≫ I₂.ι.f 0)
  (comm_g : I₂.ι.f 0 ≫ g.f 0 = S.g ≫ I₃.ι.f 0)
  (hR : (ShortComplex.mk f g zero).ShortExact)
  (hFR : (((ShortComplex.mk f g zero)).map (F.mapHomologicalComplex (up ℕ))).ShortExact)

include comm_f comm_g hR

/-- **The connecting morphism of `RF`, read through `derivedPlusResolutionHomologyIso`, is
`resolutionTriangleδ`** of the degreewise image of a compatible short exact sequence of injective
resolutions. -/
theorem rightDerivedPlusδ_eq_resolutionTriangleδ (n : ℕ) :
    (derivedPlusResolutionHomologyIso F I₃ n).inv ≫
        CechDelta.rightDerivedPlusδ F hS n ≫
        (derivedPlusResolutionHomologyIso F I₁ (n + 1)).hom =
      resolutionTriangleδ F hFR n := by
  have hsq : (resolutionDerivedComparison F I₃).hom ≫
        mapExtendSESδ F (R := ShortComplex.mk f g zero) hFR =
      (DerivedCategory.Plus.ι.map ((CechDelta.derivedDeltaFunctorStructure F).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            (F.rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison F I₁).hom)⟦(1 : ℤ)⟧' :=
    (comm₃_resolutionDerivedComparison F hS I₁ I₂ I₃ f g zero comm_f comm_g hR hFR).trans
      (eq_whisker (mapδ_rightDerivedFunctorPlus_comp_ι_singlePlusδ F hS) _)
  have hA : CechDelta.rightDerivedPlusδ (F) hS n =
      (DerivedCategory.homologyFunctor (B) 0).shiftMap
        (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure (F)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((F).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (A) 0).obj S.X₁)))
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) :=
    Functor.comp_shiftMap DerivedCategory.Plus.ι _ _ _ _ _
  have key : (resolutionDerivedComparison (F) I₃).inv ≫
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure (F)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((F).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (A) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison (F) I₁).hom)⟦(1 : ℤ)⟧' =
      mapExtendSESδ (F)
          (R := ShortComplex.mk f g zero) hFR := by
    rw [Iso.inv_comp_eq]
    exact hsq.symm
  have hkey : (DerivedCategory.homologyFunctor (B) (n : ℤ)).map
          (resolutionDerivedComparison (F) I₃).inv ≫
        (DerivedCategory.homologyFunctor (B) 0).shiftMap
          (DerivedCategory.Plus.ι.map
              ((CechDelta.derivedDeltaFunctorStructure (F)).δ hS) ≫
            (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
              ((F).rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor (A) 0).obj S.X₁)))
          (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ≫
        (DerivedCategory.homologyFunctor (B) ((n + 1 : ℕ) : ℤ)).map
          (resolutionDerivedComparison (F) I₁).hom =
      mapExtendTriangleδ (F) hFR n := by
    rw [mapExtendTriangleδ_eq, ← key]
    conv_rhs => rw [Functor.shiftMap_comp', Functor.shiftMap_comp]
    rfl
  have e₃ : ((DerivedCategory.quotientCompQhIso (B)).app
          (((F).mapHomologicalComplex (up ℤ)).obj
            (I₃.cocomplex.extend ComplexShape.embeddingUpNat))).hom ≫
        (resolutionDerivedComparison (F) I₃).inv =
      DerivedCategory.Plus.ι.map
        (derivedPlusResolutionIso (F) I₃).inv :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (Iso.hom_inv_id _) _).trans (Category.id_comp _))
  have e₁ : (resolutionDerivedComparison (F) I₁).hom ≫
        ((DerivedCategory.quotientCompQhIso (B)).app
          (((F).mapHomologicalComplex (up ℤ)).obj
            (I₁.cocomplex.extend ComplexShape.embeddingUpNat))).inv =
      DerivedCategory.Plus.ι.map
        (derivedPlusResolutionIso (F) I₁).hom :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (Iso.hom_inv_id _)).trans (Category.comp_id _))
  have hc₃ : (DerivedCategory.homologyFunctor B (n : ℤ)).map
        ((DerivedCategory.quotientCompQhIso B).hom.app _) ≫
      (DerivedCategory.homologyFunctor B (n : ℤ)).map (resolutionDerivedComparison F I₃).inv =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I₃).inv) := by
    rw [← Functor.map_comp]
    exact congrArg _ e₃
  have hc₁ : (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
        (resolutionDerivedComparison F I₁).hom ≫
      (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
        ((DerivedCategory.quotientCompQhIso B).inv.app _) =
      (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
        (DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I₁).hom) := by
    rw [← Functor.map_comp]
    exact congrArg _ e₁
  rw [hA, derivedPlusResolutionHomologyIso_inv, derivedPlusResolutionHomologyIso_hom,
    resolutionTriangleδ]
  rw [← hc₃, ← hc₁, ← hkey]
  exact reassoc_five (C := B) _ _ _ _ _

/-- **The connecting morphism of `RF` on a compatible short exact sequence of injective
resolutions.** Read through `derivedPlusToStandardObjOfResolution` at the resolutions `I₃` and
`I₁`, the connecting morphism `R ⁿF(X₃) ⟶ R ⁿ⁺¹F(X₁)` of the distinguished triangle of `RF` is
the snake-lemma connecting morphism of `0 ⟶ F(I₁) ⟶ F(I₂) ⟶ F(I₃) ⟶ 0`, read through
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`. -/
theorem rightDerivedPlusδ_resolution (n : ℕ) :
    (derivedPlusToStandardObjOfResolution F I₃ n).inv ≫
        CechDelta.rightDerivedPlusδ F hS n ≫
        (derivedPlusToStandardObjOfResolution F I₁ (n + 1)).hom =
      (I₃.isoRightDerivedObj F n).hom ≫ hFR.δ n (n + 1) rfl ≫
        (I₁.isoRightDerivedObj F (n + 1)).inv := by
  have h := rightDerivedPlusδ_eq_resolutionTriangleδ F hS I₁ I₂ I₃ f g zero comm_f comm_g hR hFR n
  have hα := extendedHomologyIso_conj_mapExtendTriangleδ F hFR n
  dsimp only at hα
  rw [resolutionTriangleδ] at h
  rw [← h] at hα
  rw [derivedPlusToStandardObjOfResolution_eq_trans, derivedPlusToStandardObjOfResolution_eq_trans]
  change (((I₃.isoRightDerivedObj F n).hom ≫ (extendedHomologyIso F I₃.cocomplex n).inv) ≫
      (derivedPlusResolutionHomologyIso F I₃ n).inv) ≫ CechDelta.rightDerivedPlusδ F hS n ≫
      (derivedPlusResolutionHomologyIso F I₁ (n + 1)).hom ≫
        ((extendedHomologyIso F I₁.cocomplex (n + 1)).hom ≫
          (I₁.isoRightDerivedObj F (n + 1)).inv) = _
  rw [← hα]
  exact reassoc_seven _ _ _ _ _ _ _

end Stacks.Cohomology.HigherDirectImagePresheaf

end
