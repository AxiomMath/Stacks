module

public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModel

/-!
# The counit of the derived adjunction of an exact left adjoint

Let `G ⊣ F` be an adjunction between abelian categories with `G` exact, and let `R` be a right
derived functor of `F` on derived categories. We describe the counit of the induced adjunction
`adjunctionOfExact` between the derived functor of `G` and `R`, and show that its component at a
K-injective complex `J` is an isomorphism exactly when the counit of the adjunction on cochain
complexes is a quasi-isomorphism at `J`.

## Main results

* `adjunctionOfExact_counit_fac`: The counit of `adjunctionOfExact` on the image of a complex of
  the homotopy category, precomposed with the derived image of the homotopy unit, is the
  localization of the counit of the adjunction on homotopy categories.
* `isIso_localization_map_iff_quasiIso`: A morphism of cochain complexes becomes an isomorphism in
  the derived category if and only if it is a quasi-isomorphism.
* `isIso_adjunctionOfExact_counit_app_iff`: At a K-injective complex `J`, the counit of
  `adjunctionOfExact` is an isomorphism if and only if the counit of the adjunction on cochain
  complexes is a quasi-isomorphism at `J`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedModel

variable {A : Type*} {B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  [CategoryWithHomology A] [CategoryWithHomology B]
  (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (QSource : CochainComplex A ℤ ⥤ DerivedCategory A)
  [QSource.IsLocalization (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (QTarget : CochainComplex B ℤ ⥤ DerivedCategory B)
  [QTarget.IsLocalization (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian A] {F : A ⥤ B} [F.Additive]
  (adj : G ⊣ F)
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QTarget ⟶ QSource ⋙ R)
  [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- For `K` in the homotopy category, the counit of `adjunctionOfExact` at the localization of `K`,
precomposed with the image under `derivedFunctorOfExact` of the homotopy unit at `K`, equals the
isomorphism `derivedFunctorOfExactFac` followed by the localization of the counit of the adjunction
`Adjunction.mapHomotopyCategoryAdjunction` at `K`. -/
theorem adjunctionOfExact_counit_fac (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (derivedFunctorOfExact G QSource QTarget).map
        ((homotopyUnit F QTarget QSource R α).app K) ≫
      (adjunctionOfExact G QSource QTarget adj R α).counit.app
        ((homotopyLocalization QSource).obj K) =
    (derivedFunctorOfExactFac G QSource QTarget).hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (homotopyLocalization QSource).map
        ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app K) := by
  unfold adjunctionOfExact
  dsimp only
  generalize_proofs
  rename_i h
  exact (Classical.choose_spec h).2 K

omit [IsGrothendieckAbelian A] [R.IsRightDerivedFunctor α
  (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] in
/-- A morphism `f` of cochain complexes becomes an isomorphism under a localization functor
`QSource` at the quasi-isomorphisms if and only if `f` is a quasi-isomorphism. -/
theorem isIso_localization_map_iff_quasiIso {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    IsIso (QSource.map f) ↔ QuasiIso f := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso,
    ← NatIso.isIso_map_iff (Localization.compUniqFunctor (DerivedCategory.Q (C := A)) QSource
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))) f, Functor.comp_map]
  exact isIso_iff_of_reflects_iso _ _

/-- For a K-injective cochain complex `J`, the counit of `adjunctionOfExact` at `J` is an
isomorphism if and only if the counit of `Adjunction.mapHomologicalComplexAdjunction` at `J` is a
quasi-isomorphism. -/
theorem isIso_adjunctionOfExact_counit_app_iff (J : CochainComplex A ℤ) (hJ : J.IsKInjective) :
    IsIso ((adjunctionOfExact G QSource QTarget adj R α).counit.app (QSource.obj J)) ↔
      QuasiIso ((Adjunction.mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).counit.app
        J) := by
  have hβ := isIso_homotopyUnit_app_quotient F QSource QTarget R α J
  rw [← NatTrans.isIso_app_iff_of_iso _ ((homotopyLocalizationQuotientIso QSource).app J),
    ← isIso_localization_map_iff_quasiIso QSource,
    ← NatIso.isIso_map_iff (homotopyLocalizationQuotientIso QSource), Functor.comp_map]
  have hfac := adjunctionOfExact_counit_fac G QSource QTarget adj R α
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)
  rw [Adjunction.mapHomotopyCategoryAdjunction_counit_app_quotient] at hfac
  have := ((derivedFunctorOfExactFac G QSource QTarget).app
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J))).isIso_hom
  rw [← isIso_comp_left_iff ((derivedFunctorOfExact G QSource QTarget).map
    ((homotopyUnit F QTarget QSource R α).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)))]
  exact (congrArg IsIso hfac).to_iff.trans (isIso_comp_left_iff _ _)

end Stacks.DerivedModel
