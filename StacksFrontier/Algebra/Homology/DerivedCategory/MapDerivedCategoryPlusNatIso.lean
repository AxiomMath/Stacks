module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans

/-!
# Isomorphisms of exact functors act on bounded below derived categories

For exact functors `T S : A ⥤ B` of abelian categories, a transformation `τ : T ⟶ S` acts on the
degreewise actions on derived categories (`Stacks.DerivedFunctor.mapDerivedNatTrans`,
`Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans`). This action is functorial, so an
isomorphism `T ≅ S` gives an isomorphism of the actions on bounded below derived categories.

## Main definitions

* `Stacks.DerivedFunctor.mapDerivedCategoryPlusNatIso`: `T ≅ S` gives
  `T.mapDerivedCategoryPlus ≅ S.mapDerivedCategoryPlus`.

## Main results

* `Stacks.DerivedFunctor.mapDerivedNatTrans_comp`: the action respects composition.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  {T S R : A ⥤ B} [T.Additive] [S.Additive] [R.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- **The action of transformations on derived categories respects composition.** -/
theorem mapDerivedNatTrans_comp (τ : T ⟶ S) (σ : S ⟶ R) :
    mapDerivedNatTrans (τ ≫ σ) = mapDerivedNatTrans τ ≫ mapDerivedNatTrans σ := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun K => ?_
  rw [← cancel_mono (R.mapDerivedCategoryFactors.hom.app K), mapDerivedNatTrans_factors_app,
    NatTrans.comp_app, Category.assoc, mapDerivedNatTrans_factors_app,
    reassoc_of% mapDerivedNatTrans_factors_app, ← Functor.map_comp,
    NatTrans.mapHomologicalComplex_comp]
  rfl

/-- **An isomorphism of exact functors acts on bounded below derived categories**: the actions of
`e.hom` and `e.inv` are inverse to each other. -/
def mapDerivedCategoryPlusNatIso (e : T ≅ S) :
    T.mapDerivedCategoryPlus ≅ S.mapDerivedCategoryPlus where
  hom := mapDerivedCategoryPlusNatTrans e.hom
  inv := mapDerivedCategoryPlusNatTrans e.inv
  hom_inv_id := by
    ext K : 2
    apply DerivedCategory.Plus.ι.map_injective
    have h : mapDerivedNatTrans e.hom ≫ mapDerivedNatTrans e.inv = 𝟙 _ := by
      rw [← mapDerivedNatTrans_comp, e.hom_inv_id]
      refine Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun K => ?_
      simp [← cancel_mono (T.mapDerivedCategoryFactors.hom.app K), mapDerivedNatTrans_factors_app]
    exact NatTrans.congr_app h _
  inv_hom_id := by
    ext K : 2
    apply DerivedCategory.Plus.ι.map_injective
    have h : mapDerivedNatTrans e.inv ≫ mapDerivedNatTrans e.hom = 𝟙 _ := by
      rw [← mapDerivedNatTrans_comp, e.inv_hom_id]
      refine Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun K => ?_
      simp [← cancel_mono (S.mapDerivedCategoryFactors.hom.app K), mapDerivedNatTrans_factors_app]
    exact NatTrans.congr_app h _

end Stacks.DerivedFunctor

end
