module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatComplexes

/-!
# The homotopy-level homology comparison of a left exact functor, read at a complex

For a left exact functor `F` between abelian categories and a cochain complex `Z`, the comparison
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopyHomologyComparisonToDerived`
at the image of `Z` in the homotopy category is the comparison `homologyComparison F Z q` of
complexes, conjugated by the two factorisations of the cohomology functor: through the homotopy
category (`HomotopyCategory.homologyFunctorFactors`) and through the derived category
(`DerivedCategory.homologyFunctorFactorsh`).

## Main results

* `Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient_crossing`: the comparison
  at `Z`, with the identification `CategoryTheory.Functor.mapHomotopyCategoryFactors` of the two
  spellings of the image complex left explicit.
* `Stacks.EdgeCompat.factorsh_hom_app_comp_map_mapHomotopyCategoryFactors`: the component of
  `DerivedCategory.homologyFunctorFactorsh` absorbs that identification.
* `Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient`: the comparison at `Z`
  as the conjugate of `homologyComparison F Z q`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.EdgeCompat

universe vA uA vB uB

/-- If `a ≫ m = a'`, then `a ≫ m ≫ r = a' ≫ r`. -/
theorem comp_comp_eq_comp {C : Type*} [Category C] {X Y Y' W : C} {a : X ⟶ Y} {m : Y ⟶ Y'}
    {a' : X ⟶ Y'} (h : a ≫ m = a') (r : Y' ⟶ W) : a ≫ m ≫ r = a' ≫ r := by
  rw [← assoc, h]

/-- Reassociation of the tail of a five-fold composite:
`a ≫ b ≫ (c ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e`. -/
theorem comp_comp_comp_assoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) :
    a ≫ b ≫ (c ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  rw [assoc]

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (q : ℤ) (Z : CochainComplex A ℤ)

/-- The isomorphism of the `Localization.Lifting` instance of `L ⋙ G` along `L` is the identity. -/
private theorem lifting_iso_compLeft {C₁ D₁ E₁ : Type*} [Category C₁] [Category D₁] [Category E₁]
    (L : C₁ ⥤ D₁) (W : MorphismProperty C₁) (G : D₁ ⥤ E₁) :
    Localization.Lifting.iso L W (L ⋙ G) G = Iso.refl _ := rfl

/-- The component of `homotopyHomologyComparisonToDerived F q` at the image `Q Z` of a complex `Z`
is `homologyComparison F Z q` conjugated by the factorisations of the cohomology functor, with
the cohomology functor applied to the identification
`CategoryTheory.Functor.mapHomotopyCategoryFactors` of `K(F)(Q Z)` with `Q(F Z)` kept as a
factor. -/
theorem homotopyHomologyComparisonToDerived_app_quotient_crossing :
    (homotopyHomologyComparisonToDerived F q).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) =
      (DerivedCategory.homologyFunctorFactorsh B q).hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) ≫
        (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q).map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app Z) ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
        homologyComparison F Z q ≫
        F.map ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).inv.app Z) ≫
        F.map ((DerivedCategory.homologyFunctorFactorsh A q).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) := by
  rw [homotopyHomologyComparisonToDerived, homologyComparisonOnHomotopy]
  simp only [Functor.comp_obj, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, homologyComparisonNatTrans, Functor.isoWhiskerRight_inv, assoc,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso, Iso.refl_hom,
    NatTrans.id_app, Functor.associator_inv_app, Functor.whiskerRight_app, id_comp, Iso.refl_inv,
    comp_id, NatIso.cancel_natIso_hom_left]
  exact comp_comp_comp_assoc _ _ _ _ _

omit [HasDerivedCategory A] [PreservesFiniteLimits F] in
/-- The component of `DerivedCategory.homologyFunctorFactorsh` at `K(F)(Q Z)`, followed by the
cohomology functor applied to the identification of `K(F)(Q Z)` with `Q(F Z)`, is its component
at `Q(F Z)`. -/
theorem factorsh_hom_app_comp_map_mapHomotopyCategoryFactors :
    (DerivedCategory.homologyFunctorFactorsh B q).hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) ≫
        (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q).map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app Z) =
      (DerivedCategory.homologyFunctorFactorsh B q).hom.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) :=
  have hQ : DerivedCategory.Qh.map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app Z) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hid : (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor B q).map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app Z) = 𝟙 _ :=
    Eq.trans (congrArg (fun g => (DerivedCategory.homologyFunctor B q).map g) hQ)
      ((DerivedCategory.homologyFunctor B q).map_id _)
  Eq.trans
    (((DerivedCategory.homologyFunctorFactorsh B q).hom.naturality
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app Z)).symm)
    (Eq.trans
      (congrArg (fun g => g ≫ (DerivedCategory.homologyFunctorFactorsh B q).hom.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))) hid)
      (id_comp _))

/-- For a cochain complex `Z` in the source of
the left exact `F`,

> `(homotopyHomologyComparisonToDerived F q).app (Q Z)`

is the comparison `H^q(F Z) ⟶ F(H^q Z)` of complexes, conjugated by the factorisations of the
cohomology functor through the homotopy category and through the derived category. -/
theorem homotopyHomologyComparisonToDerived_app_quotient :
    (homotopyHomologyComparisonToDerived F q).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) =
      (DerivedCategory.homologyFunctorFactorsh B q).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
        homologyComparison F Z q ≫
        F.map ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).inv.app Z) ≫
        F.map ((DerivedCategory.homologyFunctorFactorsh A q).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) :=
  Eq.trans (homotopyHomologyComparisonToDerived_app_quotient_crossing F q Z)
    (comp_comp_eq_comp (factorsh_hom_app_comp_map_mapHomotopyCategoryFactors F q Z) _)

end Stacks.EdgeCompat

end
