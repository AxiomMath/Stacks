module

public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartFibreStandardResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Derived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.FibreHomology
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek on the polynomial charts of a scheme, by standard resolutions

Let `Λ` be a ring, let `X` be a scheme over `Λ`, let `C_{X/Λ}` be its category of polynomial
charts, fibred over the small Zariski site of `X` with the inherited topology, and let
`π : Sh(C_{X/Λ}) ⟶ Sh(X_Zar)` be the induced morphism of topoi. For an open `U ⊆ X` let `P_{•,U}`
be the standard resolution of `𝒪_X(U)` over `Λ` and `A_{•,U} = Spec(P_{•,U})`. This file proves
Stacks 08VB:

* `A_{•,U}` is a cosimplicial object of the fibre category of `C_{X/Λ}` over `U`, which is the
  category `C_{𝒪_X(U)/Λ}`, and it is a point resolution of it in the sense of Stacks 08Q9;
* for an abelian sheaf `F` on `C_{X/Λ}` the cohomology of the complex of presheaves
  `U ↦ F(A_{•,U})` computes the homology of `F` on the fibre categories;
* the sheafification of that cohomology is `L_nπ_!(F)`, and the complex of sheaves whose term in
  degree `-n` is the sheafification of `U ↦ F(A_{n,U})` computes `Lπ_!(F)`.

The charts, their functoriality in `U` and the complex of presheaves are in
`StacksFrontier/Cotangent/StandardResolutionCharts.lean`; the identification of the fibres and the
point-resolution property, which is Stacks 08PT transported along that identification, are in
`StacksFrontier/Cotangent/SheavesOfRings/PolynomialChartFibreStandardResolution.lean`; the
computation of `Lπ_!` is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/PointResolution/`, which holds for an
arbitrary fibred category over a site with fibre products and a fibrewise point resolution.

## Main results

* `AlgebraicGeometry.PolynomialChart.standardResolutionChart_computes_derivedLowerShriek`:
  **Stacks 08VB**.

## Implementation notes

The homology of a fibre category is taken on its small model `AsSmall` in the universe of the
sections, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/PointResolution/FibreHomology.lean`:
the fibres of `C_{X/Λ}` have objects in `Type (u + 1)` and morphisms in `Type u`.

## References

* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u

namespace AlgebraicGeometry.PolynomialChart

open Stacks.Sites.FibredCategory.FibredCategorySituation

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-- The Zariski site of `X` has fibre products. -/
instance hasPullbacks_fibredCategorySituation_base :
    HasPullbacks (fibredCategorySituation Λ X structureMap).base.C :=
  inferInstanceAs (HasPullbacks X.Opens)

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 08VB.** Let `X` be a scheme over a ring `Λ`, and for an open `U ⊆ X` let `P_{•,U}` be
the standard resolution of `𝒪_X(U)` over `Λ` and `A_{•,U} = Spec(P_{•,U})`, the functorial
cosimplicial charts `standardResolutionChart`. Then:

1. the fibre category of `C_{X/Λ}` over `U` is `C_{𝒪_X(U)/Λ}`, and `A_{•,U}` is a cosimplicial
   object of it (`standardResolutionFibreChart`) which is as in Stacks 08Q9: every simplicial set
   `Mor(A_{•,U}, W)` is homotopy equivalent to a point;
2. for every abelian sheaf `F` on `C_{X/Λ}` the cohomology groups of the complex of presheaves
   `U ↦ F(A_{•,U})` compute the homology of `F` on the fibre category over `U`;
3. their sheafification computes `L_nπ_!(F)`;
4. the complex of sheaves whose term in degree `-n` is the sheafification of `U ↦ F(A_{n,U})`
   computes `Lπ_!(F)`. -/
@[stacks 08VB]
theorem standardResolutionChart_computes_derivedLowerShriek :
    (∀ U : X.Opens, Nonempty ((openFunctor (Λ := Λ) (X := X)
        (structureMap := structureMap)).Fiber U ≌
      CommAlgCat.polynomialSite Λ ((openAlgebra Λ X structureMap).obj (op U)))) ∧
    (∀ (U : X.Opens) (W : (openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).Fiber U),
      ∃ f : (standardResolutionFibreChart Λ X structureMap U).op ⋙ yoneda.obj W ⟶
          (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
        SimplicialObject.homotopyEquivalences (Type u) f) ∧
    (∀ (F : Sheaf (fibredCategorySituation Λ X structureMap).topology AddCommGrpCat.{u + 1})
      (U : (fibredCategorySituation Λ X structureMap).base.C) (n : ℕ),
      Nonempty (((((fibredCategorySituation Λ X structureMap).pointMooreComplex
          (standardResolutionChart Λ X structureMap :
            (fibredCategorySituation Λ X structureMap).base.C ⥤
              CosimplicialObject (fibredCategorySituation Λ X structureMap).C)).obj
            F.obj).homology n).obj (op U) ≅
        Stacks.CategoryHomology.categoryHomology.{u + 1, u + 1}
          ((fibredCategorySituation Λ X structureMap).smallFiberRestriction F.obj U) n)) ∧
    (∀ (F : Sheaf (fibredCategorySituation Λ X structureMap).topology AddCommGrpCat.{u + 1})
      (n : ℕ),
      Nonempty ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
          ((fibredCategorySituation Λ X structureMap).derivedAbelianLowerShriek.obj
            ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
        (presheafToSheaf (fibredCategorySituation Λ X structureMap).base.J
          AddCommGrpCat.{u + 1}).obj
          ((((fibredCategorySituation Λ X structureMap).pointMooreComplex
            (standardResolutionChart Λ X structureMap :
              (fibredCategorySituation Λ X structureMap).base.C ⥤
                CosimplicialObject (fibredCategorySituation Λ X structureMap).C)).obj
              F.obj).homology n))) ∧
    (∀ F : Sheaf (fibredCategorySituation Λ X structureMap).topology AddCommGrpCat.{u + 1},
      Nonempty ((fibredCategorySituation Λ X structureMap).derivedAbelianLowerShriek.obj
          ((DerivedCategory.singleFunctor _ 0).obj F) ≅
        DerivedCategory.Q.obj ((fibredCategorySituation Λ X structureMap).pointSheafComplex
          (standardResolutionChart Λ X structureMap :
            (fibredCategorySituation Λ X structureMap).base.C ⥤
              CosimplicialObject (fibredCategorySituation Λ X structureMap).C) F.obj))) :=
  ⟨fun U => ⟨fibreEquivalence Λ X structureMap U⟩,
    fun U W => exists_homotopyEquivalences_standardResolutionFibreChartMor Λ X structureMap U W,
    fun F U n => ⟨categoryHomologyFiberIso _ (standardResolutionChart_comp_whiskeringRight Λ X
      structureMap) (exists_homotopyEquivalences_standardResolutionChart Λ X structureMap)
      F.obj U n⟩,
    fun F n => nonempty_derivedAbelianLowerShriekHomologyIso _
      (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
      (exists_homotopyEquivalences_standardResolutionChart Λ X structureMap) F n,
    fun F => nonempty_derivedAbelianLowerShriekIso _
      (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
      (exists_homotopyEquivalences_standardResolutionChart Λ X structureMap) F⟩

end AlgebraicGeometry.PolynomialChart
