module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleDerived
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartFibreStandardResolution

/-!
# Derived lower shriek of modules on the polynomial charts of a scheme, by standard resolutions

Let `Λ` be a ring, let `X` be a scheme over `Λ`, let `C_{X/Λ}` be its category of polynomial
charts, fibred over the small Zariski site of `X` with the inherited topology, and let
`π : Sh(C_{X/Λ}) ⟶ Sh(X_Zar)` be the induced morphism of topoi. For an open `U ⊆ X` let `P_{•,U}`
be the standard resolution of `𝒪_X(U)` over `Λ` and `A_{•,U} = Spec(P_{•,U})`. This file proves
Stacks 08VB at module coefficients: for a sheaf of rings `O` on `X_Zar` (for instance `𝒪_X`,
presented in the coefficient universe by `liftedStructureSheaf`) and a sheaf `M` of
`π⁻¹O`-modules, `Lπ_!(M)` is the complex of sheaves of `O`-modules whose term in degree `-n` is
the sheafification of `U ↦ M(A_{n,U})`, and `L_nπ_!(M)` is the sheafification of
`U ↦ H_n(M(A_{•,U}))`.

The abelian statement is `standardResolutionChart_computes_derivedLowerShriek` in
`StacksFrontier/Cotangent/StandardResolutionChartsLowerShriek.lean`, which carries the tag; the
computation used here is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/PointResolution/ModuleDerived.lean`,
which holds for an arbitrary fibred category over a site with a fibrewise point resolution.

## Main results

* `AlgebraicGeometry.PolynomialChart.standardResolutionChart_computes_derivedModuleLowerShriek`:
  Stacks 08VB at module coefficients.

## References

* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology.DerivedLowerShriek

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against modules in the pinned universe `u + 1`;
the structures used here are those of the fibred category situation. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.PolynomialChart

open Stacks.Sites.FibredCategory.FibredCategorySituation

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 08VB at module coefficients, on the polynomial charts of a scheme.** Let `X` be a
scheme over a ring `Λ`, for an open `U ⊆ X` let `P_{•,U}` be the standard resolution of `𝒪_X(U)`
over `Λ` and `A_{•,U} = Spec(P_{•,U})`, the functorial cosimplicial charts
`standardResolutionChart`, let `O` be a sheaf of rings on `X_Zar` (such as `𝒪_X`) and let `M` be
a sheaf of `π⁻¹O`-modules on `C_{X/Λ}`. Then:

1. `Lπ_!(M)` is isomorphic in `D(O)` to the complex of sheaves of `O`-modules whose term in
   degree `-n` is the sheafification of `U ↦ M(A_{n,U})`;
2. the underlying complex of abelian sheaves of that complex is the one of the abelian statement,
   the sheafification of the complex of abelian presheaves `U ↦ M(A_{•,U})`;
3. `L_nπ_!(M) = H^{-n}(Lπ_! M)` is the sheaf of `O`-modules associated to
   `U ↦ H_n(M(A_{•,U}))`. -/
theorem standardResolutionChart_computes_derivedModuleLowerShriek
    (O : Sheaf (fibredCategorySituation Λ X structureMap).base.J RingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      (inverseImageRing (fibredCategorySituation Λ X structureMap).topology
        (fibredCategorySituation Λ X structureMap).base.J
          (fibredCategorySituation Λ X structureMap).p O)) :
    Nonempty (((fibredCategorySituation Λ X structureMap).derivedModuleLowerShriek O).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj (modulePointSheafComplex O
        (standardResolutionChart_comp_whiskeringRight Λ X structureMap) M)) ∧
    Nonempty (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (modulePointSheafComplex O (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
          M) ≅
      (fibredCategorySituation Λ X structureMap).pointSheafComplex
        (standardResolutionChart Λ X structureMap :
          (fibredCategorySituation Λ X structureMap).base.C ⥤
            CosimplicialObject (fibredCategorySituation Λ X structureMap).C) M.val.presheaf) ∧
    ∀ n : ℕ, Nonempty ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
        (((fibredCategorySituation Λ X structureMap).derivedModuleLowerShriek O).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (PresheafOfModules.sheafification (𝟙 O.obj)).obj
        ((((fibredCategorySituation Λ X structureMap).modulePointMooreComplex
          (standardResolutionChart_comp_whiskeringRight Λ X structureMap) O.obj).obj
            M.val).homology n)) :=
  ⟨nonempty_derivedModuleLowerShriekIso O
      (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
      (exists_homotopyEquivalences_standardResolutionChart Λ X structureMap) M,
    ⟨modulePointSheafComplexForgetIso O
      (standardResolutionChart_comp_whiskeringRight Λ X structureMap) M⟩,
    fun n => nonempty_derivedModuleLowerShriekHomologyIso O
      (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
      (exists_homotopyEquivalences_standardResolutionChart Λ X structureMap) M n⟩

end AlgebraicGeometry.PolynomialChart
