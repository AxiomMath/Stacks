module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleDerived
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceStandardResolution

/-!
# Derived lower shriek of modules on the polynomial charts of an algebraic space

Let `Λ` be a ring, let `X` be an algebraic space over `Λ`, let `C_{X/Λ}` be its category of
polynomial charts, fibred over the small étale site `X_étale` with the inherited topology, and let
`π : Sh(C_{X/Λ}) ⟶ Sh(X_étale)` be the induced morphism of topoi. For an object `U` of `X_étale`
let `P_{•,U}` be the standard resolution of `𝒪_X(U)` over `Λ` and `𝐀_{•,U} = Spec(P_{•,U})`.
This file is Stacks 08VL at module coefficients. For a sheaf of rings `O` on `X_étale` and a
sheaf `M` of `π⁻¹O`-modules, `Lπ_!(M)` is the complex of sheaves of `O`-modules whose term in
degree `-n` is the sheafification of `U ↦ M(𝐀_{n,U})`. Moreover `L_nπ_!(M)` is the
sheafification of `U ↦ H_n(M(𝐀_{•,U}))`.

The abelian statement is `standardResolutionChart_computes_derivedAbelianLowerShriek`, which
carries the tag. The computation used here holds for an arbitrary fibred category over a site
with a fibrewise point resolution, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/PointResolution/ModuleDerived.lean`.

## Main results

All names are in the namespace `AlgebraicGeometry.Space.PolynomialChart`.

* `standardResolutionChart_computes_derivedModuleLowerShriek`: Stacks 08VL at module coefficients.

## References

* [Stacks Project, Tag 08VL](https://stacks.math.columbia.edu/tag/08VL)
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

namespace AlgebraicGeometry.Space.PolynomialChart

open Stacks.Sites.FibredCategory.FibredCategorySituation

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 08VL at module coefficients.** Let `X` be an algebraic space over a ring `Λ`, for
an object `U` of `X_étale` let `P_{•,U}` be the standard resolution of `𝒪_X(U)` over `Λ` and
`𝐀_{•,U} = Spec(P_{•,U})`, the functorial cosimplicial charts `standardResolutionChart`. Let `O`
be a sheaf of rings on `X_étale` and let `M` be a sheaf of `π⁻¹O`-modules on `C_{X/Λ}`. Then:

1. `Lπ_!(M)` is isomorphic in `D(O)` to the complex of sheaves of `O`-modules whose term in
   degree `-n` is the sheafification of `U ↦ M(𝐀_{n,U})`;
2. the underlying complex of abelian sheaves of that complex is the sheafification of the complex
   of abelian presheaves `U ↦ M(𝐀_{•,U})`;
3. `L_nπ_!(M) = H^{-n}(Lπ_! M)` is the sheaf of `O`-modules associated to
   `U ↦ H_n(M(𝐀_{•,U}))`. -/
theorem standardResolutionChart_computes_derivedModuleLowerShriek
    (O : Sheaf (fibredCategorySituation Λ B hS X hX).base.J RingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      (inverseImageRing (fibredCategorySituation Λ B hS X hX).topology
        (fibredCategorySituation Λ B hS X hX).base.J
          (fibredCategorySituation Λ B hS X hX).p O)) :
    Nonempty (((fibredCategorySituation Λ B hS X hX).derivedModuleLowerShriek O).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj (modulePointSheafComplex O
        (standardResolutionChart_comp_whiskeringRight Λ B hS X hX) M)) ∧
    Nonempty (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (modulePointSheafComplex O (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
          M) ≅
      (fibredCategorySituation Λ B hS X hX).pointSheafComplex
        (standardResolutionChart Λ B hS X hX :
          (fibredCategorySituation Λ B hS X hX).base.C ⥤
            CosimplicialObject (fibredCategorySituation Λ B hS X hX).C) M.val.presheaf) ∧
    ∀ n : ℕ, Nonempty ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
        (((fibredCategorySituation Λ B hS X hX).derivedModuleLowerShriek O).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (PresheafOfModules.sheafification (𝟙 O.obj)).obj
        ((((fibredCategorySituation Λ B hS X hX).modulePointMooreComplex
          (standardResolutionChart_comp_whiskeringRight Λ B hS X hX) O.obj).obj
            M.val).homology n)) :=
  ⟨nonempty_derivedModuleLowerShriekIso O
      (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
      (exists_homotopyEquivalences_standardResolutionChart Λ B hS X hX) M,
    ⟨modulePointSheafComplexForgetIso O
      (standardResolutionChart_comp_whiskeringRight Λ B hS X hX) M⟩,
    fun n => nonempty_derivedModuleLowerShriekHomologyIso O
      (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
      (exists_homotopyEquivalences_standardResolutionChart Λ B hS X hX) M n⟩

end AlgebraicGeometry.Space.PolynomialChart

end
