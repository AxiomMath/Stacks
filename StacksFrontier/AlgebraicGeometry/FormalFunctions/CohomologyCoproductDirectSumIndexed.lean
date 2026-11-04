module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyCoproductDirectSum

/-!
# `H^p(X, ∐ᵢ Fᵢ) ≅ ⨁ᵢ H^p(X, Fᵢ)` for an index type in `Type 0`

For a quasi-compact quasi-separated scheme `X` and a family `(Fᵢ)` of `𝒪_X`-modules indexed by a
type `ι : Type` with decidable equality, this file gives the comparison of [Stacks, Tag 01FF]
between the cohomology of the coproduct and the direct sum of the cohomologies.

## Main results

* `Stacks.Cohomology.CoproductDirectSum.preservesColimitsOfShape_discrete_of_type`: cohomology of
  a quasi-compact quasi-separated scheme commutes with `ι`-indexed direct sums.
* `Stacks.Cohomology.CoproductDirectSum.indexedCohomologyCoprodDirectSumIso`: the comparison
  `H^p(X, ∐ᵢ Fᵢ) ≅ ⨁ᵢ H^p(X, Fᵢ)` over `Γ(X, ⊤)`.
* `Stacks.Cohomology.CoproductDirectSum.map_sigmaι_comp_indexedCohomologyCoprodDirectSumIso_hom`:
  the comparison is the one determined by the coproduct injections.

## Implementation notes

The index type is `ι : Type`, not `ι : Type u`, so that `DirectSum ι β` stays in the module
universe.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.Cohomology.CoproductDirectSum

open Stacks.AlgebraicGeometry.TopDegreeBaseChange
  (preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections) in
/-- **Cohomology of a quasi-compact quasi-separated scheme commutes with direct sums indexed by
a type in `Type 0`.** -/
public theorem preservesColimitsOfShape_discrete_of_type (X : Scheme.{u})
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (p : ℕ) (ι : Type) :
    PreservesColimitsOfShape (Discrete ι) ((moduleGlobalSections X).rightDerived p) :=
  have := preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X p (ULift.{u} ι)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift : ULift.{u} ι ≃ ι)) _

/-- The direct sum of the cohomologies of an `ι`-indexed family is a colimit cocone on the family
composed with `H^p`. -/
public def indexedCohomologyDirectSumCoconeIsColimit (X : Scheme.{u}) (p : ℕ) {ι : Type}
    [DecidableEq ι] (F : ι → X.Modules) :
    IsColimit ((Cocone.precompose
      (Discrete.compNatIsoDiscrete F ((moduleGlobalSections X).rightDerived p)).hom).obj
        (directSumCofan fun n => ((moduleGlobalSections X).rightDerived p).obj (F n))) :=
  (IsColimit.precomposeHomEquiv
    (Discrete.compNatIsoDiscrete F ((moduleGlobalSections X).rightDerived p)) _).symm
      (directSumCofanIsColimit fun n => ((moduleGlobalSections X).rightDerived p).obj (F n))

/-- **`H^p(X, ∐ᵢ Fᵢ) ≅ ⨁ᵢ H^p(X, Fᵢ)`** over `Γ(X, ⊤)`, for an index type in `Type 0`. -/
public def indexedCohomologyCoprodDirectSumIso (X : Scheme.{u}) [CompactSpace (X : Type u)]
    [QuasiSeparatedSpace (X : Type u)] (p : ℕ) {ι : Type} [DecidableEq ι] (F : ι → X.Modules) :
    ((moduleGlobalSections X).rightDerived p).obj (∐ F) ≅
      ModuleCat.of Γ(X, ⊤)
        (⨁ n : ι, (((moduleGlobalSections X).rightDerived p).obj (F n) : Type u)) := by
  haveI := preservesColimitsOfShape_discrete_of_type X p ι
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitOfPreserves ((moduleGlobalSections X).rightDerived p) (coproductIsCoproduct F))
    (indexedCohomologyDirectSumCoconeIsColimit X p F)

/-- **The comparison is the one determined by the coproduct injections**: `H^p(X, ιₙ)` followed
by it is `DirectSum.lof n`. -/
public theorem map_sigmaι_comp_indexedCohomologyCoprodDirectSumIso_hom (X : Scheme.{u})
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (p : ℕ) {ι : Type}
    [DecidableEq ι] (F : ι → X.Modules) (n : ι) :
    ((moduleGlobalSections X).rightDerived p).map (Sigma.ι F n) ≫
        (indexedCohomologyCoprodDirectSumIso X p F).hom =
      ModuleCat.ofHom (DirectSum.lof Γ(X, ⊤) ι
        (fun n => (((moduleGlobalSections X).rightDerived p).obj (F n) : Type u)) n) := by
  have := preservesColimitsOfShape_discrete_of_type X p ι
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves ((moduleGlobalSections X).rightDerived p) (coproductIsCoproduct F))
    (indexedCohomologyDirectSumCoconeIsColimit X p F) ⟨n⟩
  simpa [indexedCohomologyCoprodDirectSumIso, directSumCofan] using h

end Stacks.Cohomology.CoproductDirectSum

end
