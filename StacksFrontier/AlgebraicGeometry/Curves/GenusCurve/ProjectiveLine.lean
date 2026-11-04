module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The genus of the projective line is zero

The genus of a scheme over `k` is `dim_k H¹(X, 𝒪_X)` ([Stacks, Tag 0BY7]). For
`𝐏¹_k = Proj k[T₀, T₁]` the group `H¹(𝐏¹_k, 𝒪)` vanishes by Serre's computation of the
cohomology of projective space ([Stacks, Tag 01XT]), so the genus of `𝐏¹_k` is zero.

## Main results

* `Stacks.Curves.isZero_structureSheafCohomology_projToSpecCoeff_one`: `H¹(𝐏¹_k, 𝒪) = 0` in the
  spelling the genus is defined from.
* `Stacks.Curves.genus_projToSpecCoeff_one`: **the genus of `𝐏¹_k` is zero.**

## References

* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjEulerSequence (twistingSheafZeroIsoUnit)
open Stacks.ProjectiveSpace.Cohomology (isZero_lineCohomology_one_of_neg_one_le)

universe u

namespace Stacks.Curves

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

/-- The first cohomology group `H¹(𝐏¹_k, 𝒪)` of the structure sheaf of the projective line,
as a `k`-module via pushforward to `Spec k`, is zero. -/
@[sga "7 XXII 6.2" "special case"]
theorem isZero_structureSheafCohomology_projToSpecCoeff_one (k : Type u) [Field k] :
    IsZero (structureSheafCohomology (projToSpecCoeff k 1) 1) := by
  have hunit : IsZero (((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (polyGrading k 1)) ⊤).rightDerived 1).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k 1)).ringCatSheaf)) :=
    (isZero_lineCohomology_one_of_neg_one_le k (d := 0) (by norm_num)).of_iso
      (((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading k 1)) ⊤).rightDerived 1).mapIso
          (twistingSheafZeroIsoUnit (polyGrading k 1))).symm
  refine IsZero.of_iso ?_
    (structureSheafCohomologyIsoCohomologyOverField k (projToSpecCoeff k 1) 1)
  rw [ModuleCat.isZero_iff_subsingleton] at hunit ⊢
  exact hunit

/-- The genus of the projective line `𝐏¹_k` is zero. -/
@[simp] theorem genus_projToSpecCoeff_one (k : Type u) [Field k] :
    genus (projToSpecCoeff k 1) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (isZero_structureSheafCohomology_projToSpecCoeff_one k)
  exact Module.finrank_zero_of_subsingleton

end Stacks.Curves

end
