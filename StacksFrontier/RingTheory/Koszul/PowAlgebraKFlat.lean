module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.RingTheory.Koszul.CohomologicalDifferentialGradedAlgebra

/-!
# The Koszul differential graded algebra is K-flat

Let `f₁, …, f_r` be elements of a commutative ring `R` and let `K_n` be the Koszul differential
graded algebra with `d ξᵢ = fᵢ ^ n`. Its underlying cochain complex of `R`-modules has the `k`-th
exterior power of `Rʳ` in cohomological degree `-k` and nothing in positive degrees, so it is a
bounded above complex of flat `R`-modules and therefore K-flat (Tag 064K).

K-flatness of the complex underlying a differential graded algebra `C` is the hypothesis of
`DifferentialGraded.tensorPreservesQuasiIso_baseChangeBimodule`, of
`DifferentialGraded.isIso_derivedTensorBaseChangeComparison_of_kFlat` (Tag 09S4) and of
`DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlat`; this file discharges it for the
Koszul algebras.

## Main results

* `Koszul.flat_cohomologicalExteriorGrade`: every graded piece of the cohomological exterior
  algebra of `Rʳ` is a flat `R`-module.
* `Koszul.powAlgebra_kFlat`: the complex underlying `K_n` is K-flat.

## Implementation notes

The graded pieces are given by a case split on the sign of the degree rather than uniformly, so
neither flatness nor the vanishing in positive degrees is found by instance search; both are
proved by rewriting with `Koszul.cohomologicalExteriorGrade_of_nonpos` and
`Koszul.cohomologicalExteriorGrade_of_pos` first. In non-positive degree the piece is an exterior
power of the free module `Rʳ`, hence free, hence flat; in positive degree it is the zero
submodule.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open CategoryTheory DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ}

/-- Every graded piece of the cohomological exterior algebra of `Rʳ` is a flat `R`-module: in
non-positive degree `-k` it is the `k`-th exterior power of a free module, and in positive degree
it is the zero submodule. -/
theorem flat_cohomologicalExteriorGrade (R : Type u) [CommRing R] (r : ℕ) (i : ℤ) :
    Module.Flat R (cohomologicalExteriorGrade R (Fin r → R) i) := by
  rcases le_or_gt i 0 with hi | hi
  · rw [cohomologicalExteriorGrade_of_nonpos R (Fin r → R) hi]
    infer_instance
  · rw [cohomologicalExteriorGrade_of_pos R (Fin r → R) hi]
    infer_instance

/-- The complex underlying `K_n` vanishes in positive cohomological degrees. -/
theorem isZero_powAlgebra_toCochainComplex_X (f : Fin r → R) (n : ℕ) {i : ℤ} (hi : 0 < i) :
    Limits.IsZero ((regularModule (powAlgebra f n)).toCochainComplex.X i) := by
  rw [toCochainComplex_X, ModuleCat.isZero_of_iff_subsingleton,
    show (regularModule (powAlgebra f n)).grading i = ⊥ from powAlgebra_grading_of_pos f n hi]
  infer_instance

/-- The complex underlying `K_n` is concentrated in non-positive cohomological degrees. -/
instance instIsStrictlyLEPowAlgebraToCochainComplex (f : Fin r → R) (n : ℕ) :
    CochainComplex.IsStrictlyLE (regularModule (powAlgebra f n)).toCochainComplex 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun _ hi =>
    isZero_powAlgebra_toCochainComplex_X f n hi

/-- Every term of the complex underlying `K_n` is a flat `R`-module. -/
instance instFlatPowAlgebraToCochainComplexX (f : Fin r → R) (n : ℕ) (i : ℤ) :
    Module.Flat R ((regularModule (powAlgebra f n)).toCochainComplex.X i) :=
  flat_cohomologicalExteriorGrade R r i

/-- **The complex underlying the Koszul differential graded algebra `K_n` is K-flat.** It is a
bounded above complex of flat `R`-modules, so Tag 064K applies. -/
theorem powAlgebra_kFlat (f : Fin r → R) (n : ℕ) :
    CochainComplex.KFlat.{u, u} (regularModule (powAlgebra f n)).toCochainComplex :=
  CochainComplex.KFlat.kFlat_of_flat _ 0

end Koszul

end
