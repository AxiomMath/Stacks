module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GradedDimensions
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpExceptionalDualizingGorenstein
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSupplement
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimensionSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpExceptionalDualizingSupplement

/-!
# The embedding dimension of a Gorenstein rational surface singularity

Section 54.12 of the source opens with `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1` for a two-dimensional
Gorenstein rational surface singularity, and everything in `RationalDoublePoints/` rests on it.
`RationalDoublePoints/GradedDimensions.lean` proves the unconditional half,

`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = n · (dim_κ(𝔪/𝔪²) − 1) + 1`,

so what the source's `2n + 1` adds is the single number `dim_κ(𝔪/𝔪²) = 3`, equivalently
`deg 𝒪_E(1) = 2`. **This file reduces that number to one isomorphism of modules on the
exceptional curve** — the same isomorphism
`BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_exceptionalDualizingIso`
of `…/RationalSingularities/BlowUpExceptionalDualizing.lean` carries, with no quantifier in it —
and proves everything else of the computation.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_add` and
  `.invertibleCurveDegree_curveTwistSheaf_eq_zsmul`: **`deg 𝒪_E(a + b) = deg 𝒪_E(a) + deg 𝒪_E(b)`
  and `deg 𝒪_E(n) = n · deg 𝒪_E(1)` for all *integers***, extending
  `AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_eq_nsmul`, which is
  stated for natural numbers only. This is what makes the inverse twist `𝒪_E(-1)` — the one the
  dualizing sheaf of `E` is isomorphic to — carry degree `−deg 𝒪_E(1)`.
* `AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_int`:
  **`deg 𝒪_E(n) = n · (dim_κ(𝔪/𝔪²) − 1)`** for every integer `n`.
* `AlgebraicGeometry.BlowUpDualizing`
  `.finrank_cotangentSpace_eq_three_of_invertibleCurveDegree_neg_one` and
  `.finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_neg_one`:
  **`dim_κ(𝔪/𝔪²) = 3` from `deg 𝒪_E(-1) = −2`**, and from the two cohomology dimensions
  `h⁰(E, 𝒪_E(-1)) = 0` and `h¹(E, 𝒪_E(-1)) = 1` that duality over `κ` delivers.
* `AlgebraicGeometry.BlowUpDualizing.forall_finrank_gradedPiece_eq_two_mul_add_one_iff`:
  **`(∀ n, dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1) ↔ dim_κ(𝔪/𝔪²) = 3`**, the two spellings in which the input
  is taken as a hypothesis across `RationalDoublePoints/`.
* `AlgebraicGeometry.BlowUpDualizing.finrank_cotangentSpace_eq_three_of_exceptionalDualizingIso`:
  **`dim_κ(𝔪/𝔪²) = 3`, granted that `ω_E = H¹(a(ω_X))` is
  `Stacks.Duality.dualizingSheafOverField` of the structure morphism `E ⟶ Spec(κ)`.**
* `.finrank_gradedPiece_eq_two_mul_add_one_of_exceptionalDualizingIso`,
  `.exists_generators_and_quadraticRelation_of_exceptionalDualizingIso` and
  `.exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear_of_exceptionalDualizingIso`: the three
  results of `RationalDoublePoints/GradedDimensions.lean` that take `dim_κ(𝔪/𝔪²) = 3` in a
  binder, with that binder replaced by the one isomorphism.

## The argument

`invertibleCurveDegree` of an invertible module on `E` is `χ(L) − χ(𝒪_E)`, and both Euler
characteristics collapse to `h⁰ − h¹` because `E` is one-dimensional. The degree of a tensor
product of invertible modules is the sum of the degrees ([Stacks, Tag 0AYX], proved with no
hypothesis beyond properness and the dimension bound) and `𝒪_E(a) ⊗ 𝒪_E(b) ≅ 𝒪_E(a + b)` for
all *integers* `a`, `b` — `AlgebraicGeometry.BlowUpDualizing.curveTwistSheafAddIso` is already
stated over `ℤ` — so the degree is additive over `ℤ` and `n ↦ deg 𝒪_E(n)` is `n · deg 𝒪_E(1)` by
induction in both directions. With `deg 𝒪_E(1) = dim_κ(𝔪/𝔪²) − 1` (clause (3) of
[Stacks, Tag 0B63]) that reads `deg 𝒪_E(-1) = 1 − dim_κ(𝔪/𝔪²)`, so `deg 𝒪_E(-1) = −2` is
exactly `dim_κ(𝔪/𝔪²) = 3`.

For the Gorenstein singularity, `ω_E ≅ 𝒪_E(-1)`
(`AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_curveTwistSheaf`),
and granted the isomorphism of `ω_E` with `Stacks.Duality.dualizingSheafOverField` of
`E ⟶ Spec(κ)` the two cohomology dimensions of `𝒪_E(-1)` are read off duality over `κ`, which
is proved with nothing carried: `AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one`
gives `h⁰(ω_E) = h¹(E, 𝒪_E) = 0`, and `AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one`
— clause 0B5B, read off clause (4) of [Stacks, Tag 0BS2] — gives `h¹(ω_E) = 1`. So
`deg 𝒪_E(-1) = (0 − 1) − (1 − 0) = −2`.

## What is still carried here, and where `eE` is discharged

The hypothesis `eE` is not discharged in this file, and nothing in this file is tagged. **It is
discharged elsewhere**: for a `ω_X` normalized in the sense of [Stacks, Remark 0B4R] — which is
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`, strictly stronger than
the degree-zero `NormalizedDualizingModule` taken below — it is `AlgebraicGeometry`
`.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField` of
`…/Duality/ExceptionalDualizingSheafIdentification.lean`, and
`RationalDoublePoints/EmbeddingDimensionGorenstein.lean` uses it to prove
`dim_κ(𝔪/𝔪²) = 3` carrying only that normalized `ω_X`. The route taken there does not pass
through the global generation `G` below either.

The proof of `eE` uses the cohomological reading of [Stacks, Tag 0A7M] together with
[Stacks, Tag 0A9F], in place of the reading of [Stacks, Tag 0AA2] at the level of stalk modules,
the closed point being affine.

A normalization argument from [Stacks, Tag 0A7F] does **not** replace `eE`, for three separate
reasons.

* [Stacks, Tag 0A7F] is formalized only over a Noetherian *ring*
  (`Dualizing.IsDualizingComplex.exists_iso_derivedTensorProduct_invertible`, whose attribute
  records the restriction to the affine case). There is no scheme-level uniqueness of dualizing
  complexes in this development, so there is nothing to apply to `E`.
* One of its two inputs is missing anyway: that
  `Stacks.Duality.dualizingComplexOverField` of `E ⟶ Spec(κ)` is a dualizing complex is not
  proved — what is proved about `ω_E` in that direction is
  `AlgebraicGeometry.BlowUpDualizing.isDualizingModule_exceptionalDualizingModule`, about `ω_E`
  and not about the sheaf it has to be compared with.
* Even granted both, degree bookkeeping cannot close the gap. The conclusion of
  [Stacks, Tag 0A7F] is `ω_E ≅ ω ⊗ L[m]` with `L` invertible; two modules in degree zero force
  `m = 0`, and then writing `d` for the unknown `deg 𝒪_E(1)` the results above give
  `deg ω_E = −d` and `deg ω = −2`, hence `deg L = 2 − d`. Every `d ≥ 2` is consistent with
  that, so the twist is not pinned down by any degree or rank count on `E`. This is the same
  phenomenon as the counterexample recorded in
  `…/Curves/VanishingResults/DualizingTwist.lean`, where `𝒪(-7)` on `ℙ¹` is a dualizing module
  for which the [Stacks, Tag 0B62] vanishing fails.

## What this does not discharge

The `hdim` binders of `RationalDoublePoints/GradedRelations.lean`,
`/FormPolynomial.lean` and `/ChartPresentation.lean`, and the `hrank` binders of
`/QuadraticForm.lean`, are **not** instances of the input reduced here: those results are stated
for an arbitrary Noetherian local ring, where the dimension formula is a genuine premise and not
a stand-in for anything. What this file bears on is the three results of
`/GradedDimensions.lean` whose hypothesis is about the situation's own ring, and those are the
three given above with `eE` in place of it.

## References

* [Stacks Project, Tag 0BGB](https://stacks.math.columbia.edu/tag/0BGB)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 0B62](https://stacks.math.columbia.edu/tag/0B62)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing (CotangentSpace ResidueField maximalIdeal)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (S : RationalSingularitySituation.{u})
  [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))]

/-! ### The degree of every integer twist -/

/-- **`deg 𝒪_E(a + b) = deg 𝒪_E(a) + deg 𝒪_E(b)` for all integers `a` and `b`.** -/
public theorem invertibleCurveDegree_curveTwistSheaf_add (a b : ℤ) :
    invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A (a + b)) =
      invertibleCurveDegree (ResidueField S.A)
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
          (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
          (curveTwistSheaf S.A a) +
        invertibleCurveDegree (ResidueField S.A)
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
          (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
          (curveTwistSheaf S.A b) := by
  have hiso : Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
      (curveTwistSheaf S.A a) (curveTwistSheaf S.A b) ≅ curveTwistSheaf S.A (a + b) :=
    curveTwistSheafAddIso S.A a b
  have htens : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(exceptionalCurve S.A).toRingedSpace.presheaf,
        (exceptionalCurve S.A).toRingedSpace.IsSheaf⟩).obj (curveTwistSheaf S.A a)).obj
          (curveTwistSheaf S.A b))
      = Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
          (curveTwistSheaf S.A a) (curveTwistSheaf S.A b) :=
    Stacks.TensorSheafDedup.tensorSheaf_eq _ _ _
  have hraw := curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one
    (ResidueField S.A) (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
    (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
    (curveTwistSheaf S.A a) (curveTwistSheaf S.A b) 1 1
  simp only [Nat.cast_one, one_mul] at hraw
  have : Stacks.Ample.IsInvertibleModule (exceptionalCurve S.A)
      (Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
        (curveTwistSheaf S.A a) (curveTwistSheaf S.A b)) :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso hiso.symm
  have hadd : curveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
          (curveTwistSheaf S.A a) (curveTwistSheaf S.A b)) 1 =
      curveDegree (ResidueField S.A)
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
          (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
          (curveTwistSheaf S.A a) 1 +
        curveDegree (ResidueField S.A)
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
          (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
          (curveTwistSheaf S.A b) 1 :=
    (curveDegree_congr_module (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      1 htens
      (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (exceptionalCurve S.A)
        (curveTwistSheaf S.A a) (curveTwistSheaf S.A b) 1 1)
      inferInstance).symm.trans hraw
  rw [← invertibleCurveDegree_eq_of_iso (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        hiso,
    invertibleCurveDegree_eq_curveDegree_one, hadd,
    ← invertibleCurveDegree_eq_curveDegree_one, ← invertibleCurveDegree_eq_curveDegree_one]

/-- **`deg 𝒪_E(0) = 0`**, because `𝒪_E(0) ≅ 𝒪_E`. -/
public theorem invertibleCurveDegree_curveTwistSheaf_zero :
    invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A 0) = 0 :=
  invertibleCurveDegree_eq_zero_of_iso_unit (ResidueField S.A)
    (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
    (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
    (curveTwistSheaf S.A 0) (curveTwistSheafZeroIso S.A)

/-- **`deg 𝒪_E(n) = n · deg 𝒪_E(1)` for every integer `n`.** -/
public theorem invertibleCurveDegree_curveTwistSheaf_eq_zsmul (n : ℤ) :
    invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A n) =
      n * invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A 1) := by
  induction n using Int.induction_on with
  | zero => rw [invertibleCurveDegree_curveTwistSheaf_zero]; ring
  | succ k ih =>
      have h := invertibleCurveDegree_curveTwistSheaf_add S (k : ℤ) 1
      rw [ih] at h
      rw [h]
      ring
  | pred k ih =>
      have h := invertibleCurveDegree_curveTwistSheaf_add S (-(k : ℤ) - 1) 1
      rw [show (-(k : ℤ) - 1 + 1) = -(k : ℤ) by ring, ih] at h
      linear_combination -h

/-- **`deg 𝒪_E(n) = n · (dim_κ(𝔪/𝔪²) − 1)` for every integer `n`.** -/
public theorem invertibleCurveDegree_curveTwistSheaf_int (n : ℤ) :
    invertibleCurveDegree (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
        (curveTwistSheaf S.A n) =
      n * ((Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) : ℤ) - 1) := by
  rw [invertibleCurveDegree_curveTwistSheaf_eq_zsmul S n,
    invertibleCurveDegree_curveTwistSheaf_one S]

/-! ### Embedding dimension three from the degree of the inverse twist -/

/-- **`deg 𝒪_E(-1) = -2` forces `dim_κ(𝔪/𝔪²) = 3`.** -/
public theorem finrank_cotangentSpace_eq_three_of_invertibleCurveDegree_neg_one
    (h : invertibleCurveDegree (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (curveTwistSheaf S.A (-1)) = -2) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 := by
  rw [invertibleCurveDegree_curveTwistSheaf_int S (-1)] at h
  omega

/-- **`h⁰(E, 𝒪_E(-1)) = 0` and `h¹(E, 𝒪_E(-1)) = 1` force `dim_κ(𝔪/𝔪²) = 3`.**

These two dimensions are what Serre duality on `E` over `κ` delivers from `h¹(E, 𝒪_E) = 0` and
`h⁰(E, 𝒪_E) = 1`, once `𝒪_E(-1)` is known to be the dualizing sheaf of `E` over `κ`. The degree
is the alternating sum of the two minus the same sum for the structure sheaf, both sums
collapsing to `h⁰ − h¹` because `E` is one-dimensional, so the hypotheses give
`deg 𝒪_E(-1) = (0 − 1) − (1 − 0) = −2`. -/
public theorem finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_neg_one
    (h0 : Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (curveTwistSheaf S.A (-1)) 0) = 0)
    (h1 : Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (curveTwistSheaf S.A (-1)) 1) = 1) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 := by
  refine finrank_cotangentSpace_eq_three_of_invertibleCurveDegree_neg_one S ?_
  have hvan : ∀ (F : (exceptionalCurve S.A).Modules) (m : ℕ), 2 ≤ m →
      IsZero (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F m) := fun F m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F (d := 1)
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (by omega)
  rw [invertibleCurveDegree_eq_sub_of_isZero (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (curveTwistSheaf S.A (-1)) (fun m hm => hvan _ m hm) (fun m hm => hvan _ m hm),
    h0, h1, finrank_cohomologyOverField_unit_zero S, finrank_cohomologyOverField_unit_one S]
  norm_num

/-! ### The two readings of the embedding dimension -/

omit [IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))] in
/-- **`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1` for every `n` is equivalent to `dim_κ(𝔪/𝔪²) = 3`.**

The graded dimensions are `n · (dim_κ(𝔪/𝔪²) − 1) + 1` unconditionally
(`AlgebraicGeometry.BlowUpDualizing.finrank_gradedPiece_eq`), which gives the backward
direction; the forward direction is the case `n = 1`, where the graded piece is the cotangent
space. The two forms are the two spellings in which the governing input of Section 54.12 is
taken as a hypothesis — `= 3` by the results of
`RationalDoublePoints/GradedDimensions.lean`, `∀ n, = 2n + 1` by those of
`RationalDoublePoints/GradedRelations.lean`, `/FormPolynomial.lean` and
`/ChartPresentation.lean` — so this is what lets one discharge the other. -/
public theorem forall_finrank_gradedPiece_eq_two_mul_add_one_iff :
    (∀ n, Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1) ↔
      Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 := by
  refine ⟨fun h => ?_, fun h n => finrank_gradedPiece_eq_two_mul_add_one S n h⟩
  have h1 := h 1
  rw [IsLocalRing.finrank_gradedPiece_one] at h1
  omega

/-! ### Embedding dimension three, granted that `ω_E` is the dualizing sheaf of `E` over `κ` -/

/-- **`dim_κ(𝔪/𝔪²) = 3` for a Gorenstein rational surface singularity, with the single input
that `ω_E = H¹(a(ω_X))` is the dualizing sheaf of `E` over `κ`.**

This is the opening computation of Section 54.12 of the source. Clause (1) of
[Stacks, Tag 0B64] and `ω_A ≅ A` give `ω_E ≅ 𝒪_E(-1)`
(`AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_curveTwistSheaf`);
the hypothesis `eE` identifies `ω_E` with `Stacks.Duality.dualizingSheafOverField` of the
structure morphism `E ⟶ Spec(κ)`, for which duality over `κ` gives
`h⁰ = dim_κ H¹(E, 𝒪_E) = 0` and `h¹ = 1`
(`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one` and
`.finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one`, both proved with nothing
carried); so `deg 𝒪_E(-1) = -2`, so `deg 𝒪_E(1) = 2`, so `dim_κ(𝔪/𝔪²) = 3`.

The hypothesis `eE` is the same single isomorphism that
`BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_exceptionalDualizingIso`
carries, and it is the only thing missing: see the module documentation of
`…/RationalSingularities/BlowUpExceptionalDualizing.lean` for which tags proving it needs. No
`@[stacks]` attribute is attached, because a hypothesis is carried. -/
public theorem finrank_cotangentSpace_eq_three_of_exceptionalDualizingIso
    (hnot : ¬ IsRegularLocalRing S.A)
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : ωA ≅ ModuleCat.of S.A S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).NormalizedDualizingModule ωA ωX)
    (G : SheafOfModules.GeneratingSections
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX))
    (eE : exceptionalDualizingModule S.A ωX ≅ Stacks.Duality.dualizingSheafOverField
      (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
      (cohenMacaulayCurveSituationExceptionalDivisor S).f) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 := by
  obtain ⟨hG⟩ := nonempty_exceptionalDualizingModule_iso_curveTwistSheaf S hnot ωA hωA e ωX N G
  have iso : curveTwistSheaf S.A (-1) ≅ Stacks.Duality.dualizingSheafOverField
      (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
      (cohenMacaulayCurveSituationExceptionalDivisor S).f := hG.symm ≪≫ eE
  have hd0 :=
    CohenMacaulayCurveSituation.finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one
      (cohenMacaulayCurveSituationExceptionalDivisor S)
  have hd1 :=
    CohenMacaulayCurveSituation.finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one
      (cohenMacaulayCurveSituationExceptionalDivisor S)
  exact finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_neg_one S
    ((finrank_cohomologyOverField_eq_of_iso (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) iso 0).trans
      (hd0.trans (finrank_cohomologyOverField_unit_one S)))
    ((finrank_cohomologyOverField_eq_of_iso (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) iso 1).trans hd1)

/-! ### What the identification discharges downstream -/

section Discharged

variable (hnot : ¬ IsRegularLocalRing S.A)
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : ωA ≅ ModuleCat.of S.A S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).NormalizedDualizingModule ωA ωX)
    (G : SheafOfModules.GeneratingSections
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX))
    (eE : exceptionalDualizingModule S.A ωX ≅ Stacks.Duality.dualizingSheafOverField
      (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
      (cohenMacaulayCurveSituationExceptionalDivisor S).f)

include hnot ωA hωA e ωX N G eE

/-- **`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1`**, the opening computation of Section 54.12 in the form the
results of `RationalDoublePoints/GradedRelations.lean`,
`RationalDoublePoints/FormPolynomial.lean` and `RationalDoublePoints/ChartPresentation.lean`
take it, with the embedding dimension discharged from the single isomorphism `eE`. -/
public theorem finrank_gradedPiece_eq_two_mul_add_one_of_exceptionalDualizingIso (n : ℕ) :
    Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1 :=
  finrank_gradedPiece_eq_two_mul_add_one S n
    (finrank_cotangentSpace_eq_three_of_exceptionalDualizingIso S hnot ωA hωA e ωX N G eE)

/-- **The quadratic relation of Section 54.12**, with the embedding dimension discharged from
the single isomorphism `eE` rather than taken in a binder as in
`AlgebraicGeometry.BlowUpDualizing.exists_generators_and_quadraticRelation_of_finrank`. -/
public theorem exists_generators_and_quadraticRelation_of_exceptionalDualizingIso :
    ∃ (x : Fin 3 → S.A) (a : Fin 3 → Fin 3 → S.A) (b : Fin 3 → Fin 3 → Fin 3 → S.A),
      Ideal.span (Set.range x) = maximalIdeal S.A ∧ (∀ p q, q < p → a p q = 0) ∧
        (∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal S.A) ∧
        ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r) :=
  exists_generators_and_quadraticRelation_of_finrank S
    (finrank_cotangentSpace_eq_three_of_exceptionalDualizingIso S hnot ωA hωA e ωX N G eE)

/-- **The case I / case II dichotomy of Section 54.12**, with the embedding dimension
discharged from the single isomorphism `eE` rather than taken in a binder as in
`AlgebraicGeometry.BlowUpDualizing`
`.exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear_of_finrank`. -/
public theorem exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear_of_exceptionalDualizingIso :
    (∃ (x : Fin 3 → S.A) (b : Fin 3 → Fin 3 → Fin 3 → S.A),
        Ideal.span (Set.range x) = maximalIdeal S.A ∧
          x 2 * x 2 = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) ∨
      ∃ (x : Fin 3 → S.A) (a : Fin 3 → Fin 3 → S.A) (b : Fin 3 → Fin 3 → Fin 3 → S.A),
        Ideal.span (Set.range x) = maximalIdeal S.A ∧ (∀ p q, q < p → a p q = 0) ∧
          (∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal S.A) ∧
          (∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) ∧
          ¬ IsScalarSqLinear fun p q => IsLocalRing.residue S.A (a p q) :=
  exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear_of_finrank S
    (finrank_cotangentSpace_eq_three_of_exceptionalDualizingIso S hnot ωA hωA e ωX N G eE)

end Discharged

end AlgebraicGeometry.BlowUpDualizing

end
