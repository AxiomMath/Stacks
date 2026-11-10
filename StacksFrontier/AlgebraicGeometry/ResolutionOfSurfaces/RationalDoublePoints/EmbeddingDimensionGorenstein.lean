module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDualityZero
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.EmbeddingDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Situation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentificationSupplement

/-!
# The embedding dimension of a Gorenstein rational surface singularity

Section 54.12 of the source opens with `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1` for a two-dimensional
Gorenstein rational surface singularity. `RationalDoublePoints/GradedDimensions.lean` proves
`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = n · (dim_κ(𝔪/𝔪²) − 1) + 1`, so what remains is `dim_κ(𝔪/𝔪²) = 3`. This file
proves it for a singularity which is not regular, given a dualizing module on the blowup
normalized in the sense of [Stacks, Remark 0B4R].

## Main results

The elided prefix is `AlgebraicGeometry.BlowUpDualizing`.

* `.finrank_cotangentSpace_eq_three_of_dualizingNormalization`: **`dim_κ(𝔪/𝔪²) = 3`** for a
  Gorenstein rational surface singularity which is not regular, given a normalized `ω_X` on the
  blowup.
* `AlgebraicGeometry.RationalDoublePointSituation`
  `.finrank_cotangentSpace_eq_three_of_dualizingNormalization`: the same at Situation
  [Stacks, Tag 0BGC], where non-regularity and the Gorenstein property are fields of the
  situation.

The three steps, each stated separately:

* `.finrank_cotangentSpace_le_three_of_finrank_cohomologyOverField_neg_one_le_one` and
  `.finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_neg_one_le_one`:
  **`dim_κ H¹(E, 𝒪_E(-1)) ≤ 1` forces `dim_κ(𝔪/𝔪²) ≤ 3`**, and with `A` not regular forces
  equality.
* `.finrank_cohomologyOverField_curveTwistSheaf_neg_one_one_eq_zero_pullback`:
  **`dim_κ H¹(E, 𝒪_E(-1)) = dim_κ H⁰(E, ω_X|_E)`**, duality on `E` over `κ` at `𝒪_E(-1)`.
* `.finrank_cohomologyOverField_zero_pullback_le_one`: **`dim_κ H⁰(E, ω_X|_E) ≤ 1`**, which is
  where the Gorenstein hypothesis enters.

## The argument

The source reads `deg 𝒪_E(1) = 2` off `ω_E = 𝒪_E(-1)`, and gets `ω_X ≅ 𝒪_X`, which is what makes
`ω_E = 𝒪_E(-1)`, from clause (3) of [Stacks, Tag 0B64], whose one input is the global generation
of `ω_X|_E` of [Stacks, Tag 0B5H]. The argument below does not trivialize `ω_X`, and so does not
use that global generation. It counts sections instead.

* Riemann–Roch for the invertible `𝒪_E(-1)`: `deg 𝒪_E(-1) = h⁰ − h¹ − 1` and
  `deg 𝒪_E(-1) = 1 − dim_κ(𝔪/𝔪²)`, so `dim_κ(𝔪/𝔪²) = 2 − h⁰(𝒪_E(-1)) + h¹(𝒪_E(-1))`. Since
  `h⁰ ≥ 0`, a bound `h¹(𝒪_E(-1)) ≤ 1` gives `dim_κ(𝔪/𝔪²) ≤ 3`, and non-regularity gives the
  reverse inequality.
* `h¹(E, 𝒪_E(-1)) = h⁰(E, 𝒪_E(-1)^∨ ⊗ ω_E)` is the duality of dimensions of
  [Stacks, Tag 0BS6], clause (3), at `i = 1`; `𝒪_E(-1)^∨ ≅ 𝒪_E(1)` and clause (1) of
  [Stacks, Tag 0B64] turn the right-hand side into `h⁰(E, ω_X|_E)`. This uses that the module
  `ω_E = H¹(a(ω_X))` of clause (1) is the dualizing sheaf of `E` over `κ`
  (`AlgebraicGeometry.BlowUpDualizing`
  `.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField`).
* `h⁰(E, ω_X|_E) ≤ 1` is the Gorenstein input: `Γ(X, ω_X) ≅ ω_A ≅ A` is cyclic by
  [Stacks, Tag 0BBU], it surjects onto `Γ(E, ω_X|_E)` by the restriction sequence and
  `H¹(X, ω_X(1)) = 0` (clause (2) of [Stacks, Tag 0B64]), and `Γ(E, 𝒪_E) = κ`.

## The hypothesis

`ωX` together with `N` is a dualizing module on the blowup normalized relative to `A`.
`…/RationalSingularities/NormalizedDualizingExistence.lean` defines the condition and proves that
it determines `ω_X` up to isomorphism
(`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization.moduleIso`); the existence
of such a module is not proved. The Gorenstein hypothesis supplies `ω_A`, its dualizing character
and the isomorphism `ω_A ≅ A` at once, `Dualizing.IsGorensteinLocalRing A` being by definition
the statement that `A[0]` is a dualizing complex over `A`.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
* [Stacks Project, Tag 0BBU](https://stacks.math.columbia.edu/tag/0BBU)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 040A](https://stacks.math.columbia.edu/tag/040A)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing (ResidueField)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

/-! ### Embedding dimension at most three from the first cohomology of the inverse twist -/

/-- **`dim_κ H¹(E, 𝒪_E(-1)) ≤ 1` forces `dim_κ(𝔪/𝔪²) ≤ 3`.**

The degree of `𝒪_E(-1)` is the alternating sum of its two cohomology dimensions minus the same
sum for the structure sheaf, both sums collapsing to `h⁰ − h¹` because `E` is one-dimensional,
so it is `h⁰(𝒪_E(-1)) − h¹(𝒪_E(-1)) − 1`; and it is `1 − dim_κ(𝔪/𝔪²)` by
`AlgebraicGeometry.BlowUpDualizing.invertibleCurveDegree_curveTwistSheaf_int`. Hence
`dim_κ(𝔪/𝔪²) = 2 − h⁰(𝒪_E(-1)) + h¹(𝒪_E(-1))`, which the hypothesis bounds by three. -/
public theorem finrank_cotangentSpace_le_three_of_finrank_cohomologyOverField_neg_one_le_one
    (S : RationalSingularitySituation.{u})
    (h1 : Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (curveTwistSheaf S.A (-1)) 1) ≤ 1) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) ≤ 3 := by
  have : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    isProper_exceptionalDivisorToCentre_residuePoint S.A
  have hvan : ∀ (F : (exceptionalCurve S.A).Modules) (m : ℕ), 2 ≤ m →
      IsZero (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F m) := fun F m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) F (d := 1)
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (by omega)
  have key := invertibleCurveDegree_eq_sub_of_isZero (ResidueField S.A)
    (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
    (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
    (curveTwistSheaf S.A (-1)) (fun m hm => hvan _ m hm) (fun m hm => hvan _ m hm)
  rw [invertibleCurveDegree_curveTwistSheaf_int S (-1),
    finrank_cohomologyOverField_unit_zero S, finrank_cohomologyOverField_unit_one S] at key
  push_cast at key
  omega

/-- **`dim_κ H¹(E, 𝒪_E(-1)) ≤ 1` forces `dim_κ(𝔪/𝔪²) = 3`** for a singularity which is not
regular: the hypothesis gives `dim_κ(𝔪/𝔪²) ≤ 3`, and non-regularity rules the value two out of
the range `[2, 3]` that a two-dimensional local ring leaves. -/
public theorem finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_neg_one_le_one
    (S : RationalSingularitySituation.{u}) (hnot : ¬ IsRegularLocalRing S.A)
    (h1 : Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (curveTwistSheaf S.A (-1)) 1) ≤ 1) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 := by
  have hle := finrank_cotangentSpace_le_three_of_finrank_cohomologyOverField_neg_one_le_one S h1
  have hne : Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) ≠ 2 := fun h =>
    hnot ((isRegularLocalRing_iff_finrank_cotangentSpace_eq_two S).mpr h)
  have h2 := two_le_finrank_cotangentSpace S
  omega

/-! ### The dual of the inverse twist, and duality at `𝒪_E(-1)` -/

/-- **`𝒪_E(-1)^∨ ≅ 𝒪_E(1)`.** The evaluation pairing makes the dual of an invertible module a
tensor inverse of it ([Stacks, Tag 040A], clause (2)), `𝒪_E(1)` is one too, and a tensor
inverse is unique up to isomorphism. -/
private def dualCurveTwistNegOneIso (A : Type u) [CommRing A] [IsLocalRing A] :
    Stacks.SheafOfModules.dualSheaf (exceptionalCurve A).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))
        (curveTwistSheaf A (-1)) ≅
      curveTwistSheaf A 1 := by
  haveI : Stacks.Ample.IsInvertibleModule (exceptionalCurve A)
      (Stacks.SheafOfModules.dualSheaf (exceptionalCurve A).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))
        (curveTwistSheaf A (-1))) :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf _ _ _
  haveI := Stacks.SheafOfModules.Invertible.isIso_evaluation (exceptionalCurve A).presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))
    (curveTwistSheaf A (-1))
  have e : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(exceptionalCurve A).presheaf,
        CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ (exceptionalCurve A).presheaf
          (CategoryTheory.forget₂ CommRingCat RingCat)
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))⟩).obj
        (Stacks.SheafOfModules.dualSheaf (exceptionalCurve A).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))
          (curveTwistSheaf A (-1)))).obj (curveTwistSheaf A (-1))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (exceptionalCurve A).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))) :=
    asIso (Stacks.SheafOfModules.evaluation (exceptionalCurve A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))
      (curveTwistSheaf A (-1)))
  exact Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso (exceptionalCurve A) _
    (curveTwistSheaf A 1) (curveTwistSheaf A (-1)) e
    (curveTwistSheafAddIso A 1 (-1) ≪≫
      curveTwistSheafCongr A (show (1 : ℤ) + -1 = 0 by ring) ≪≫ curveTwistSheafZeroIso A)

/-- **`𝒪_E(-1)^∨ ⊗ ω_E = ω_X|_E`** for `ω_E = H¹(a(ω_X))` the module of clause (1) of
[Stacks, Tag 0B64]: the dual of `𝒪_E(-1)` is `𝒪_E(1)`, and clause (1) read as
`ω_X|_E ≅ ω_E(1)` is `AlgebraicGeometry.BlowUpDualizing`
`.nonempty_pullback_dualizing_iso_curveTwist`. -/
private def dualTensorExceptionalDualizingIso (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (ωX : (blowUpScheme A).Modules) :
    Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve A)
        (Stacks.SheafOfModules.dualSheaf (exceptionalCurve A).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A))
          (curveTwistSheaf A (-1)))
        (exceptionalDualizingModule A ωX) ≅
      (Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX :=
  Stacks.RelativeVeryAmple.tensorModulesMapIso (exceptionalCurve A)
      (dualCurveTwistNegOneIso A) (Iso.refl _) ≪≫
    Stacks.SheafOfModules.tensorSheafBraiding (exceptionalCurve A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A)) _ _ ≪≫
    (nonempty_pullback_dualizing_iso_curveTwist
      (nonempty_exceptionalDualizingModule_iso_curveTwist A ωX).some).some.symm

/-- **`dim_κ H¹(E, 𝒪_E(-1)) = dim_κ H⁰(E, ω_X|_E)`.**

This is the duality of dimensions of [Stacks, Tag 0BS6], clause (3), at `i = 1` and at the
invertible `ℰ = 𝒪_E(-1)`
(`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`),
read through `𝒪_E(-1)^∨ ⊗ ω_E = ω_X|_E` and the identification of `ω_E = H¹(a(ω_X))` with the
dualizing sheaf of `E` over `κ`, which is `AlgebraicGeometry.BlowUpDualizing`
`.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField` and is where the
normalization `N` of `ω_X` enters. -/
public theorem finrank_cohomologyOverField_curveTwistSheaf_neg_one_one_eq_zero_pullback
    (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) :
    Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (curveTwistSheaf S.A (-1)) 1) =
      Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) 0) := by
  have : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    isProper_exceptionalDivisorToCentre_residuePoint S.A
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  obtain ⟨ecan⟩ :=
    nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField S ωA hωA ωX N
  have hiso : dualTensorDualizingSheafOverField
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (curveTwistSheaf S.A (-1)) ≅
        (Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso (exceptionalCurve S.A) (Iso.refl _)
        ecan.symm ≪≫
      dualTensorExceptionalDualizingIso S.A ωX
  rw [← finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      (le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two))
      (curveTwistSheaf S.A (-1)) 1]
  exact finrank_cohomologyOverField_eq_of_iso (ResidueField S.A)
    (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) hiso 0

/-- **`dim_κ H⁰(E, ω_X|_E) ≤ 1` forces `dim_κ(𝔪/𝔪²) = 3`** for a singularity which is not
regular and carries a dualizing module `ω_X` on the blowup normalized in the sense of
[Stacks, Remark 0B4R].

The two steps are
`AlgebraicGeometry.BlowUpDualizing`
`.finrank_cohomologyOverField_curveTwistSheaf_neg_one_one_eq_zero_pullback`,
duality on `E` over `κ` at the invertible `𝒪_E(-1)`, and
`AlgebraicGeometry.BlowUpDualizing`
`.finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_neg_one_le_one`,
Riemann–Roch for `𝒪_E(-1)`. -/
public theorem finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_zero_pullback_le_one
    (S : RationalSingularitySituation.{u}) (hnot : ¬ IsRegularLocalRing S.A)
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX)
    (h : Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) 0) ≤ 1) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 :=
  finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_neg_one_le_one S hnot
    ((finrank_cohomologyOverField_curveTwistSheaf_neg_one_one_eq_zero_pullback S ωA hωA
      ωX N).trans_le h)

/-! ### The section count from the trace isomorphism -/

section Sections

open Opposite
open Stacks.Cohomology.AffineBase (moduleGlobalSections)

/-- **A vector space in which every vector is a multiple of one fixed vector has dimension at
most one.** The map `c ↦ c • v` is then a surjection from the base field, so the dimension is at
most `dim_K K = 1`. -/
private theorem finrank_le_one_of_forall_exists_smul {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (v : V) (h : ∀ w : V, ∃ c : K, c • v = w) :
    Module.finrank K V ≤ 1 := by
  have hrange : LinearMap.range (LinearMap.toSpanSingleton K V v) = ⊤ :=
    LinearMap.range_eq_top.2 h
  have h1 : Module.finrank K
      (LinearMap.range (LinearMap.toSpanSingleton K V v)) ≤ Module.finrank K K :=
    LinearMap.finrank_range_le _
  rwa [hrange, (Submodule.topEquiv (R := K) (M := V)).finrank_eq, Module.finrank_self] at h1

/-- **`dim_κ H⁰(E, ω_X|_E) ≤ 1` when `ω_A ≅ A`.**

Three facts combine.

* The `ω_X`-twisted restriction sequence `0 ⟶ ω_X(1) ⟶ ω_X ⟶ i_*(ω_X|_E) ⟶ 0` of
  [Stacks, Tag 0C6K] (`AlgebraicGeometry.BlowUpDualizing`
  `.exists_shortExact_schemeTwist_dualizing_unit`, whose second map is pinned to be the unit of
  `i^* ⊣ i_*`) together with `H¹(X, ω_X(1)) = 0`, clause (2) of [Stacks, Tag 0B64] at `n = 1`
  (`AlgebraicGeometry.BlowUpDualizing`
  `.isZero_firstCohomology_dualizingTwist_of_isDualizingRingModule`), makes
  `Γ(X, ω_X) ⟶ Γ(E, ω_X|_E)` surjective through the long exact cohomology sequence.
* `Γ(X, ω_X) ≅ ω_A ≅ A` is [Stacks, Tag 0BBU] for the normalized `ω_X`
  (`AlgebraicGeometry.RationalSingularitySituation.traceIsoOfNormalized`) composed with the
  Gorenstein isomorphism `e`, so `Γ(X, ω_X)` is a cyclic `A`-module: every section is `a · t₀`.
* `Γ(E, ω_E) = κ` (`AlgebraicGeometry`
  `.isIso_globalSections_exceptionalDivisorToCentre_residuePoint`,
  clause (5) of [Stacks, Tag 0B63] at `n = 0`), and the scalars act on `Γ(E, ω_X|_E)` through
  `Γ(X, 𝒪_X) ⟶ Γ(E, 𝒪_E)`. So the image of `a · t₀` is a `Γ(E, 𝒪_E)`-multiple,
  hence a `κ`-multiple, of the image of `t₀`.

The three together say that `Γ(E, ω_X|_E)` is spanned over `κ` by a single section. -/
public theorem finrank_cohomologyOverField_zero_pullback_le_one
    (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : ωA ≅ ModuleCat.of S.A S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) :
    Module.finrank (ResidueField S.A) (cohomologyOverField (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) 0) ≤ 1 := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  let : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
  obtain ⟨fseq, wseq, hS⟩ := exists_shortExact_schemeTwist_dualizing_unit S.A ωX N.isDualizing
  have h2 := isZero_firstCohomology_dualizingTwist_of_isDualizingRingModule S ωA hωA ωX N 1
  rw [Nat.cast_one] at h2
  have hH : IsZero (Hgroup (blowUpScheme S.A).ringCatSheaf ⊤ 1 (schemeTwist S.A ωX 1)) :=
    (Stacks.Cohomology.ModuleComparison.isZero_hgroup_iff_isZero_rightDerivedPlus_evaluation
        _ ⊤ (m := (1 : ℤ)) (n := 1) (by norm_num) _).2
      ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
        (moduleGlobalSections (blowUpScheme S.A)) 1 _).1 h2)
  have hsurj := Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one
    (blowUpScheme S.A) ⊤ hS hH
  let θ : (rationalSingularitySituationBlowUp S).globalSectionsModule ωX ≅
      ModuleCat.of (rationalSingularitySituationBlowUp S).A
        (rationalSingularitySituationBlowUp S).A :=
    (rationalSingularitySituationBlowUp S).traceIsoOfNormalized
      (RationalSingularitySituation.DualizingNormalization.normalizedDualizingModule
        (rationalSingularitySituationBlowUp S) N) ≪≫ e
  have := isIso_globalSections_exceptionalDivisorToCentre_residuePoint S
  have happ : (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appTop =
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤ (by simp) := by
    simpa [Scheme.Hom.appTop] using
      (Scheme.Hom.app_eq_appLE
        (f := exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
        (U := (⊤ : (Spec (.of (ResidueField S.A))).Opens)))
  have hsurjφ : Function.Surjective
      ((Scheme.ΓSpecIso (.of (ResidueField S.A))).inv ≫
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤
          (by simp)).hom := by
    rw [← happ]
    exact (ConcreteCategory.bijective_of_isIso _).2
  set GS := (rationalSingularitySituationBlowUp S).globalSectionsMap
    ((Scheme.Modules.pullbackPushforwardAdjunction (exceptionalImmersion S.A)).unit.app ωX)
    with hGS
  set t₀ := θ.toLinearEquiv.symm (1 : (rationalSingularitySituationBlowUp S).A) with ht₀
  set v₀ := GS.hom t₀ with hv₀
  refine Eq.trans_le ((cohomologyOverFieldZeroLinearIso (ResidueField S.A)
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX)).toLinearEquiv.finrank_eq)
    (finrank_le_one_of_forall_exists_smul v₀ ?_)
  intro w
  obtain ⟨t, ht⟩ := hsurj w
  obtain ⟨a', ha'⟩ : ∃ a : (rationalSingularitySituationBlowUp S).A,
      (t : (rationalSingularitySituationBlowUp S).globalSectionsModule ωX) = a • t₀ :=
    ⟨θ.toLinearEquiv t, by
      rw [ht₀, ← map_smul, smul_eq_mul, mul_one]
      exact (θ.toLinearEquiv.symm_apply_apply t).symm⟩
  obtain ⟨c, hc⟩ := hsurjφ (((exceptionalImmersion S.A).appTop).hom
    ((rationalSingularitySituationBlowUp S).structureRingHom a'))
  have hgoal : GS.hom t = a' • v₀ := by
    rw [hv₀, ha']
    exact map_smul GS.hom _ _
  refine ⟨c, Eq.trans ?_ (Eq.trans hgoal.symm ht)⟩
  let vE : (moduleGlobalSections (exceptionalCurve S.A)).obj
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) := v₀
  change ((Scheme.ΓSpecIso (.of (ResidueField S.A))).inv ≫
        (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)).appLE ⊤ ⊤
          (by simp)).hom c • vE =
      ((exceptionalImmersion S.A).appTop).hom
        ((rationalSingularitySituationBlowUp S).structureRingHom a') • vE
  rw [hc]

end Sections

/-! ### Embedding dimension three -/

/-- **`dim_κ(𝔪/𝔪²) = 3` for a Gorenstein rational surface singularity which is not regular**,
given a dualizing module `ω_X` on the blowup of `Spec(A)` in the maximal ideal, normalized relative
to `A` in the sense of [Stacks, Remark 0B4R]. The Gorenstein hypothesis is used as the statement
that `A` is a dualizing module for itself, which is what `Dualizing.IsGorensteinLocalRing` says.

The two halves are the lower bound `dim_κ(𝔪/𝔪²) ≥ 3`, which is the non-regularity of `A`
through clause (3) of [Stacks, Tag 0B63], and the upper bound, which is
`AlgebraicGeometry.BlowUpDualizing.finrank_cohomologyOverField_zero_pullback_le_one` read
through duality on `E` over `κ` and Riemann–Roch for `𝒪_E(-1)`. -/
public theorem finrank_cotangentSpace_eq_three_of_dualizingNormalization
    (S : RationalSingularitySituation.{u}) (hnot : ¬ IsRegularLocalRing S.A)
    (hgor : Dualizing.IsGorensteinLocalRing S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization
        (ModuleCat.of S.A S.A) ωX) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  have hωA : Stacks.Duality.IsDualizingRingModule S.A (ModuleCat.of S.A S.A) :=
    ⟨inferInstance, ⟨0, hgor⟩⟩
  exact finrank_cotangentSpace_eq_three_of_finrank_cohomologyOverField_zero_pullback_le_one S
    hnot (ModuleCat.of S.A S.A) hωA ωX N
    (finrank_cohomologyOverField_zero_pullback_le_one S (ModuleCat.of S.A S.A) hωA
      (Iso.refl _) ωX N)
end AlgebraicGeometry.BlowUpDualizing

namespace AlgebraicGeometry.RationalDoublePointSituation

open AlgebraicGeometry.BlowUpDualizing

/-- **`dim_κ(𝔪/𝔪²) = 3` at Situation [Stacks, Tag 0BGC]**: the embedding dimension of a
rational double point is three. The non-regularity and the Gorenstein property that
`AlgebraicGeometry.BlowUpDualizing.finrank_cotangentSpace_eq_three_of_dualizingNormalization`
takes in binders are fields of the situation.

The modification `f : X ⟶ Spec(A)` and the enumeration of the components of its special fibre
are what `AlgebraicGeometry.RationalDoublePointSituation.toRationalSingularitySituation` asks
for in order to read a rational double point as a member of Situation [Stacks, Tag 0B4W];
nothing below depends on which modification is chosen, every object of the computation being
built from the blowup of `Spec(A)` in the maximal ideal, on which `ω_X` is a normalized
dualizing module. -/
public theorem finrank_cotangentSpace_eq_three_of_dualizingNormalization
    (S : RationalDoublePointSituation.{u}) (X : Scheme.{u}) [IsNormal X] (f : X ⟶ S.base)
    (hf : IsModification f) (numberOfComponents : ℕ)
    (components : Fin numberOfComponents ≃ {Z : Set (f.fiber S.closedPoint) //
      Z ∈ irreducibleComponents (f.fiber S.closedPoint)})
    (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp
          (S.toRationalSingularitySituation X f hf numberOfComponents components)).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp
          (S.toRationalSingularitySituation X f hf numberOfComponents components)
        ).DualizingNormalization (ModuleCat.of S.A S.A) ωX) :
    Module.finrank (ResidueField S.A) (IsLocalRing.CotangentSpace S.A) = 3 :=
  BlowUpDualizing.finrank_cotangentSpace_eq_three_of_dualizingNormalization
    (S.toRationalSingularitySituation X f hf numberOfComponents components)
    S.not_isRegularLocalRing S.gorenstein ωX N

end AlgebraicGeometry.RationalDoublePointSituation

end

