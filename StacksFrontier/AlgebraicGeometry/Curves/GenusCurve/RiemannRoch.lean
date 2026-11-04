module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# Riemann-Roch on a proper curve with constant global functions, in terms of the genus

Let `k` be a field and `X` a proper scheme over `k` of dimension at most one with
`H⁰(X, 𝒪_X) = k`. Then `χ(X, 𝒪_X) = 1 - g`, where `g = dim_k H¹(X, 𝒪_X)` is the genus of
[Stacks, Tag 0BY7], and consequently, for every finite locally free `𝒪_X`-module `ℰ` of constant
rank `r` and every invertible `𝒪_X`-module `ℒ`,

  `χ(X, ℰ) = deg(ℰ) + r(1 - g)`,  `χ(X, ℒ) = dim H⁰(X, ℒ) - dim H¹(X, ℒ) = deg(ℒ) + 1 - g`,

with `deg` the degree of [Stacks, Tag 0AYR].

## The canonical API

The notions used here, and throughout the chapter on curves, are the following, and no other:

* the Euler characteristic `AlgebraicGeometry.eulerCharacteristic` of [Stacks, Tag 0BEJ], taken
  of the cohomology `AlgebraicGeometry.cohomologyOverField`;
* the degree `AlgebraicGeometry.curveDegree` of a finite locally free module of constant rank, and
  `AlgebraicGeometry.invertibleCurveDegree` of an invertible module, of [Stacks, Tag 0AYR];
* the genus `AlgebraicGeometry.genus` of [Stacks, Tag 0BY7];
* Riemann-Roch with Chern classes, equations [Stacks, Tag 0BRY] and [Stacks, Tag 0BRZ], is
  `AlgebraicGeometry.curveDegree_eq_chowDegree_firstChernCapOnCycles_fundamental` and
  `AlgebraicGeometry.eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add`.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_one_unit_eq_genus`: `dim_k H¹(X, 𝒪_X) = g`.
* `AlgebraicGeometry.eulerCharacteristic_unit_eq_one_sub_genus`: `χ(X, 𝒪_X) = 1 - g`.
* `AlgebraicGeometry.eulerCharacteristic_eq_curveDegree_add_genus`:
  `χ(X, ℰ) = deg(ℰ) + r(1 - g)`.
* `AlgebraicGeometry.eulerCharacteristic_eq_invertibleCurveDegree_add_genus`:
  `χ(X, ℒ) = deg(ℒ) + 1 - g`.
* `AlgebraicGeometry.finrank_sub_finrank_eq_invertibleCurveDegree_add_genus`:
  `dim H⁰(X, ℒ) - dim H¹(X, ℒ) = deg(ℒ) + 1 - g`.

## Implementation notes

`H⁰(X, 𝒪_X) = k` is spelled `IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)`: the ring map
from `k` to the global functions that the structure morphism induces is an isomorphism. The
coherence instances that `AlgebraicGeometry.eulerCharacteristic` needs are supplied by
properness over `k`, so no statement here takes a coherence hypothesis. The vanishing of
cohomology above degree one is Grothendieck's theorem [Stacks, Tag 02UZ].

## References

* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.CurveEulerBridge

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`dim_k H¹(X, 𝒪_X)` is the genus**, the genus of [Stacks, Tag 0BY7] being defined through the
derived global sections after pushforward to `Spec k`. -/
theorem finrank_cohomologyOverField_one_unit_eq_genus :
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) =
      genus f :=
  (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq.symm

/-- **`χ(X, 𝒪_X) = 1 - g`** for a proper scheme `X` of dimension at most one over a field `k`
with `H⁰(X, 𝒪_X) = k`, where `g` is the genus of [Stacks, Tag 0BY7]. -/
theorem eulerCharacteristic_unit_eq_one_sub_genus [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1) :
    letI := isCoherent_unit k f
    eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) = 1 - (genus f : ℤ) := by
  refine (finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f _
    (isZero_cohomologyOverField_two_le k f hdim _)).trans ?_
  rw [finrank_cohomologyOverField_unit_zero_eq_one, finrank_cohomologyOverField_one_unit_eq_genus]
  simp

/-- **Riemann-Roch on a proper curve with `H⁰(X, 𝒪_X) = k`, for a finite locally free module.**
For `ℰ` finite locally free of constant rank `r`, `χ(X, ℰ) = deg(ℰ) + r(1 - g)`, with `deg` the
degree of [Stacks, Tag 0AYR] and `g` the genus of [Stacks, Tag 0BY7]. -/
theorem eulerCharacteristic_eq_curveDegree_add_genus [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    letI := isCoherent_of_isFiniteLocallyFreeOfRank k f E r
    eulerCharacteristic k f E = curveDegree k f hdim E r + r * (1 - (genus f : ℤ)) := by
  have h1 := eulerCharacteristic_unit_eq_one_sub_genus k f hdim
  unfold eulerCharacteristic at h1 ⊢
  unfold curveDegree
  rw [h1]
  ring

/-- **Riemann-Roch on a proper curve with `H⁰(X, 𝒪_X) = k`, for an invertible module.**
`χ(X, ℒ) = deg(ℒ) + 1 - g`, with `deg` the degree of [Stacks, Tag 0AYR] and `g` the genus of
[Stacks, Tag 0BY7]. -/
theorem eulerCharacteristic_eq_invertibleCurveDegree_add_genus [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI := isCoherent_of_isFiniteLocallyFreeOfRank k f L 1
    eulerCharacteristic k f L = invertibleCurveDegree k f hdim L + 1 - (genus f : ℤ) := by
  rw [invertibleCurveDegree_eq_curveDegree,
    eulerCharacteristic_eq_curveDegree_add_genus k f hdim L 1]
  push_cast
  ring

/-- **Riemann-Roch on a proper curve with `H⁰(X, 𝒪_X) = k`, in terms of `h⁰` and `h¹`.** For an
invertible module `ℒ`, `dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) = deg(ℒ) + 1 - g`. -/
theorem finrank_sub_finrank_eq_invertibleCurveDegree_add_genus [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f L 1) : ℤ) =
      invertibleCurveDegree k f hdim L + 1 - (genus f : ℤ) := by
  have h := eulerCharacteristic_eq_invertibleCurveDegree_add_genus k f hdim L
  unfold eulerCharacteristic at h
  rw [← h, finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f L
    (isZero_cohomologyOverField_two_le k f hdim L)]

end AlgebraicGeometry

end
