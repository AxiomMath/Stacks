module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveAmple
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineProperties
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional

/-!
# An ample invertible module on the projective line has Euler characteristic at least two

Let `k` be a field and `X` a proper curve over `k`. The degree of an invertible `𝒪_X`-module `𝓛`
is `χ(X, 𝓛) - χ(X, 𝒪_X)` ([Stacks, Tag 0AYR]), and `𝓛` is ample exactly when that degree is
positive ([Stacks, Tag 0B5X]). So when `χ(X, 𝒪_X) = 1` an ample `𝓛` has `χ(X, 𝓛) ≥ 2`. On a
scheme isomorphic over `k` to `𝐏¹_k` the hypothesis holds: `H⁰(X, 𝒪_X) = k`, the genus is `0`,
and cohomology vanishes above degree one, so `χ(X, 𝒪_X) = 1 - 0 = 1`.

Euler characteristics here are
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum`, the alternating sum of
`dim_k Hⁿ(X, -)` taken over all `n : ℕ` with `finsum`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `eulerSum_eq_invertibleCurveDegree_add_eulerSum_unit`: `χ(𝓛) = deg 𝓛 + χ(𝒪_X)`, the
  definition of the degree read backwards.
* `eulerSum_unit_eq_one_sub_genus_of_isIso_globalSections`: `χ(𝒪_X) = 1 - g` on a proper scheme
  of dimension at most one with `H⁰(X, 𝒪_X) = k`.
* `two_le_eulerSum_of_isAmple_of_eulerSum_unit_eq_one`: on a proper curve with `χ(𝒪_X) = 1`, an
  ample invertible module has `χ ≥ 2`.
* `eulerSum_unit_of_iso_projectiveLine`: `χ(𝒪_X) = 1` for `X ≅ 𝐏¹_k` over `k`.
* `two_le_eulerSum_of_isAmple_of_iso_projectiveLine`: **an ample invertible module on a scheme
  isomorphic over `k` to `𝐏¹_k` has `χ ≥ 2`.**

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic (eulerSum)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`χ(X, 𝓛) = deg 𝓛 + χ(X, 𝒪_X)`** for an invertible module on a proper scheme of dimension
at most one over a field: the degree of [Stacks, Tag 0AYR] is defined as the difference. -/
theorem eulerSum_eq_invertibleCurveDegree_add_eulerSum_unit [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    eulerSum k f L =
      invertibleCurveDegree k f hdim L + eulerSum k f (SheafOfModules.unit X.ringCatSheaf) := by
  unfold invertibleCurveDegree eulerSum
  ring

/-- **`χ(X, 𝒪_X) = 1 - g`** for a proper scheme of dimension at most one over a field `k` with
`H⁰(X, 𝒪_X) = k`, where `g` is the genus of [Stacks, Tag 0BY7]. This is
`AlgebraicGeometry.eulerCharacteristic_unit_eq_one_sub_genus` read for `eulerSum`, which has the
same defining sum. -/
theorem eulerSum_unit_eq_one_sub_genus_of_isIso_globalSections [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1) :
    eulerSum k f (SheafOfModules.unit X.ringCatSheaf) = 1 - (genus f : ℤ) := by
  have h := eulerCharacteristic_unit_eq_one_sub_genus k f hdim
  unfold eulerCharacteristic at h
  exact h

/-- **On a proper curve with `χ(𝒪_X) = 1`, an ample invertible module has `χ ≥ 2`.** Its degree
is positive by [Stacks, Tag 0B5X], `AlgebraicGeometry.isAmple_iff_invertibleCurveDegree_pos`,
and `χ(𝓛) = deg 𝓛 + χ(𝒪_X)`. -/
theorem two_le_eulerSum_of_isAmple_of_eulerSum_unit_eq_one [IsCurve k f] [IsProper f]
    (hO : eulerSum k f (SheafOfModules.unit X.ringCatSheaf) = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    2 ≤ eulerSum k f L := by
  have hdim : topologicalKrullDim X ≤ 1 := le_of_eq (IsCurve.topologicalKrullDim_eq_one f)
  have hdeg := (isAmple_iff_invertibleCurveDegree_pos k f hdim L).mp hL
  rw [eulerSum_eq_invertibleCurveDegree_add_eulerSum_unit k f hdim L, hO]
  omega

variable {k} {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
  (e : Z ≅ AlgebraicGeometry.Proj (polyGrading k 1)) (he : e.hom ≫ projToSpecCoeff k 1 = g)

include he in
/-- **`χ(𝒪_Z) = 1` for a scheme `Z` isomorphic over `k` to `𝐏¹_k`**: `H⁰(Z, 𝒪_Z) = k`, the genus
is `0`, and `Z` has dimension one. -/
theorem eulerSum_unit_of_iso_projectiveLine :
    eulerSum k g (SheafOfModules.unit Z.ringCatSheaf) = 1 := by
  have := isProper_of_iso_projectiveLine g e he
  have := isIso_globalSections_of_iso_projectiveLine g e he
  rw [eulerSum_unit_eq_one_sub_genus_of_isIso_globalSections k g
      (topologicalKrullDim_of_iso_projectiveLine e).le,
    genus_of_iso_projectiveLine g e he]
  simp

include he in
/-- **An ample invertible module on a scheme isomorphic over `k` to `𝐏¹_k` has Euler
characteristic at least two.** The scheme is a proper curve
(`AlgebraicGeometry.isCurve_of_iso_projectiveLine`) with `χ(𝒪_Z) = 1`
(`AlgebraicGeometry.eulerSum_unit_of_iso_projectiveLine`), and
`AlgebraicGeometry.two_le_eulerSum_of_isAmple_of_eulerSum_unit_eq_one` applies. -/
theorem two_le_eulerSum_of_isAmple_of_iso_projectiveLine (H : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple Z H) :
    2 ≤ eulerSum k g H := by
  have := isProper_of_iso_projectiveLine g e he
  have := isCurve_of_iso_projectiveLine g e he
  exact two_le_eulerSum_of_isAmple_of_eulerSum_unit_eq_one k g
    (eulerSum_unit_of_iso_projectiveLine g e he) H hH

end AlgebraicGeometry

end
