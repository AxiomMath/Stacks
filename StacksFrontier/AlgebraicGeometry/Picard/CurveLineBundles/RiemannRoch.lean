module

public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Riemann-Roch and the dimension of the space of sections on a proper curve

Let `k` be a field and `X` a proper scheme of dimension at most one over `k` whose only global
regular functions are the constants, of genus `g = h¹(X, 𝒪_X)`. For an invertible `𝒪_X`-module
`ℒ` of degree `deg ℒ` this file collects the numerical facts about `h⁰(ℒ)` and `h¹(ℒ)` that the
construction of the Jacobian uses:

* **Riemann-Roch**: `χ(ℒ) = h⁰(ℒ) - h¹(ℒ) = deg ℒ + 1 - g`;
* **vanishing in large degree**: if `deg ℒ > 2g - 2` then `H¹(X, ℒ) = 0`, hence
  `h⁰(ℒ) = deg ℒ + 1 - g`, when `k` is algebraically closed and `X` is a curve;
* **the bounds on `h⁰`**: `h⁰(ℒ) = 0` when `deg ℒ < 0`, and
  `deg ℒ + 1 - g ≤ h⁰(ℒ) ≤ deg ℒ + 1` when `deg ℒ ≥ 0`.

Over an algebraically closed field the hypothesis on the global functions holds for every proper
integral scheme (`AlgebraicGeometry.isIso_globalSections_of_isAlgClosed`), so for a curve over
such a field all of these hold with no further hypothesis; in particular they hold for a smooth
projective curve.

Riemann-Roch itself is the definition of the degree, `deg ℒ = χ(ℒ) - χ(𝒪_X)`, read with
`χ(𝒪_X) = 1 - g`; the vanishing is [Stacks, Tag 0B90]
(`isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree`);
the vanishing of `H⁰` in negative degree is part (1) of [Stacks, Tag 0B40]; the upper bound is
[Stacks, Tag 0CCS] applied to the complete linear system of `ℒ`.

## Main results

* `isIso_globalSections_of_isAlgClosed`: `H⁰(X, 𝒪_X) = k` for `X` proper and integral over an
  algebraically closed field.
* `finrank_cohomologyOverField_zero_sub_one_eq_invertibleCurveDegree_add_one_sub_genus` and
  `eulerCharacteristic_eq_invertibleCurveDegree_add_one_sub_genus`: Riemann-Roch.
* `isZero_cohomologyOverField_one_of_two_mul_genus_sub_two_lt_invertibleCurveDegree` and
  `finrank_cohomologyOverField_zero_eq_of_two_mul_genus_sub_two_lt_invertibleCurveDegree`: the
  large-degree case.
* `isZero_cohomologyOverField_zero_of_invertibleCurveDegree_neg`,
  `finrank_cohomologyOverField_zero_le_invertibleCurveDegree_add_one` and
  `invertibleCurveDegree_add_one_sub_genus_le_finrank_cohomologyOverField_zero`: the bounds on
  `h⁰`.

## Implementation notes

The degree is `AlgebraicGeometry.invertibleCurveDegree`, which takes a proof `hdim` of
`topologicalKrullDim X ≤ 1`; every statement here takes `hdim` as an argument, and since it is a
proof of a proposition any two choices give the same degree. Invertibility is
`AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2`, the spelling
`invertibleCurveDegree` is written over; it is definitionally the spelling
`X.sheaf.obj X.ringCatSheaf.property` that the cited results take.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0B90](https://stacks.math.columbia.edu/tag/0B90)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0CCS](https://stacks.math.columbia.edu/tag/0CCS)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **On a scheme proper and integral over an algebraically closed field the only global regular
functions are the constants.** The ring of global functions is a finite-dimensional `k`-algebra
([Stacks, Tag 0BUG] (1)) and a domain, hence integral over `k`, hence equal to `k`. -/
theorem isIso_globalSections_of_isAlgClosed [IsAlgClosed k] [IsProper f] [IsIntegral X] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Module.Finite k Γ(X, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k f
  have : Algebra.IsIntegral k Γ(X, ⊤) := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k Γ(X, ⊤)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-! ### Riemann-Roch -/

/-- **Riemann-Roch**: on a proper scheme of dimension at most one over `k` whose only global
functions are the constants, `h⁰(ℒ) - h¹(ℒ) = deg ℒ + 1 - g` for every invertible `ℒ`.

The degree is `χ(ℒ) - χ(𝒪_X)` by definition, both Euler characteristics stop at `H¹` by
[Stacks, Tag 02UZ], and `h⁰(𝒪_X) = 1`. -/
theorem finrank_cohomologyOverField_zero_sub_one_eq_invertibleCurveDegree_add_one_sub_genus
    [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) -
        Module.finrank k (cohomologyOverField k f L 1) =
      invertibleCurveDegree k f hdim L + 1 - genus f := by
  have h := finrank_cohomologyOverField_zero_sub_one_eq k f hdim L hL
  rw [finrank_cohomologyOverField_unit_zero_eq_one f, Nat.cast_one] at h
  exact h

/-- **Riemann-Roch, as an identity of Euler characteristics**: `χ(ℒ) = deg ℒ + 1 - g` for every
invertible `ℒ` on a proper scheme of dimension at most one over `k` whose only global functions
are the constants. -/
theorem eulerCharacteristic_eq_invertibleCurveDegree_add_one_sub_genus [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [L.IsCoherent] :
    eulerCharacteristic k f L = invertibleCurveDegree k f hdim L + 1 - genus f := by
  rw [eulerCharacteristic_eq_sub_of_isZero k f L fun m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k f L (d := 1) (i := m) hdim hm]
  exact finrank_cohomologyOverField_zero_sub_one_eq_invertibleCurveDegree_add_one_sub_genus
    k f hdim L

/-- **The lower bound of Riemann-Roch**: `deg ℒ + 1 - g ≤ h⁰(ℒ)`. -/
@[sga "4 XVIII 1.3.2.1" "special case"]
theorem invertibleCurveDegree_add_one_sub_genus_le_finrank_cohomologyOverField_zero [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hdim L + 1 - genus f ≤
      (Module.finrank k (cohomologyOverField k f L 0) : ℤ) := by
  have := finrank_cohomologyOverField_zero_sub_one_eq_invertibleCurveDegree_add_one_sub_genus
    k f hdim L
  omega

/-! ### Large degree -/

/-- **Vanishing in large degree**: on a proper curve over an algebraically closed field,
`H¹(X, ℒ) = 0` for every invertible `ℒ` with `deg ℒ > 2g - 2`. This is [Stacks, Tag 0B90]. -/
@[sga "4 XVIII 1.3.2.1" "special case"]
theorem isZero_cohomologyOverField_one_of_two_mul_genus_sub_two_lt_invertibleCurveDegree
    [IsAlgClosed k] [IsProper f] [IsCurve k f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 2 * (genus f : ℤ) - 2 < invertibleCurveDegree k f hdim L) :
    IsZero (cohomologyOverField k f L 1) :=
  isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree k f L hL
    (by omega)

/-- **The dimension of the space of sections in large degree**: on a proper curve over an
algebraically closed field, `h⁰(ℒ) = deg ℒ + 1 - g` for every invertible `ℒ` of degree at least
`2g - 1`. -/
@[sga "4 XVIII 1.3.2.1" "special case"]
theorem finrank_cohomologyOverField_zero_eq_of_two_mul_genus_sub_two_lt_invertibleCurveDegree
    [IsAlgClosed k] [IsProper f] [IsCurve k f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 2 * (genus f : ℤ) - 2 < invertibleCurveDegree k f hdim L) :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) =
      invertibleCurveDegree k f hdim L + 1 - genus f := by
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  have hrr := finrank_cohomologyOverField_zero_sub_one_eq_invertibleCurveDegree_add_one_sub_genus
    k f hdim L
  have hone : Module.finrank k (cohomologyOverField k f L 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_one_of_two_mul_genus_sub_two_lt_invertibleCurveDegree
        k f hdim L hdeg)
    Module.finrank_zero_of_subsingleton
  rw [hone, Nat.cast_zero, sub_zero] at hrr
  exact hrr

/-! ### Bounds on the space of sections -/

/-- **An invertible module of negative degree has no nonzero global section**: on a proper
integral scheme of dimension at most one over `k`, `H⁰(X, ℒ) = 0` when `deg ℒ < 0`. A nonzero
section would make the degree nonnegative, by part (1) of [Stacks, Tag 0B40]. -/
@[sga "7 X 1.13" "more general"]
theorem isZero_cohomologyOverField_zero_of_invertibleCurveDegree_neg [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : invertibleCurveDegree k f hdim L < 0) :
    IsZero (cohomologyOverField k f L 0) := by
  have hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  refine ModuleCat.isZero_iff_subsingleton.mpr ?_
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨s, hs⟩ := exists_eval_top_ne_zero_of_nontrivial_cohomologyOverField_zero f L hns
  have := invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim L s hs
  omega

/-- **The upper bound on the space of sections**: on a proper curve over `k` whose only global
functions are the constants, `h⁰(ℒ) ≤ deg ℒ + 1` for every invertible `ℒ` of nonnegative degree.

When `H⁰(X, ℒ) ≠ 0` the whole of `H⁰(X, ℒ)` is a linear series of degree `deg ℒ` and dimension
`h⁰(ℒ) - 1`, and [Stacks, Tag 0CCS] bounds that dimension by the degree. -/
theorem finrank_cohomologyOverField_zero_le_invertibleCurveDegree_add_one [IsProper f]
    [IsCurve k f] (hdim : topologicalKrullDim X ≤ 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : 0 ≤ invertibleCurveDegree k f hdim L) :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) ≤
      invertibleCurveDegree k f hdim L + 1 := by
  rcases Nat.eq_zero_or_pos (Module.finrank k (cohomologyOverField k f L 0)) with h0 | hpos
  · rw [h0]; omega
  · let series : LinearSeries k f hdim (invertibleCurveDegree k f hdim L).toNat
        (Module.finrank k (cohomologyOverField k f L 0) - 1) :=
      { L := L
        isInvertible := hL
        degree_eq := (Int.toNat_of_nonneg hdeg).symm
        V := ⊤
        finrank_eq := by rw [finrank_top]; omega }
    have := linearSeries_dimension_le_degree f series
    omega

end AlgebraicGeometry

end
