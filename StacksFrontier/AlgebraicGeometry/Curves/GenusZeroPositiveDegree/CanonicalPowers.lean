module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveEmbedding
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafRank
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalGenerationLargeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SubcurveFieldExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible

/-!
# Powers of a module of canonical degree on an integral curve

Let `X` be a proper integral curve over `k` with `H⁰(X, 𝒪_X) = k` and genus `g`, and let `𝒩` be an
invertible module of degree `2g - 2` — the degree of the dualizing sheaf of a Gorenstein curve
([Stacks, Tag 0C19]). This file records what the results of the section on genus-zero curves and
on global generation say about the powers of `𝒩`; these are the irreducible cases of
[Stacks, Tag 0E3K].

## Main results

* `AlgebraicGeometry.isRelativelyVeryAmple_tensorPower_neg_one_of_genus_eq_zero`: for `g = 0`,
  `𝒩^{⊗ -1}` is very ample.
* `AlgebraicGeometry.isGeneratedByGlobalSections_tensorPower_of_two_le_genus`: for `g ≥ 2`, every
  power `𝒩^{⊗ m}` with `m ≥ 2` is globally generated.
* `AlgebraicGeometry.isGeneratedByGlobalSections_tensorPower_of_subcurve_bound`: the same on a
  reduced curve, given `dim H¹(Y, 𝒪_Y) ≤ deg(𝒩|_Y)` on proper subcurves ([Stacks, Tag 0E3F]).

## References

* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
* [Stacks Project, Tag 0E3C](https://stacks.math.columbia.edu/tag/0E3C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **In genus zero the inverse of a module of degree `-2` is very ample.** On a proper integral
curve over `k` with `H⁰(X, 𝒪_X) = k` and genus `0`, an invertible module `𝒩` of degree `-2` has
`𝒩^{⊗ -1}` of degree `2`, hence very ample by [Stacks, Tag 0C6T] part (2). -/
theorem isRelativelyVeryAmple_tensorPower_neg_one_of_genus_eq_zero [IsProper f] [IsIntegral X]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    (hgenus : genus f = 0) (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hN : invertibleCurveDegree k f hdim N = -2) :
    letI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N (-1)
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f
      (tensorPower X.presheaf X.ringCatSheaf.2 N (-1)) := by
  let hL := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N (-1)
  set L := tensorPower X.presheaf X.ringCatSheaf.2 N (-1)
  have hdeg : invertibleCurveDegree k f hdim L = 2 := by
    rw [invertibleCurveDegree_tensorPower k f hdim N (-1), hN]
    norm_num
  let M := (restrictScalarsOverBase k f).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj L)
  have hfin : Module.finrank k M = 3 := by
    have := finrank_globalSections_eq_invertibleCurveDegree_add_one k f hdim L hgenus
      (by rw [hdeg]; norm_num)
    rw [hdeg] at this
    exact_mod_cast this
  have : Module.Finite k M := Module.finite_of_finrank_eq_succ hfin
  let b : Module.Basis (Fin (2 + 1)) k M := Module.finBasisOfFinrankEq k M hfin
  exact (isRelativelyVeryAmple_and_isClosedImmersion_of_basis f hdim hgenus L
    (d := 2) (by exact_mod_cast hdeg) two_pos b).1

/-- **In genus at least two the powers of a module of degree `2g - 2` are globally generated.**
On a proper integral curve over `k` with `H⁰(X, 𝒪_X) = k` and genus `g ≥ 2`, an invertible module
`𝒩` of degree `2g - 2` has `𝒩^{⊗ m}` globally generated for every `m ≥ 2`: its degree
`m(2g - 2)` is at least `2g` ([Stacks, Tag 0E3C]). -/
theorem isGeneratedByGlobalSections_tensorPower_of_two_le_genus [IsProper f] [IsIntegral X]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X = 1)
    (hgenus : 2 ≤ genus f) (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hN : invertibleCurveDegree k f hdim.le N = 2 * (genus f : ℤ) - 2) (m : ℕ) (hm : 2 ≤ m) :
    SheafOfModules.IsGeneratedByGlobalSections (tensorPower X.presheaf X.ringCatSheaf.2 N m) := by
  let := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N m
  let S : CohenMacaulayCurveSituation.{u} := ⟨k, X, f, hdim⟩
  refine CohenMacaulayCurveSituation.isGeneratedByGlobalSections_of_two_mul_genus_le (S := S)
    (tensorPower X.presheaf X.ringCatSheaf.2 N m) ?_
  change 2 * (genus f : ℤ) ≤ invertibleCurveDegree k f hdim.le _
  rw [invertibleCurveDegree_tensorPower k f hdim.le N m, hN]
  have hg : (2 : ℤ) ≤ genus f := by exact_mod_cast hgenus
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- **On a reduced curve the powers of a module of degree `2g - 2` with large restrictions are
globally generated.** Let `X` be a proper reduced scheme of dimension one over `k` with
`H⁰(X, 𝒪_X) = k` and genus `g ≥ 2`, and let `𝒩` be invertible of degree `2g - 2` such that
`dim_k H¹(Y, 𝒪_Y) ≤ deg(𝒩|_Y)` for every proper subcurve `Y ⊊ X`. Then `𝒩^{⊗ m}` is globally
generated for every `m ≥ 2`.

This is the split form of [Stacks, Tag 0E3F]
(`AlgebraicGeometry.isGeneratedByGlobalSections_of_subcurve_bounds`): on a proper subcurve
`deg(𝒩^{⊗ m}|_Y) = m · deg(𝒩|_Y) ≥ 2 dim H¹(Y, 𝒪_Y)`, and on `X` itself the two inequalities
read `2g - 2 < m(2g - 2)` and `2g < m(2g - 2) + 1`. -/
theorem isGeneratedByGlobalSections_tensorPower_of_subcurve_bound [IsProper f] [IsReduced X]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X = 1)
    (hgenus : 2 ≤ genus f) (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hdeg : invertibleCurveDegree k f hdim.le N = 2 * (genus f : ℤ) - 2)
    (hsub : ∀ (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
      (hY : topologicalKrullDim Y.subscheme = 1), Y ≠ ⊥ →
      letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι N hN
      (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) ≤
        invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj N))
    (m : ℕ) (hm : 2 ≤ m) :
    SheafOfModules.IsGeneratedByGlobalSections (tensorPower X.presheaf X.ringCatSheaf.2 N m) := by
  let hNm := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N m
  have hg : (2 : ℤ) ≤ genus f := by exact_mod_cast hgenus
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hdegm : invertibleCurveDegree k f hdim.le (tensorPower X.presheaf X.ringCatSheaf.2 N m) =
      m * (2 * (genus f : ℤ) - 2) := by
    rw [invertibleCurveDegree_tensorPower k f hdim.le N m, hdeg]
  have h0 := finrank_cohomologyOverField_unit_zero_eq_one f
  have h1 := finrank_cohomologyOverField_one_unit_eq_genus k f
  refine isGeneratedByGlobalSections_of_subcurve_bounds f hdim.le _ ?_ ?_ ?_
  · intro Y _ _ hY hY0
    have hP : SheafOfModules.IsInvertible Y.subscheme.presheaf Y.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback Y.subschemeι).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 N m)) :=
      Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι _ hNm
    have hQ : SheafOfModules.IsInvertible Y.subscheme.presheaf Y.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback Y.subschemeι).obj N) :=
      Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι N hN
    have hb := hsub Y hY hY0
    rw [invertibleCurveDegree_pullback_tensorPower Y.subschemeι (Y.subschemeι ≫ f) hY.le N m
      (hP := hP) (hQ := hQ)]
    have hnn : (0 : ℤ) ≤ (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) := by positivity
    nlinarith
  all_goals
    rw [hdegm, h0, h1]
    have := mul_le_mul_of_nonneg_right hm' (show (0 : ℤ) ≤ 2 * (genus f : ℤ) - 2 by linarith)
    push_cast
    linarith

end AlgebraicGeometry

end
