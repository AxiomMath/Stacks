module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Ratio
public import StacksFrontier.AlgebraicGeometry.SectionRingProjOverlap.Basic

/-!
# One exponent for every chart: the degree equalisation of step 2 of Stacks Tag 01VS

Let `X` be a scheme, `L` an **ample** invertible `𝒪_X`-module and `a i` a family of homogeneous
elements of one positive degree `d` of the graded section ring `Γ_*(X, L)` of Stacks Tag 01CV.
Step 2 of the proof of Stacks Tag 01VS writes finitely many functions on each chart `X_{a i}` as
ratios whose denominator is a power of `a i`, and then **equalises the exponents**: one single
`e` serving every chart and every function at once, so that all the numerators and all the
denominators are homogeneous of the one degree `d e` and can be collected into a *single* family
of global sections of `L ^⊗ (d e)`.

That last move is what this file supplies, and it is the only thing between the two proved
halves of step 2 and the family that `Stacks.AmpleImmersionReduction.ChartImmersion` quantifies
over.

## What was already there, and what was missing

* `Stacks.SectionRingChartBijective.exists_ratio_powSec` writes **one** function on **one** chart
  as a ratio with the denominator a genuine power of `a` — but as `(a^{N₀})^m`, a power of a
  power, in a degree `d N₀ m` that depends on the function.

That does not give one degree across *several* charts, which is what a single family of sections
of a single `L ^⊗ N` needs. Supplying it is exactly the arithmetic of exponents, and it is done
here in three steps: the power of a power is normalised to a single power
(`Stacks.ChartDegreeEqualisation.powSec_powSec`), a ratio's exponent is raised at will by
multiplying the numerator by a further power of the denominator
(`Stacks.ChartDegreeEqualisation.exists_ratio_powSec_of_le`), and the finitely many exponents a
finite family of charts produces are raised to their maximum
(`Stacks.ChartDegreeEqualisation.exists_common_exponent_ratio`).

Raising is available precisely because the denominator is a power of `a`: a ratio `t / a^k` is
also `t a^r / a^{k+r}`, and `X_{a^{k+r}} = X_a` is untouched. A denominator recorded only up to
its nonvanishing locus cannot be raised this way, which is why the first of the two proved halves
is the one this file builds on.

## Main results

* `Stacks.ChartDegreeEqualisation.resTop_ratio_mul`: a ratio relation between global sections is
  multiplied through by a homogeneous element.
* `Stacks.ChartDegreeEqualisation.powSec_powSec`: a power of a power is a power, modulo the
  degree transport `d N m = d (N m)`.
* `Stacks.ChartDegreeEqualisation.mul_powSec_powSec`: powers multiply, modulo `d r + d k =
  d (r + k)`.
* `Stacks.ChartDegreeEqualisation.exists_ratio_powSec_of_le`: **the exponent of a ratio may be
  raised.**
* `Stacks.ChartDegreeEqualisation.exists_ratio_powSec'`: one function on one chart as a ratio
  with denominator a *single* power of `a`.
* `Stacks.ChartDegreeEqualisation.exists_common_exponent_ratio`: **the deliverable.** For a finite
  family of charts `X_{a i}` and, on each, a finite family of functions, one exponent `e ≥ 1` and
  numerators `t i j` of the single degree `d e` with `g i j = t i j / (a i)^e` on `X_{a i}`.
* `Stacks.ChartDegreeEqualisation.exists_common_exponent_ratio_tensorPow`: the same in the
  `Stacks.Ample.tensorPowModule` vocabulary the consumers of the ample cluster are stated over,
  with the chart recorded as `X_{(a i)^e}` so that denominator and numerators are global sections
  of one and the same module.
* `Stacks.ChartDegreeEqualisation.ratio_eq_of_resTop_eq`: a ratio relation between two members of
  a family of global sections identifies the coordinate ratio
  `Stacks.ProjectiveFromSections.ratio` of that family, and
  `Stacks.ChartDegreeEqualisation.chartRatio_eq_of_resTop_eq` reads that on the chart as a scheme.
* `Stacks.ChartDegreeEqualisation.exists_family_ratio_eq`: **the equalised family.** Denominators
  and numerators collected into one family of global sections of one `L ^⊗ N`, generating every
  stalk, with the prescribed functions appearing as its coordinate ratios out of each chart.

## No Stacks attribute is attached

Nothing here is a statement of the Stacks Project. It is the exponent arithmetic that the second
step of the proof of Stacks Tag 01VS performs silently, between Tag 01PW and the family of
sections that defines the morphism of Tag 01NE.

## What is not done

Three things separate `Stacks.ChartDegreeEqualisation.exists_family_ratio_eq` from
`Stacks.AmpleImmersionReduction.ChartImmersion`, and none of them is exponent arithmetic.

1. **The index type.** The family here is indexed by `ι ⊕ (Σ i, κ i)`; the construction of a
   morphism to `ℙⁿ_S` consumes a `Fin (n + 1)`-indexed one. Re-indexing along an equivalence and
   padding with the zero section is what
   `Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple` does for the covering
   family alone, and it is not done here.
2. **The functions.** Nothing here produces the `g i j`. Stacks Tag 01T2 is formalized as
   `Stacks.AmpleChartsOverBase.exists_generating_family_finiteType_of_isAmple`, whose per-chart
   datum is `RingHom.FiniteType (f.appLE V (nvCover s i) e).hom`; turning that into a finite
   subset of `Γ(X, X_{a i})` generating it as an `Γ(S, V i)`-algebra — an
   `Algebra.adjoin … = ⊤` — is a separate step.
3. **The chart dictionary**, which is the real obstruction. Even with 1 and 2 there is no
   declaration identifying the restricted morphism
   `X_{a i} ⟶ D₊(T i) ⊓ pr⁻¹(V i)` of `Stacks.ChartImmersionAssembly.chartOpenOver` with the
   ring map sending `T k / T i` to the `k`-th coordinate ratio. Without it
   `Stacks.ChartImmersionAssembly.isImmersion_chartImmersion_of_adjoin`, which is exactly the
   one-chart immersion statement at an `Algebra.adjoin` generating set, cannot be applied, and
   that file's own "What is not done" records the same gap and names the handle it would need
   (`Stacks.SectionsToProjectiveSpace.resLE_toProjectiveSpaceAtUniverse`).

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul powCongr powCongr_rfl)
open Stacks.SectionProduct (globalSection globalSection_mul globalSection_comp)
open Stacks.SectionRingProjOverlap (of_pow_eq_of_powSec)
open Stacks.SectionExtension (powSec resTop resTop_app_of_res_eq nvLocus_powSec_of_one_le
  exists_forall_le)

universe u

namespace Stacks.ChartDegreeEqualisation

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules)

/-! ### Reading an identity of homogeneous elements off the section ring -/

/-- **`DirectSum.of` is injective at a fixed degree.** Two homogeneous elements of the same degree
with the same image in `Γ_*(X, L)` are equal; the degree-`m` coordinate of `DirectSum.of _ m s` is
`s`. This is how the identities below are transported back from the ring, where `pow_add` and
`pow_mul` are available, to the sections the geometry is stated about. -/
theorem eq_of_of_eq {m : ℕ} {s t : powSections L m}
    (h : DirectSum.of (powSections L) m s = DirectSum.of (powSections L) m t) : s = t := by
  simpa using congrArg (fun z : DirectSum ℕ (powSections L) => z m) h

/-- **A degree transport is invisible in the section ring.** Composing a homogeneous element with
`Stacks.GradedSections.powCongr` along an equality of degrees does not change its image under
`DirectSum.of`. The two degrees are variables here, so the equality can be eliminated by `subst`;
at the compound degrees the identities below are stated at, it cannot be. -/
theorem of_comp_powCongr {n m : ℕ} (h : n = m) (s : powSections L n) :
    DirectSum.of (powSections L) m (s ≫ powCongr L h) = DirectSum.of (powSections L) n s := by
  subst h
  rw [powCongr_rfl, Category.comp_id]

/-! ### The exponent arithmetic of `powSec` -/

/-- **A power of a power is a power**, modulo the transport along `d N m = d (N m)` that the
grading forces. `Stacks.SectionRingChartBijective.exists_ratio_powSec` hands its denominator over
as `(a^N)^m`; this is what turns it into `a^{N m}`. -/
theorem powSec_powSec {d : ℕ} (a : powSections L d) (N m : ℕ) (h : d * N * m = d * (N * m)) :
    powSec L (powSec L a N) m ≫ powCongr L h = powSec L a (N * m) := by
  refine eq_of_of_eq L ?_
  rw [of_comp_powCongr, ← of_pow_eq_of_powSec, ← of_pow_eq_of_powSec, ← pow_mul,
    of_pow_eq_of_powSec]

/-- **Powers of one homogeneous element multiply**, modulo the transport along
`d r + d k = d (r + k)`. This is what raises the exponent of a ratio: multiplying a relation
`t|_U = g · (a^k)|_U` through by `a^r` produces `a^r a^k` as the denominator, and this identifies
it with `a^{r + k}`. -/
theorem mul_powSec_powSec {d : ℕ} (a : powSections L d) (r k : ℕ)
    (h : d * r + d * k = d * (r + k)) :
    mul (powSec L a r) (powSec L a k) ≫ powCongr L h = powSec L a (r + k) := by
  refine eq_of_of_eq L ?_
  rw [of_comp_powCongr, ← Stacks.SectionProduct.of_mul_of, ← of_pow_eq_of_powSec,
    ← of_pow_eq_of_powSec, ← pow_add, of_pow_eq_of_powSec]

/-! ### Moving a ratio relation -/

/-- **A ratio relation is multiplied through by a homogeneous element.** If `t|_U = g · σ|_U` for
global sections of one tensor power, then `(u t)|_U = g · (u σ)|_U`: the product by `u` is a
morphism of `𝒪_X`-modules applied to the second factor
(`Stacks.SectionProduct.globalSection_mul`), and every such morphism preserves a ratio relation
(`Stacks.SectionExtension.resTop_app_of_res_eq`). -/
theorem resTop_ratio_mul {p q : ℕ} (u : powSections L p) {t σ : powSections L q} {U : X.Opens}
    (g : Γ(X, U))
    (hts : resTop U (globalSection X _ t) = g • resTop U (globalSection X _ σ)) :
    resTop U (globalSection X _ (mul u t)) = g • resTop U (globalSection X _ (mul u σ)) := by
  rw [globalSection_mul, globalSection_mul]
  exact resTop_app_of_res_eq _ g _ _ hts

/-- **A ratio relation survives a degree transport.** The two degrees are variables, so this is
`subst` and nothing else; it is stated because at the compound degrees of this file the transport
cannot be eliminated in place. -/
theorem resTop_ratio_powCongr {n m : ℕ} (h : n = m) {t σ : powSections L n} {U : X.Opens}
    (g : Γ(X, U))
    (hts : resTop U (globalSection X _ t) = g • resTop U (globalSection X _ σ)) :
    resTop U (globalSection X _ (t ≫ powCongr L h))
      = g • resTop U (globalSection X _ (σ ≫ powCongr L h)) := by
  subst h
  simpa using hts

/-- A ratio relation survives a degree transport, with the transported denominator named. -/
private theorem resTop_ratio_powCongr_of_eq {n m : ℕ} (h : n = m) {t σ : powSections L n}
    {σ' : powSections L m} {U : X.Opens} (g : Γ(X, U)) (hσ : σ ≫ powCongr L h = σ')
    (hts : resTop U (globalSection X _ t) = g • resTop U (globalSection X _ σ)) :
    resTop U (globalSection X _ (t ≫ powCongr L h)) = g • resTop U (globalSection X _ σ') :=
  hσ ▸ resTop_ratio_powCongr L h g hts

/-! ### Raising the exponent of a ratio -/

/-- **The exponent of a ratio may be raised at will.** If a function `g` on an open `U` is the
ratio of a homogeneous element of degree `d k` by `a^k`, it is also the ratio of one of degree
`d e` by `a^e`, for every `e ≥ k`: multiply numerator and denominator by `a^{e - k}`.

No hypothesis relates `U` to a nonvanishing locus — this is an identity between restrictions — and
no ampleness is used. It is here that the denominator being a *genuine power* of `a` is spent: a
denominator known only up to its nonvanishing locus has no `a^{e - k}` to be multiplied by. -/
theorem exists_ratio_powSec_of_le {d : ℕ} (a : powSections L d) {U : X.Opens} (g : Γ(X, U))
    {k e : ℕ} (hke : k ≤ e) (t : powSections L (d * k))
    (ht : resTop U (globalSection X _ t) = g • resTop U (globalSection X _ (powSec L a k))) :
    ∃ t' : powSections L (d * e),
      resTop U (globalSection X _ t')
        = g • resTop U (globalSection X _ (powSec L a e)) := by
  obtain ⟨r, rfl⟩ : ∃ r, e = r + k := ⟨e - k, by omega⟩
  have hdeg : d * r + d * k = d * (r + k) := by ring
  refine ⟨mul (powSec L a r) t ≫ powCongr L hdeg, ?_⟩
  exact resTop_ratio_powCongr_of_eq L hdeg g (mul_powSec_powSec L a r k hdeg)
    (resTop_ratio_mul L (powSec L a r) g ht)

/-! ### One chart, one function, a single power -/

variable [Stacks.Ample.IsInvertibleModule X L]

/-- **A function on `X_a` is a global section divided by a single power of `a`.**
`Stacks.SectionRingChartBijective.exists_ratio_powSec` with its power of a power normalised by
`Stacks.ChartDegreeEqualisation.powSec_powSec`: the exponent is one natural number `k ≥ 1` and the
numerator is homogeneous of the one degree `d k`. -/
theorem exists_ratio_powSec' (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d) (a : powSections L d)
    (g : Γ(X, nvOpen L a)) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ t : powSections L (d * k),
      resTop (nvOpen L a) (globalSection X _ t)
        = g • resTop (nvOpen L a) (globalSection X _ (powSec L a k)) := by
  obtain ⟨N₀, m, hN₀, hm, t, ht⟩ :=
    Stacks.SectionRingChartBijective.exists_ratio_powSec L hL hd a g
  have hdeg : d * N₀ * m = d * (N₀ * m) := by ring
  refine ⟨N₀ * m, Nat.mul_pos (by omega) (by omega),
    t ≫ powCongr L hdeg, ?_⟩
  exact resTop_ratio_powCongr_of_eq L hdeg g (powSec_powSec L a N₀ m hdeg) ht

/-! ### The deliverable: one exponent for every chart -/

/-- **The equalisation of the degrees.** Let `L` be ample, let `a : ι → powSections L d` be a
finite family of homogeneous elements of one positive degree `d` — the charts `X_{a i}` — and let
`g i : κ i → Γ(X, X_{a i})` be, on each chart, a finite family of functions. Then there is a
**single** exponent `e ≥ 1` and numerators `t i j`, all homogeneous of the **single** degree
`d e`, with

`g i j = t i j / (a i)^e`   on `X_{a i}`.

The denominators `(a i)^e` are homogeneous of that same degree `d e`, so the numerators and the
denominators together are a family of global sections of one and the same `L ^⊗ (d e)`, and
`Stacks.SectionExtension.nvLocus_powSec_of_one_le` says the chart is unchanged:
`X_{(a i)^e} = X_{a i}`.

This is the clause the docstring of `Stacks.AmpleImmersionReduction.ChartImmersion` calls "the
equalisation of the degrees". The exponent is the maximum of the finitely many exponents that
`Stacks.ChartDegreeEqualisation.exists_ratio_powSec'` returns, raised to it one ratio at a time by
`Stacks.ChartDegreeEqualisation.exists_ratio_powSec_of_le`. -/
theorem exists_common_exponent_ratio (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Finite ι] (a : ι → powSections L d)
    {κ : ι → Type*} [∀ i, Finite (κ i)] (g : ∀ i, κ i → Γ(X, nvOpen L (a i))) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ t : ∀ i, κ i → powSections L (d * e),
      ∀ (i : ι) (j : κ i),
        resTop (nvOpen L (a i)) (globalSection X _ (t i j))
          = g i j • resTop (nvOpen L (a i)) (globalSection X _ (powSec L (a i) e)) := by
  classical
  choose k hk t ht using fun (i : ι) (j : κ i) => exists_ratio_powSec' L hL hd (a i) (g i j)
  obtain ⟨K, hK⟩ := exists_forall_le fun q : Sigma κ => k q.1 q.2
  refine ⟨K + 1, by omega, ?_⟩
  choose t' ht' using fun (i : ι) (j : κ i) =>
    exists_ratio_powSec_of_le L (a i) (g i j)
      (le_trans (hK ⟨i, j⟩) (Nat.le_succ K)) (t i j) (ht i j)
  exact ⟨t', ht'⟩

/-- **The equalisation of the degrees, in the `Stacks.Ample.tensorPowModule` vocabulary.** The
consumers of the ample cluster — `Stacks.AmpleImmersionReduction.ChartImmersion` among them — are
stated over honest global sections of `Stacks.Ample.tensorPowModule X L N` rather than over
homogeneous elements of the section ring, and
`Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow` is an equality of modules, so the passage
is an `eqToIso`.

The chart is recorded as the nonvanishing open of the denominator `σ i` itself, which is where
`Stacks.SectionExtension.nvLocus_powSec_of_one_le` is spent: the denominator is a positive power
of `a i`, so its nonvanishing open is `X_{a i}` and nothing about the cover changes. -/
theorem exists_common_exponent_ratio_tensorPow (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Finite ι] (a : ι → powSections L d)
    {κ : ι → Type*} [∀ i, Finite (κ i)] (g : ∀ i, κ i → Γ(X, nvOpen L (a i))) :
    ∃ (N : ℕ) (σ : ι → Γ(tensorPowModule X L (N : ℤ), ⊤))
      (b : ∀ i, κ i → Γ(tensorPowModule X L (N : ℤ), ⊤)), 1 ≤ N ∧
      (∀ i, nonvanishingOpen X (tensorPowModule X L (N : ℤ)) (σ i) = nvOpen L (a i)) ∧
        ∀ (i : ι) (j : κ i),
          resTop (nvOpen L (a i)) (b i j) = g i j • resTop (nvOpen L (a i)) (σ i) := by
  obtain ⟨e, he, t, ht⟩ := exists_common_exponent_ratio L hL hd a g
  have hmod : (natTensorPow L (d * e) : X.Modules) = tensorPowModule X L ((d * e : ℕ) : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L (d * e)
  refine ⟨d * e, fun i => (eqToIso (C := X.Modules) hmod).hom.app ⊤
      (globalSection X _ (powSec L (a i) e)),
    fun i j => (eqToIso (C := X.Modules) hmod).hom.app ⊤ (globalSection X _ (t i j)),
    Nat.mul_pos (by omega) (by omega), fun i => ?_,
    fun i j => ?_⟩
  · refine TopologicalSpace.Opens.ext ?_
    rw [coe_nonvanishingOpen,
      nonvanishingLocus_congr (eqToIso (C := X.Modules) hmod)
        (globalSection X _ (powSec L (a i) e)), coe_nvOpen]
    exact nvLocus_powSec_of_one_le L (a i) e he
  · rw [Stacks.SectionExtension.resTop_app, Stacks.SectionExtension.resTop_app, ht i j,
      Scheme.Modules.Hom.app_smul]

end Monoidal

/-! ### The equalised data as the coordinate ratios of one family -/

section Ratios

variable {X : Scheme.{u}} {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]

/-- **A ratio relation identifies the coordinate ratio.** If the restriction of `s k` to the
chart `X_{s i}` is `g` times the restriction of `s i`, then `g` *is* the coordinate ratio
`s k / s i` of `Stacks.ProjectiveFromSections.ratio` — the ratio is the unique such section
(`Stacks.ProjectiveFromSections.eq_div`).

The chart is given as an open `U` equal to `X_{s i}` rather than as `X_{s i}` itself, because the
equalisation above produces its functions on the chart of the element the denominator is a power
of; the two opens are equal, and the restriction along that equality is the identity once the
equality is eliminated. -/
theorem ratio_eq_of_resTop_eq {ι : Type*} (s : ι → Γ(M, ⊤)) (i k : ι) {U : X.Opens}
    (hU : Stacks.ProjectiveFromSections.nvCover s i = U) (g : Γ(X, U))
    (h : resTop U (s k) = g • resTop U (s i)) :
    Stacks.ProjectiveFromSections.ratio s i k
      = Stacks.ProjectiveFromSections.resO (le_of_eq hU) g := by
  subst hU
  have hid : Stacks.ProjectiveFromSections.resO
      (le_of_eq (rfl : Stacks.ProjectiveFromSections.nvCover s i
        = Stacks.ProjectiveFromSections.nvCover s i)) g = g := by
    simp [Stacks.ProjectiveFromSections.resO]
  rw [hid]
  exact (Stacks.ProjectiveFromSections.eq_div (s i) le_rfl h.symm).symm

/-- **The coordinate ratio of the chart, on the chart as a scheme.** The ratio identified by
`Stacks.ChartDegreeEqualisation.ratio_eq_of_resTop_eq`, read through the comparison
`Stacks.ProjectiveFromSections.chartRatio` applies, which is the spelling the pinning hypothesis
of `Stacks.AmpleImmersionReduction.ChartImmersion` is stated in. -/
theorem chartRatio_eq_of_resTop_eq {n : ℕ} (s : Fin (n + 1) → Γ(M, ⊤)) (i k : Fin (n + 1))
    {U : X.Opens} (hU : Stacks.ProjectiveFromSections.nvCover s i = U) (g : Γ(X, U))
    (h : resTop U (s k) = g • resTop U (s i)) :
    Stacks.ProjectiveFromSections.chartRatio s i k
      = (Stacks.ProjectiveFromSections.nvCover s i).topIso.inv
          (Stacks.ProjectiveFromSections.resO (le_of_eq hU) g) :=
  congrArg _ (ratio_eq_of_resTop_eq s i k hU g h)

end Ratios

section Assembly

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The equalised family.** Let `L` be ample, let `a : ι → powSections L d` be a finite family
of homogeneous elements of one positive degree whose charts `X_{a i}` cover `X`, and let
`g i : κ i → Γ(X, X_{a i})` be, on each chart, a finite family of functions. Then there is one
degree `N ≥ 1` and one family

`s : ι ⊕ (Σ i, κ i) → Γ(L ^⊗ N, ⊤)`

of global sections of that single power, generating every stalk, whose `inl i`-th chart is
`X_{a i}` and whose coordinate ratio out of that chart at the index `inr ⟨i, j⟩` is exactly
`g i j`.

This is what the degree equalisation is for: numerators and denominators landing in one degree is
precisely what lets them be collected into one family, and a single family of global sections of a
single `L ^⊗ N` is what defines a morphism to a *single* projective space over `S`
(`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks`), pinned on
each chart by these ratios.

The `inl` part is the covering family, whose charts are unchanged because the denominators are
positive powers; the `inr` part is the numerators. Generation is
`Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem` applied to the `inl` part
alone. -/
theorem exists_family_ratio_eq (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Finite ι] (a : ι → powSections L d)
    (hcov : ∀ x : X, ∃ i, x ∈ nvOpen L (a i))
    {κ : ι → Type*} [∀ i, Finite (κ i)] (g : ∀ i, κ i → Γ(X, nvOpen L (a i))) :
    ∃ (N : ℕ) (s : ι ⊕ (Σ i, κ i) → Γ(tensorPowModule X L (N : ℤ), ⊤))
      (hnv : ∀ i, Stacks.ProjectiveFromSections.nvCover s (Sum.inl i) = nvOpen L (a i)),
      1 ≤ N ∧ Stacks.ProjectiveFromSections.GeneratesStalks s ∧
        ∀ (i : ι) (j : κ i),
          Stacks.ProjectiveFromSections.ratio s (Sum.inl i) (Sum.inr (Sigma.mk i j))
            = Stacks.ProjectiveFromSections.resO (le_of_eq (hnv i)) (g i j) := by
  obtain ⟨N, σ, b, hN, hnvσ, hratio⟩ := exists_common_exponent_ratio_tensorPow L hL hd a g
  refine ⟨N, Sum.elim σ fun q => b q.1 q.2, hnvσ, hN, ?_, fun i j => ?_⟩
  · refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    obtain ⟨i, hi⟩ := hcov x
    refine ⟨Sum.inl i, ?_⟩
    exact (hnvσ i).ge hi
  · exact ratio_eq_of_resTop_eq _ (Sum.inl i) (Sum.inr (Sigma.mk i j)) (hnvσ i) (g i j)
      (hratio i j)

end Assembly

end Stacks.ChartDegreeEqualisation

end
