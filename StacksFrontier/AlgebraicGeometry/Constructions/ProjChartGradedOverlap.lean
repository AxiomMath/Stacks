module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClauseTwo

/-!
# Two charts of `θ` agree on their overlap

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. For `f ∈ 𝒜 d` homogeneous,
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection` is the chart-level comparison

  `θ_f : (A_f)_n ⟶ Γ(L ^⊗ n, V)`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`,

of [Stacks, Tag 01NK], defined over every open `V` on which `ψ(f)` does not vanish.

This file proves that **two such comparisons agree on the overlap of their charts**: if `f ∈ 𝒜 d`
and `g ∈ 𝒜 d'` and `V ≤ T_{ψ(f)} ⊓ T_{ψ(g)}`, then `θ_f` and `θ_g` take the same value over `V`
on two fractions that become equal in `A_{f g}`.

Together with `Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.map_chartSection`, which says
each `θ_f` commutes with restriction to a smaller open of its chart, this is the compatibility
across the cover `U(ψ) = ⋃_f T_{ψ(f)}` of [Stacks, Tag 01NK]: the per-chart values of the
degree-`n` part depend only on the fraction and not on which chart it is read on.

Written on representatives `x / f ^ j` and `x' / g ^ k`, equality of the two fractions in
`A_{f g}` is

  `(f g) ^ c · (x g ^ k) = (f g) ^ c · (x' f ^ j)`   for some `c : ℕ`,

and the case `c = 0` is the cross-multiplication `x g ^ k = x' f ^ j`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedOverlap.chartSectionOf_mul_left`: **the
  common-denominator form of a chart value**: for `u` homogeneous of degree `m` not vanishing on
  `V`, the quotient `ψ(u x) / ψ(u f ^ j)` is `θ_f(x / f ^ j)`.
* `Stacks.AlgebraicGeometry.ProjChartGradedOverlap.chartSectionOf_eq_of_cross`: **`θ_f` and `θ_g`
  agree on cross-multiplying representatives**: if `x g ^ k = x' f ^ j` then
  `ψ(x) / ψ(f ^ j) = ψ(x') / ψ(g ^ k)` over `V`.
* `Stacks.AlgebraicGeometry.ProjChartGradedOverlap.chartSectionOf_eq_of_cross_mul_pow`: the same
  under the hypothesis with a factor `(f g) ^ c`, which is equality of the two fractions in
  `A_{f g}`.
* `Stacks.AlgebraicGeometry.ProjChartGradedOverlap.chartSection_eq_of_mk_eq_away`: **the agreement
  of the two comparisons on the overlap**, stated on elements of `(A_f)_n` and `(A_g)_n` with the
  hypothesis read as an equality in the localization of `A` at `f g`.

## Implementation notes

The unit axiom `ψ(1) = 1` is not used;
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections` does not require it.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (chartSection chartSectionOf chartSection_mk
  chartSectionOf_mul_pow divTop_congr_sections divTop_toFun_congr)
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (powCongr_app_toFun)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections nonvanishingOpen_mulSections)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (mem_graded_of_eq)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.GradedSections (powCongr)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (divTop divTop_mulSections_cancel)
open Stacks.TensorPowers (natTensorPow)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedOverlap

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-! ### A chart value read over a larger denominator -/

section Common

variable {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- **Multiplying numerator and denominator of a chart value by a nonvanishing `ψ(u)` does not
change it**: for `u` homogeneous of degree `m` whose value does not vanish on `V`, the quotient
`ψ(u x) / ψ(u f ^ j)` over `V` is `θ_f(x / f ^ j)`. -/
theorem chartSectionOf_mul_left (n j : ℕ) {m : ℕ} {u : A} (hu : u ∈ 𝒜 m)
    (hVu : V ≤ nonvanishingOpen T (natTensorPow L m) (ψ.toFun m ⟨u, hu⟩))
    {x : A} (hx : x ∈ 𝒜 (j * d + n))
    (hprod : u * f ^ j ∈ 𝒜 (m + j * d)) (hux : u * x ∈ 𝒜 (m + j * d + n))
    (hmid : V ≤ nonvanishingOpen T (natTensorPow L (m + j * d))
      (ψ.toFun (m + j * d) ⟨u * f ^ j, hprod⟩)) :
    divTop L (ψ.toFun (m + j * d) ⟨u * f ^ j, hprod⟩) hmid n
        (ψ.toFun (m + j * d + n) ⟨u * x, hux⟩)
      = chartSectionOf ψ hf hV n j hx := by
  have hfj : f ^ j ∈ 𝒜 (j * d) := HomogeneousRatios.pow_mem hf j
  have hnum : u * x ∈ 𝒜 (m + (j * d + n)) := SetLike.mul_mem_graded hu hx
  have hmul : V ≤ nonvanishingOpen T (natTensorPow L (m + j * d))
      (mulSections L (ψ.toFun m ⟨u, hu⟩) (ψ.toFun (j * d) ⟨f ^ j, hfj⟩)) :=
    (le_inf hVu (ψ.le_nonvanishingOpen_pow hf hV j)).trans_eq
      (nonvanishingOpen_mulSections L _ _).symm
  have hnumeq : (powCongr L (Nat.add_assoc m (j * d) n).symm).app ⊤
      (mulSections L (ψ.toFun m ⟨u, hu⟩) (ψ.toFun (j * d + n) ⟨x, hx⟩))
      = ψ.toFun (m + j * d + n) ⟨u * x, hux⟩ := by
    rw [← ψ.map_mul m (j * d + n) ⟨u, hu⟩ ⟨x, hx⟩ ⟨u * x, hnum⟩ rfl]
    exact powCongr_app_toFun 𝒜 ψ (Nat.add_assoc m (j * d) n).symm (u * x) hnum hux
  rw [divTop_congr_sections
      (ψ.map_mul m (j * d) ⟨u, hu⟩ ⟨f ^ j, hfj⟩ ⟨u * f ^ j, hprod⟩ rfl)
      hnumeq.symm hmid hmul,
    divTop_mulSections_cancel]
  · rfl
  · exact hVu

end Common

/-! ### The two comparisons agree on the overlap -/

section Overlap

variable {d d' : ℕ} {f g : A} {V : T.Opens} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d')
  (hVf : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
  (hVg : V ≤ nonvanishingOpen T (natTensorPow L d') (ψ.toFun d' ⟨g, hg⟩))

/-- A product of a degree-`p` element and a degree-`q + n` element has degree `p + q + n`. -/
private theorem mul_mem_graded_add_assoc {p q n : ℕ} {a x : A} (ha : a ∈ 𝒜 p)
    (hx : x ∈ 𝒜 (q + n)) : a * x ∈ 𝒜 (p + q + n) :=
  mem_graded_of_eq 𝒜 (Nat.add_assoc p q n).symm (SetLike.mul_mem_graded ha hx)

/-- **`θ_f` and `θ_g` agree on two cross-multiplying representatives.** If `x` is homogeneous of
degree `j d + n`, `x'` of degree `k d' + n` and `x g ^ k = x' f ^ j`, then the quotients
`ψ(x) / ψ(f ^ j)` and `ψ(x') / ψ(g ^ k)` are the same section of `L ^⊗ n` over an open where
neither `ψ(f)` nor `ψ(g)` vanishes. -/
theorem chartSectionOf_eq_of_cross (n j k : ℕ) {x x' : A}
    (hx : x ∈ 𝒜 (j * d + n)) (hx' : x' ∈ 𝒜 (k * d' + n))
    (hcross : x * g ^ k = x' * f ^ j) :
    chartSectionOf ψ hf hVf n j hx = chartSectionOf ψ hg hVg n k hx' := by
  have hfj : f ^ j ∈ 𝒜 (j * d) := HomogeneousRatios.pow_mem hf j
  have hgk : g ^ k ∈ 𝒜 (k * d') := HomogeneousRatios.pow_mem hg k
  have hVfj := ψ.le_nonvanishingOpen_pow hf hVf j
  have hVgk := ψ.le_nonvanishingOpen_pow hg hVg k
  have hp1 : g ^ k * f ^ j ∈ 𝒜 (k * d' + j * d) := SetLike.mul_mem_graded hgk hfj
  have hp2 : f ^ j * g ^ k ∈ 𝒜 (j * d + k * d') := SetLike.mul_mem_graded hfj hgk
  have hn1 : g ^ k * x ∈ 𝒜 (k * d' + j * d + n) := mul_mem_graded_add_assoc hgk hx
  have hn2 : f ^ j * x' ∈ 𝒜 (j * d + k * d' + n) := mul_mem_graded_add_assoc hfj hx'
  have hmid1 : V ≤ nonvanishingOpen T (natTensorPow L (k * d' + j * d))
      (ψ.toFun (k * d' + j * d) ⟨g ^ k * f ^ j, hp1⟩) :=
    ψ.le_nonvanishingOpen_mul hgk hfj hp1 hVgk hVfj
  have hmid2 : V ≤ nonvanishingOpen T (natTensorPow L (j * d + k * d'))
      (ψ.toFun (j * d + k * d') ⟨f ^ j * g ^ k, hp2⟩) :=
    ψ.le_nonvanishingOpen_mul hfj hgk hp2 hVfj hVgk
  rw [← chartSectionOf_mul_left ψ hf hVf n j hgk hVgk hx hp1 hn1 hmid1,
    ← chartSectionOf_mul_left ψ hg hVg n k hfj hVfj hx' hp2 hn2 hmid2]
  exact divTop_toFun_congr ψ hp1 hp2 n hn1 hn2 hmid1 hmid2 (Nat.add_comm _ _)
    (mul_comm _ _) (by rw [mul_comm (g ^ k) x, hcross, mul_comm])

/-- **The same agreement under the hypothesis with a factor `(f g) ^ c`.** This is equality of the
two fractions `x / f ^ j` and `x' / g ^ k` in the localization of `A` at `f g`, written out: the
cross-multiplication of `chartSectionOf_eq_of_cross` is the case `c = 0`. -/
theorem chartSectionOf_eq_of_cross_mul_pow (n j k c : ℕ) {x x' : A}
    (hx : x ∈ 𝒜 (j * d + n)) (hx' : x' ∈ 𝒜 (k * d' + n))
    (hcross : f ^ c * g ^ c * (x * g ^ k) = f ^ c * g ^ c * (x' * f ^ j)) :
    chartSectionOf ψ hf hVf n j hx = chartSectionOf ψ hg hVg n k hx' := by
  have hX : f ^ c * x ∈ 𝒜 ((c + j) * d + n) :=
    mem_graded_of_eq 𝒜 (by ring) (mul_mem_graded_add_assoc (HomogeneousRatios.pow_mem hf c) hx)
  have hX' : g ^ c * x' ∈ 𝒜 ((c + k) * d' + n) :=
    mem_graded_of_eq 𝒜 (by ring) (mul_mem_graded_add_assoc (HomogeneousRatios.pow_mem hg c) hx')
  rw [← chartSectionOf_mul_pow ψ hf hVf n j c hx hX,
    ← chartSectionOf_mul_pow ψ hg hVg n k c hx' hX']
  refine chartSectionOf_eq_of_cross ψ hf hg hVf hVg n (c + j) (c + k) hX hX' ?_
  calc f ^ c * x * g ^ (c + k) = f ^ c * g ^ c * (x * g ^ k) := by ring
    _ = f ^ c * g ^ c * (x' * f ^ j) := hcross
    _ = g ^ c * x' * f ^ (c + j) := by ring

/-- **The chart-level comparisons of two homogeneous elements agree on the overlap of their
charts.** For `y` in the degree-`n` part of `A_f` and `z` in the degree-`n` part of `A_g` whose
representatives `x / f ^ j` and `x' / g ^ k` become equal in the localization of `A` at `f g`, the
sections `θ_f(y)` and `θ_g(z)` of `L ^⊗ n` over `V ≤ T_{ψ(f)} ⊓ T_{ψ(g)}` coincide. -/
theorem chartSection_eq_of_mk_eq_away (n j k : ℕ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (z : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) g (n : ℤ))
    {x x' : A} (hx : x ∈ 𝒜 (j * d + n)) (hx' : x' ∈ 𝒜 (k * d' + n))
    (hy : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f))
    (hz : (z : LocalizedModule.Away g A)
      = LocalizedModule.mk x' (⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g))
    (hmk : LocalizedModule.mk (M := A) (x * g ^ k) (1 : Submonoid.powers (f * g))
      = LocalizedModule.mk (x' * f ^ j) (1 : Submonoid.powers (f * g))) :
    chartSection ψ hf hVf n y = chartSection ψ hg hVg n z := by
  obtain ⟨⟨_, c, rfl⟩, hu⟩ := LocalizedModule.mk_eq.1 hmk
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul] at hu
  rw [chartSection_mk ψ hf hVf n y j x hx hy, chartSection_mk ψ hg hVg n z k x' hx' hz]
  exact chartSectionOf_eq_of_cross_mul_pow ψ hf hg hVf hVg n j k c hx hx' (by rwa [← mul_pow])

end Overlap

end Stacks.AlgebraicGeometry.ProjChartGradedOverlap

end
