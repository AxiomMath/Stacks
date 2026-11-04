module

public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Localization
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Locality

/-!
# The chart comparison for `Proj` of a graded ring with a cover in one positive degree

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a graded ring and let `d > 0` be a degree such that the standard
opens of the homogeneous elements of degree `d` cover `Proj 𝒮`. This file redoes, at degree `d`,
the two steps of the chart comparison of Stacks Tag 0801 that
`StacksFrontier/AlgebraicGeometry/ProjChartKernel/Localization.lean` and
`StacksFrontier/AlgebraicGeometry/ProjSaturation/IdealOfClosedSubscheme.lean` prove at degree one:

* the **localization step** — a kernel membership on one chart `D₊(f)` gives, after multiplying
  the numerator by a power of `f`, a kernel membership on any other degree-`d` chart `D₊(h)`;
* the **chartwise criterion** — a homogeneous element of a degree that is a multiple of `d` lies
  in the Tag 0BXK ideal of equations as soon as its chart function lies in the kernel on every
  chart of a degree-`d` cover.

## Why degree `d` and not degree one

Stacks Tag 0801 assumes nothing about generation in degree one; its proof takes
`f_0, …, f_n ∈ A_+` of arbitrary positive degrees and passes to `d = lcm (deg f_i)`, "so that
each `𝒪_X(nd)` is invertible". The degree-one statements in this repository are the special case
`d = 1`, and the only place degree one is really used is the invertibility of the twists: a
graded ring generated in degree one has **every** `𝒪(n)` invertible, whereas in general only the
multiples of `d` are. That is exactly the shape of
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top`,
which concludes the invertibility of `𝒪(d · n)` from `Stacks.AlgebraicGeometry.ProjShared`
`.ratioLocus 𝒮 d = ⊤`, and a degree-`d` cover puts the ratio locus at `⊤` by
`Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_ratioLocus`. Everything else in the two files
being generalized is already stated at an arbitrary degree `d`:
`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction_eq_of_cross`, `chartFraction_mul`,
`chartFraction_restrict`, `zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq`,
`chartFraction_mem_ker_app_of_mem_idealOfClosedSubscheme`, and Mathlib's
`HomogeneousLocalization.Away.isLocalization_mul`, whose only hypothesis on the degree is that it
be nonzero.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction_pow'`: a power of a chart function is
  the chart function of the power, with the numerator of an arbitrary index rather than of index
  one.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.ratioLocus_eq_top_of_iSup_basicOpen_degree`: a cover
  by standard opens of degree-`d` elements puts Tag 01MU's locus `W_d` at `⊤`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf_smul`:
  hence `𝒪(m · d)` is invertible, in the class `AlgebraicGeometry.zeroScheme` consumes.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_chartFraction_mem_ker_uniform`: **the
  localization step at degree `d`.**
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker_uniform`: **the chartwise
  criterion at degree `d`**, with no hypothesis of generation in degree one.

## Implementation notes

The localization element of `HomogeneousLocalization.Away.isLocalization_mul hh hf` is
`h`-fraction `f ^ d / h ^ d`, of index `d` rather than of index `1` as in the degree-one case,
which is why `chartFraction_pow'` is needed: the `k`-th power of a chart function of index `d` is
the chart function of index `k * d`.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (isInvertible_twistingSheaf_of_ratioLocus_eq_top)

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable {f h : S} {d : ℕ}

/-! ### Powers of a chart function of arbitrary index -/

/-- **The `k`-th power of a chart function is the chart function of the `k`-th power.** This is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction_pow` with the index of the numerator
allowed to be an arbitrary `a` rather than `1`. -/
alias chartFraction_pow' := chartFraction_pow

/-! ### Invertibility of the twists in the multiples of `d` -/

/-- **A cover by standard opens of degree-`d` elements puts Tag 01MU's locus `W_d` at `⊤`.** -/
theorem ratioLocus_eq_top_of_iSup_basicOpen_degree {ι : Type*} (g : ι → S)
    (hg : ∀ j, g j ∈ 𝒮 d) (hcov : ⨆ j, Proj.basicOpen 𝒮 (g j) = ⊤) :
    Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒮 d = ⊤ :=
  top_le_iff.mp <| hcov.ge.trans <| iSup_le fun j =>
    Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_ratioLocus 𝒮 dvd_rfl (hg j)

/-- **The twists in the multiples of `d` are invertible**, in the class
`AlgebraicGeometry.zeroScheme` consumes. This is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top`
with the degree written as a natural-number multiple `m • d`, which is the indexing the chart
functions use. -/
theorem algebraicGeometry_isInvertible_twistingSheaf_smul
    (hd : Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒮 d = ⊤) (m : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (Proj 𝒮).sheaf.obj
      (Proj 𝒮).ringCatSheaf.property (twistingSheaf 𝒮 ((m • d : ℕ) : ℤ)) := by
  have hc : ((d : ℤ) * (m : ℤ)) = ((m • d : ℕ) : ℤ) := by
    push_cast [smul_eq_mul]
    ring
  have hinv := isInvertible_twistingSheaf_of_ratioLocus_eq_top 𝒮 hd (m : ℤ)
  rwa [hc] at hinv

/-! ### The localization step at degree `d` -/

/-- **The localization step, at a uniform positive degree `d`.** If the chart function
`b / f ^ n` of a homogeneous element lies in the kernel of `i` over `D₊(f)`, then for every other
degree-`d` element `h` there is an exponent `N` such that the chart function
`f ^ N b / h ^ (N + n)` lies in the kernel of `i` over `D₊(h)`.

This is `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_chartFraction_mem_ker` with
`d = 1` relaxed to an arbitrary positive `d`. The argument is unchanged: over `D₊(h f)` the two
fractions differ by a unit, the kernel over `D₊(h f)` is generated by the kernel over `D₊(h)`
(`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`), and `Away 𝒮 (h f)` is the localization of
`Away 𝒮 h` at `f ^ d / h ^ d` (`HomogeneousLocalization.Away.isLocalization_mul`, whose degree
hypothesis is only `d ≠ 0`), so some power of that element carries the class back. -/
alias exists_pow_mul_chartFraction_mem_ker_uniform := exists_pow_mul_chartFraction_mem_ker

/-! ### The chartwise criterion at degree `d` -/

/-- **Membership in `I(Z)` is checked chart by chart on a cover by degree-`d` standard opens.**
If the chart function of a homogeneous element `z` of degree `m · d` lies in
`Ker(i.app D₊(fam j))` for every member of a family of degree-`d` elements whose standard opens
cover `Proj 𝒮`, then `z` lies in the ideal of `Z`.

This is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_idealOfClosedSubscheme_of_forall_chartFraction_`
`mem_ker` with the hypothesis of generation in degree one deleted: the invertibility of the
twist it spends that hypothesis on is needed only in the degree `m · d` of the element at hand,
and a degree-`d` cover supplies exactly the twists in the multiples of `d`. -/
theorem mem_idealOfClosedSubscheme_of_forall_chartFraction_mem_ker_uniform (hd : 0 < d)
    {ι : Type*} (fam : ι → S) (hfam : ∀ j, fam j ∈ 𝒮 d)
    (hcov : ⨆ j, Proj.basicOpen 𝒮 (fam j) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] {m : ℕ} (z : 𝒮 (m • d))
    (hz : ∀ (j : ι) (c : 𝒮 (m • d)), (c : S) = (z : S) →
      chartFraction 𝒮 (hfam j) m c ∈ RingHom.ker (i.app (Proj.basicOpen 𝒮 (fam j))).hom) :
    (z : S) ∈ idealOfClosedSubscheme 𝒮 i := by
  have inst := algebraicGeometry_isInvertible_twistingSheaf_smul 𝒮
    (ratioLocus_eq_top_of_iSup_basicOpen_degree 𝒮 fam hfam hcov) m
  refine mem_idealOfClosedSubscheme 𝒮 i (m • d) z ?_
  rw [pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker]
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun j => ⟨Proj.basicOpen 𝒮 (fam j),
      Proj.isAffineOpen_basicOpen 𝒮 (fam j) (hfam j) hd⟩) hcov ?_
  intro j
  rw [Scheme.Hom.ker_apply]
  exact le_of_eq_of_le
    (zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq 𝒮 (hfam j) hd m rfl z z.2)
    ((Ideal.span_singleton_le_iff_mem _).mpr (hz j ⟨(z : S), z.2⟩ rfl))

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
