module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableGenusLociOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothOfLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOpen

/-!
# `𝓜̄` and `𝓜̄_g` are smooth over `Spec(ℤ)` (Stacks 0E79)

**Stacks 0E79.** The morphisms `𝓜̄ → Spec(ℤ)` and `𝓜̄_g → Spec(ℤ)` are smooth.

The source's proof: `𝓜̄` is an open substack of `Curves^{nodal}`, which is smooth over `Spec(ℤ)`
(Stacks 0E00). The same holds for each `𝓜̄_g`, an open substack of `𝓜̄`.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus`: the stable
  families all of whose fibres have genus `g` (the families of `𝓜̄_g`,
  `AlgebraicGeometry.moduliStableCurvesOfGenus`, Stacks 0E77) satisfy condition (o) of Stacks
  0E0E, so they cut out an open substack of `Curves`. Unregistered.
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus`: the same for
  the stable families with `R¹f_*𝒪_X` locally free of rank `g` (the openness part of Stacks
  0E78). Unregistered.
* `AlgebraicGeometry.isSmoothOverIntegers_moduliStableCurves_and_moduliStableCurvesOfGenus`:
  **Stacks 0E79**, for `𝓜̄` and for `𝓜̄_g`, every `g`.

## Implementation notes

The stack of curves is algebraic (Stacks 0D5A,
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`), so it has the small
model `AlgebraicGeometry.curvesAlgebraicStack`. `𝓜̄` and `𝓜̄_g` are the open substacks of that
model cut out by the stable families (Stacks 0E76,
`AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily`) and by the stable families
all of whose fibres have genus `g`. Smoothness over `Spec(ℤ)` is
`AlgebraicGeometry.IsSmoothOverIntegers`: smoothness of the inclusion followed by the structure
morphism of Stacks 050D, as for Stacks 0E72.

The openness of `𝓜̄_g` is that of `𝓜̄` together with the openness of the genus loci of prestable
families (`AlgebraicGeometry.C1590Private.prestableGenusLociOpen_of`). On stable families, all
fibres having genus `g` is the same as `R¹f_*𝒪_X` being locally free of rank `g`
(`CurveFamily.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre`), the form
`AlgebraicGeometry.IsStableCurveFamilyOfGenus` of part (1) of Stacks 0E78 in which
`AlgebraicGeometry.isSmoothOverIntegers_stableOfGenus` is stated. The local finite presentation of
`Curves → Spec(ℤ)` enters through the limit preservation of `Curves` (Stacks 0D55,
`AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory`).

## References

* [Stacks Project, Tag 0E79](https://stacks.math.columbia.edu/tag/0E79)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **`𝓜̄_g` is an open substack of `Curves`.** The stable families of curves all of whose fibres
have genus `g` satisfy condition (o) of Stacks 0E0E: the stable families do (Stacks 0E76), and
the genus loci of prestable families are open. Unregistered. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfFibreGenus B hZ g) :=
  (C1590Private.isOpenCurvesLocus_and_hasFibresOfGenus
      (C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) (fun _ h => h.1)
      (C1590Private.prestableGenusLociOpen_of (C1590Private.hasEtaleLocalSchemeCharts B hZ))
      g).of_iff fun _ => Iff.rfl

/-- The stable families of curves with `R¹f_*𝒪_X` locally free of rank `g` satisfy condition (o)
of Stacks 0E0E, being the families of `𝓜̄_g`. Unregistered. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  (isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus B hZ g).of_iff
    (isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus B hZ g)

@[deprecated (since := "2026-11-01")]
alias C1763Private.isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus :=
  isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus

@[deprecated (since := "2026-11-01")]
alias C1763Private.isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus :=
  isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus

@[deprecated (since := "2026-11-01")]
alias C1763Private.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus :=
  isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus

open C1590Private

/-- **Stacks 0E79.** The morphisms `𝓜̄ → Spec(ℤ)` and, for every `g`, `𝓜̄_g → Spec(ℤ)` are smooth.
Here `𝓜̄` is the open substack of the algebraic stack of curves (Stacks 0D5A) of the stable
families (Stacks 0E76), and `𝓜̄_g` is its open substack of the stable families of genus `g`. The
second conjunct states smoothness of `𝓜̄_g` in both forms of its families: stable with `R¹f_*𝒪_X`
locally free of rank `g` (part (1) of Stacks 0E78, `AlgebraicGeometry.IsStableCurveFamilyOfGenus`),
and stable with every fibre of genus `g` (Stacks 0E77,
`AlgebraicGeometry.IsStableCurveFamilyOfFibreGenus`); the two properties of families agree
(`AlgebraicGeometry.isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus`),
so they cut out the same open substack. Both `𝓜̄` and `𝓜̄_g` are open substacks of
`Curves^{nodal}`, which is smooth over `Spec(ℤ)` (Stacks 0E00).

The statement assumes nothing beyond the site `B` containing `Spec(ℤ)`; the algebraicity
of `Curves` (Stacks 0D5A), its limit preservation (Stacks 0D55) and the openness of `𝓜̄` and
`𝓜̄_g` are all proved. -/
@[stacks 0E79 "both morphisms: 𝓜̄ → Spec(ℤ) (first conjunct) and 𝓜̄_g → Spec(ℤ) for every g \
(second conjunct, for 𝓜̄_g cut out by R¹f_*𝒪_X locally free of rank g as in 0E78 (1), and by all \
fibres of genus g as in 0E77) are smooth"]
theorem isSmoothOverIntegers_moduliStableCurves_and_moduliStableCurvesOfGenus :
    IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
        (isOpenCurvesLocus_isStableCurveFamily B hZ) ∧
      ∀ g : ℕ,
        IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
            (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus B hZ g) ∧
          IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
            (isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus B hZ g) := by
  refine ⟨isSmoothOverIntegers_stable_of_isLimitPreserving B hZ
      (isAlgebraicStack_curvesFiberedCategory B hZ) (isLimitPreserving_curvesFiberedCategory B hZ)
      _, fun g => ?_⟩
  have hsm : IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
      (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus B hZ g) :=
    isSmoothOverIntegers_stableOfGenus_of_isLimitPreserving B hZ
      (isAlgebraicStack_curvesFiberedCategory B hZ) (isLimitPreserving_curvesFiberedCategory B hZ)
      g _
  exact ⟨hsm, isSmoothOverIntegers_of_imp B hZ (isAlgebraicStack_curvesFiberedCategory B hZ)
    (isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus B hZ g)
    (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus B hZ g)
    (fun X => (isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus B hZ g X).1) hsm⟩

end AlgebraicGeometry

end
