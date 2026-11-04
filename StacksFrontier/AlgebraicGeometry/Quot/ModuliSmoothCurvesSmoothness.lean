module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesH01Open
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ModuliSmoothCurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableGenusLociOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.UniversallyBijectiveGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOfGenus

/-!
# `𝓜` and `𝓜_g` are smooth over `Spec(ℤ)` (Stacks 0E84)

The morphisms `𝓜 → Spec(ℤ)` and `𝓜_g → Spec(ℤ)` are smooth.

Here `𝓜 = Curves^{smooth, h0}` is the moduli stack of smooth proper curves (Stacks 0E81, 0E82),
the open substack of `Curves` of families `f : X → S` smooth of relative dimension one with
`f_*𝒪_X = 𝒪_S` universally, and `𝓜_g ⊂ 𝓜` the open and closed substack of genus `g` (Stacks
0E83). Both are open substacks of `Curves^{lci+}`, which is smooth over `Spec(ℤ)` (Stacks 0DZX).

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_moduliSmoothCurves_and_moduliSmoothCurvesOfGenus`:
  `𝓜` and, for every `g`, `𝓜_g` are smooth over `Spec(ℤ)`.

## Implementation notes

The stack of curves is algebraic (Stacks 0D5A,
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`), so it has the small
model `AlgebraicGeometry.curvesAlgebraicStack`. The two open substacks are the open substacks of
that model cut out by their conditions (o) of Stacks 0E0E, and smoothness over `Spec(ℤ)` is
`AlgebraicGeometry.IsSmoothOverIntegers`.

`𝓜` is the property `AlgebraicGeometry.IsSmoothH0Family` of `AlgebraicGeometry.moduliSmoothCurves`
and `𝓜_g` is the property `AlgebraicGeometry.IsSmoothH0FamilyOfFibreGenus` of
`AlgebraicGeometry.moduliSmoothCurvesOfGenus`, the summands of the decomposition of Stacks 0E83
(`AlgebraicGeometry.moduliSmoothCurves_openClosedDecomposition`). Their conditions (o) are built
from the étale local scheme charts of families of curves (Stacks 0E6F,
`AlgebraicGeometry.C1590Private.hasEtaleLocalSchemeCharts`), from which come the openness of the
locus where `f_*𝒪_X = 𝒪_S` universally and of the genus loci. The limit preservation of `Curves`
(Stacks 0D55) enters through Stacks 0DZX. The genus `g` ranges over all natural numbers.

## References

* [Stacks Project, Tag 0E84](https://stacks.math.columbia.edu/tag/0E84)
* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The morphisms `𝓜 → Spec(ℤ)` and, for every `g`, `𝓜_g → Spec(ℤ)` are smooth. Here
`𝓜 = Curves^{smooth, h0}` and `𝓜_g` are the open substacks of the algebraic stack of curves (Stacks
0D5A) of the families smooth of relative dimension one with `f_*𝒪_X = 𝒪_S` universally, and of
those with moreover all fibres of genus `g`. Both are open substacks of `Curves^{lci+}`, which is
smooth over `Spec(ℤ)` (Stacks 0DZX). -/
@[stacks 0E84 "both morphisms 𝓜 → Spec(ℤ) and 𝓜_g → Spec(ℤ), for every g"]
theorem isSmoothOverIntegers_moduliSmoothCurves_and_moduliSmoothCurvesOfGenus :
    IsSmoothOverIntegers B hZ (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
        (C1590Private.isOpenCurvesLocus_isSmoothH0Family_of B hZ
          (C1590Private.isOpenCurvesLocus_hasUniversallyBijectiveGlobalFunctions_of
            (C1590Private.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
              (C1590Private.hasEtaleLocalSchemeCharts B hZ))
            (C1590Private.hasUniversallyBijectiveGlobalFunctions_of
              (C1590Private.hasEtaleLocalSchemeCharts B hZ)))) ∧
      ∀ g : ℕ, IsSmoothOverIntegers B hZ
        (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
        (IsOpenCurvesLocus.of_iff (Q := IsSmoothH0FamilyOfFibreGenus B hZ g)
          (C1590Private.isOpenCurvesLocus_isSmoothH0FamilyOfFibreGenus_of
            (C1590Private.isOpenCurvesLocus_hasUniversallyBijectiveGlobalFunctions_of
              (C1590Private.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
                (C1590Private.hasEtaleLocalSchemeCharts B hZ))
              (C1590Private.hasUniversallyBijectiveGlobalFunctions_of
                (C1590Private.hasEtaleLocalSchemeCharts B hZ)))
            (C1590Private.prestableGenusLociOpen_of (C1590Private.hasEtaleLocalSchemeCharts B hZ))
            g)
          fun _ => Iff.rfl) := by
  obtain ⟨hM, -⟩ := C1590Private.isSmoothOverIntegers_moduliSmoothCurves_of_isLimitPreserving
    B hZ (C1590Private.isAlgebraicStack_curvesFiberedCategory B hZ)
    (C1590Private.isLimitPreserving_curvesFiberedCategory B hZ) _
    (C1590Private.isOpenCurvesLocus_isSmoothH0FamilyOfFibreGenus_of
      (C1590Private.isOpenCurvesLocus_hasUniversallyBijectiveGlobalFunctions_of
        (C1590Private.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
          (C1590Private.hasEtaleLocalSchemeCharts B hZ))
        (C1590Private.hasUniversallyBijectiveGlobalFunctions_of
          (C1590Private.hasEtaleLocalSchemeCharts B hZ)))
      (C1590Private.prestableGenusLociOpen_of (C1590Private.hasEtaleLocalSchemeCharts B hZ)))
  exact ⟨hM, fun g => isSmoothOverIntegers_of_imp B hZ _ _ _ (fun _ hF => hF.1) hM⟩

end AlgebraicGeometry

end
