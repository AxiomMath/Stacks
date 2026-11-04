module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci

/-!
# Condition (o) for `f_*𝒪_X = 𝒪_S` universally

Stacks 0E6I produces the open substack `Curves^{h0,1}` of families of curves `f : X → S` with
`f_*𝒪_X = 𝒪_S` universally and all fibres of dimension `1`. This file proves condition (o) of
Stacks 0E0E for the property "`f_*𝒪_X = 𝒪_S` universally", given two hypotheses:

* `hopen`: the fibrewise condition `κ = H⁰(X_κ, 𝒪)` at the field-valued points of the base,
  `AlgebraicGeometry.CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres`, satisfies condition
  (o) (Stacks 0E0R at `i = 0`, for `𝓕 = 𝒪_X`);
* `hpush`: that fibrewise condition implies `f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B, part (a)).

## Main results

* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_hasUniversallyBijectiveGlobalFunctions_of`:
  condition (o) for `f_*𝒪_X = 𝒪_S` universally, from `hopen` and `hpush`.

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
  (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
    HasUniversallyBijectiveGlobalFunctions B hZ X)

include hopen hpush

/-- **Condition (o) for `f_*𝒪_X = 𝒪_S` universally.** Given `hopen` (the fibrewise condition
`κ = H⁰(X_κ, 𝒪)` satisfies condition (o)) and `hpush` (the fibrewise condition implies
`f_*𝒪_X = 𝒪_S` universally), the property `f_*𝒪_X = 𝒪_S` universally satisfies condition (o). -/
theorem isOpenCurvesLocus_hasUniversallyBijectiveGlobalFunctions_of :
    IsOpenCurvesLocus B hZ (HasUniversallyBijectiveGlobalFunctions B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := hopen G
  refine ⟨W, hW, fun F a => ⟨fun h => (hchar F a).1 ?_, fun h => hpush F ((hchar F a).2 h)⟩⟩
  exact
    CurveFamily.hasBijectiveGlobalFunctionsOnFieldFibres_of_hasUniversallyBijectiveGlobalFunctions
      h

end AlgebraicGeometry.C1590Private

end
