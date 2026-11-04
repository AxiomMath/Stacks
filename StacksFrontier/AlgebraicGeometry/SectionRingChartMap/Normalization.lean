module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Division

/-!
# The ratio of the denominator by itself

For `a` a homogeneous section of degree `d` of the tensor powers of `L`, `n ≥ 1` and an open
`V ≤ X_a`, `Stacks.SectionRingChartMap.numMap` divides a global section of `L ^⊗ (d n)` by `aⁿ`
over `V`. This file records the normalization of that division: the denominator divided by itself
is `1`.

## Main results

* `Stacks.SectionRingChartMap.numMap_self`: `aⁿ / aⁿ = 1`.
* `Stacks.SectionRingChartMap.numMap_eq_one_iff_resTop_eq`: a ratio is `1` exactly when the
  numerator restricts to the denominator.

## The exponent shift

The chart map at `a` is assembled by `Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree`
from a family of additive maps `e : ℕ → Γ_*(X, L) →+ Γ(X, V)` indexed by the exponent of the
denominator, including the exponent zero. The family is defined with the exponent shifted,
`e n x := (a · x) / a ^ (n + 1)`, whose denominator exponent is positive for every `n`; it is the
same function as `x / aⁿ`. Its unit law `e 0 1 = 1` is `Stacks.SectionRingChartMap.numMap_self`
at `n = 1`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec)
open Stacks.AmpleFiniteAvoidance (nvOpen)
open Stacks.TensorPowerTrivialize (resTop)

universe u

namespace Stacks.SectionRingChartMap

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  {d : ℕ} (a : powSections L d) {V : X.Opens}

/-- **The denominator divided by itself is `1`:** `aⁿ / aⁿ = 1` on `V`. -/
public theorem numMap_self (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) :
    numMap L a hV n hn (globalSection X _ (powSec L a n)) = 1 :=
  numMap_unique L a hV n hn _ 1
    (one_smul (Γ(X, V)) (resTop (natTensorPow L (d * n))
      (globalSection X _ (powSec L a n)) V)).symm

/-- A ratio is `1` exactly when the numerator restricts to the denominator. -/
public theorem numMap_eq_one_iff_resTop_eq (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n)
    (t : Γ(natTensorPow L (d * n), ⊤)) :
    numMap L a hV n hn t = 1 ↔
      resTop (natTensorPow L (d * n)) t V
        = resTop (natTensorPow L (d * n)) (globalSection X _ (powSec L a n)) V := by
  refine ⟨fun h ↦ ?_, fun h ↦ numMap_unique L a hV n hn t 1 (h.trans (one_smul _ _).symm)⟩
  rw [← numMap_smul_resTop L a hV n hn t, h, one_smul]

end Monoidal

end Stacks.SectionRingChartMap

end
