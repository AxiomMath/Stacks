module

public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Power
public import StacksFrontier.AlgebraicGeometry.SectionRingProjOverlap.Basic

/-!
# Dividing a section of `L ^⊗ (d n)` by the `n`-th power of a section of `L ^⊗ d`

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `a` a global section of `L ^⊗ d`, that is
a homogeneous element of degree `d` of the graded section ring
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag 01CV in the spelling
`Stacks.GradedSections.sectionRing`. Over an open `V` inside the nonvanishing open `X_a` the
power `aⁿ` generates `L ^⊗ (d n)` freely, so every section of `L ^⊗ (d n)` over `V` is a unique
function on `V` times `aⁿ|_V`. This file names that function.

The chart map of `Proj Γ_*(X, L)` at `a` is the ring homomorphism `Γ_*(X, L)₍a₎ → Γ(X, X_a)`
sending the fraction `t / aⁿ` to this ratio. The degree `d` is arbitrary, and the `n`-th map
divides by `aⁿ`, a section of `L ^⊗ (d * n)`.

## Main definitions

* `Stacks.SectionRingChartMap.divEquiv`: for `n ≥ 1`, multiplication by `aⁿ|_V` as a linear
  equivalence `Γ(X, V) ≃ₗ Γ(L ^⊗ (d n), V)`. Its inverse is the division.
* `Stacks.SectionRingChartMap.numMap`: **the ratio `t ↦ t/aⁿ`** as an additive map
  `Γ(X, L ^⊗ (d n)) →+ Γ(X, V)`, defined on global sections of the numerator's degree.

## Main results

* `Stacks.SectionRingChartMap.le_nvOpen_powSec`: one open `V ≤ X_a` lies inside the nonvanishing
  open of every positive power of `a` at once.
* `Stacks.SectionRingChartMap.numMap_smul_resTop`: **the defining identity**,
  `t|_V = (t/aⁿ) · aⁿ|_V`.
* `Stacks.SectionRingChartMap.numMap_unique`: the ratio is the *only* function with that property,
  so any identity of the shape `t|_V = f · aⁿ|_V` computes it.
* `Stacks.SectionRingChartMap.numMap_smul`: the ratio of a scalar multiple is the scalar multiple
  of the ratio.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec)
open Stacks.AmpleFiniteAvoidance (nvOpen)
open Stacks.TensorPowerTrivialize (resTop trivEquiv)

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

/-- **One open serves every positive power.** An open inside the nonvanishing open of `a` lies
inside the nonvanishing open of `aⁿ` for every `n ≥ 1`. -/
public theorem le_nvOpen_powSec (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) :
    V ≤ nvOpen L (powSec L a n) :=
  hV.trans_eq (Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L a n hn).symm

/-- **Multiplication by `aⁿ|_V`, as a linear equivalence.** For `n ≥ 1` and `V` inside `X_a` the
power `aⁿ` generates `L ^⊗ (d n)` over `V`, by the trivialization clause of Stacks Tag 01CY; this
is that trivialization with the generator named. -/
public noncomputable def divEquiv (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) :
    Γ(X, V) ≃ₗ[Γ(X, V)] Γ(natTensorPow L (d * n), V) :=
  trivEquiv (natTensorPow L (d * n)) (globalSection X _ (powSec L a n))
    (le_nvOpen_powSec L a hV n hn)

/-- Multiplication by `aⁿ|_V` is what `divEquiv` does. -/
public theorem divEquiv_apply (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) (f : Γ(X, V)) :
    divEquiv L a hV n hn f =
      f • resTop (natTensorPow L (d * n)) (globalSection X _ (powSec L a n)) V :=
  rfl

/-- **The ratio `t / aⁿ`**, as an additive map on the global sections of `L ^⊗ (d n)`: the unique
function on `V` whose product with `aⁿ|_V` is `t|_V`. -/
public noncomputable def numMap (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) :
    Γ(natTensorPow L (d * n), ⊤) →+ Γ(X, V) where
  toFun t := (divEquiv L a hV n hn).symm (resTop (natTensorPow L (d * n)) t V)
  map_zero' := by
    change (divEquiv L a hV n hn).symm (resTop (natTensorPow L (d * n)) 0 V) = 0
    rw [show resTop (natTensorPow L (d * n)) 0 V = 0 from map_zero _, map_zero]
  map_add' t t' := by
    change (divEquiv L a hV n hn).symm (resTop (natTensorPow L (d * n)) (t + t') V) = _
    rw [show resTop (natTensorPow L (d * n)) (t + t') V
          = resTop (natTensorPow L (d * n)) t V + resTop (natTensorPow L (d * n)) t' V from
        map_add _ t t', map_add]

/-- **The defining identity of the ratio:** `t|_V = (t/aⁿ) · aⁿ|_V`. -/
public theorem numMap_smul_resTop (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n)
    (t : Γ(natTensorPow L (d * n), ⊤)) :
    numMap L a hV n hn t •
        resTop (natTensorPow L (d * n)) (globalSection X _ (powSec L a n)) V =
      resTop (natTensorPow L (d * n)) t V :=
  (divEquiv L a hV n hn).apply_symm_apply (resTop (natTensorPow L (d * n)) t V)

/-- **The ratio is the unique function with the defining property:** if `t|_V = f · aⁿ|_V`, then
`t / aⁿ = f`. -/
public theorem numMap_unique (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n)
    (t : Γ(natTensorPow L (d * n), ⊤)) (f : Γ(X, V))
    (hf : resTop (natTensorPow L (d * n)) t V
      = f • resTop (natTensorPow L (d * n)) (globalSection X _ (powSec L a n)) V) :
    numMap L a hV n hn t = f :=
  (divEquiv L a hV n hn).injective
    ((numMap_smul_resTop L a hV n hn t).trans hf)

/-- The ratio of a scalar multiple is the scalar multiple of the ratio, for a scalar that is the
restriction of a function on `V`. -/
public theorem numMap_smul (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n)
    (t : Γ(natTensorPow L (d * n), ⊤)) (f : Γ(X, V)) (t' : Γ(natTensorPow L (d * n), ⊤))
    (ht : resTop (natTensorPow L (d * n)) t' V = f • resTop (natTensorPow L (d * n)) t V) :
    numMap L a hV n hn t' = f * numMap L a hV n hn t :=
  numMap_unique L a hV n hn t' _
    (ht.trans ((congrArg (f • ·) (numMap_smul_resTop L a hV n hn t).symm).trans
      (smul_smul f (numMap L a hV n hn t) _)))

end Monoidal

end Stacks.SectionRingChartMap

end
