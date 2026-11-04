module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# `X_a` and `D₊(a)`: the overlap calculus of the charts of `X ⟶ Proj Γ_*(X, L)`

Let `X` be a scheme and `L` an invertible `𝒪_X`-module, and let
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` be the graded section ring of Stacks Tag 01CV in the
spelling `Stacks.GradedSections.sectionRing`, whose degree-`n` piece is
`Stacks.GradedSections.powSections L n` and whose internal grading is
`Stacks.AmpleFiniteAvoidance.grading`. A homogeneous element of degree `d` is
`DirectSum.of (powSections L) d a`, and it has two opens attached to it:

* `Stacks.AmpleFiniteAvoidance.nvOpen L a`, the nonvanishing open `X_a ⊆ X`;
* `AlgebraicGeometry.Proj.basicOpen (grading L) (DirectSum.of _ d a)`, the chart
  `D₊(a) ⊆ Proj Γ_*(X, L)`.

Clause (1) of Stacks Tag 01PZ is the identity `f ⁻¹ᵁ D₊(a) = X_a` for the canonical morphism
`f : X ⟶ Proj Γ_*(X, L)`. This file shows that the two sides have the same multiplicative
calculus, so that the identity, once checked on a family of homogeneous elements, holds on the
multiplicative set they generate.

## Main results

* `Stacks.SectionRingProjOverlap.of_pow_eq_of_powSec`: the `k`-th power of `DirectSum.of _ d a`
  in `Γ_*(X, L)` is `DirectSum.of _ (d * k) (powSec L a k)`.
  `Stacks.SectionRingProjOverlap.apply_of_pow` is the same read as the homogeneous component.
* `Stacks.SectionRingProjOverlap.projBasicOpen_of_mul` and `projBasicOpen_of_powSec`:
  `D₊(ab) = D₊(a) ⊓ D₊(b)` and `D₊(a^k) = D₊(a)` for `k ≥ 1`, for homogeneous elements of
  `Γ_*(X, L)`.
* `Stacks.SectionRingProjOverlap.preimage_projBasicOpen_eq_nvOpen_mul` and
  `preimage_projBasicOpen_eq_nvOpen_powSec`: if a morphism `g : X ⟶ Proj Γ_*(X, L)` satisfies
  `g ⁻¹ᵁ D₊(a) = X_a` and `g ⁻¹ᵁ D₊(b) = X_b`, it satisfies it at `ab`, and at every positive
  power of `a`.
* `Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le`: `X_{a^k} = X_a` for `k ≥ 1`, as an
  equality of opens.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)

## What is not done

The morphism `f : X ⟶ Proj Γ_*(X, L)` is not constructed here, so clause (1) of Stacks Tag 01PZ is
not proved; what is proved is that the identity it asserts propagates along the multiplication of
the section ring. Nothing is said about degree zero: `D₊(1) = ⊤` is Mathlib's
`Proj.basicOpen_one`, and the matching `X_1 = X` is not proved here.

No `@[stacks]` attribute is attached. These are overlap identities used for Tags 01PZ and 01Q1,
not the statement of either.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Ample Stacks.GradedSections Stacks.AmpleFiniteAvoidance
open Stacks.SectionExtension (powSec powSec_zero powSec_succ nvLocus_powSec_of_one_le)

universe u

namespace Stacks.SectionRingProjOverlap

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

/-! ### The power of a homogeneous element, computed in the section ring -/

/-- **The `k`-th power of a homogeneous element of `Γ_*(X, L)`.** The ring power of
`DirectSum.of _ d a` is the `DirectSum.of` of `Stacks.SectionExtension.powSec`, in degree
`d * k`. -/
theorem of_pow_eq_of_powSec {d : ℕ} (a : powSections L d) (k : ℕ) :
    DirectSum.of (powSections L) d a ^ k
      = DirectSum.of (powSections L) (d * k) (powSec L a k) := by
  induction k with
  | zero =>
      rw [pow_zero, powSec_zero]
      exact (DirectSum.of_zero_one (powSections L)).symm
  | succ k ih =>
      have hmul : DirectSum.of (powSections L) (d * k) (powSec L a k) *
            DirectSum.of (powSections L) d a
          = DirectSum.of (powSections L) (d * k + d) (mul (powSec L a k) a) :=
        DirectSum.of_mul_of (powSec L a k) a
      rw [pow_succ, ih, hmul, powSec_succ]
      rfl

/-- `of_pow_eq_of_powSec` read on the homogeneous component: the degree-`d * k` coordinate of the
`k`-th power of `DirectSum.of _ d a` is the `k`-th power of `a`. -/
theorem apply_of_pow {d : ℕ} (a : powSections L d) (k : ℕ) :
    (DirectSum.of (powSections L) d a ^ k) (d * k) = powSec L a k := by
  rw [of_pow_eq_of_powSec, DirectSum.of_eq_same]

variable [IsInvertibleModule X L]

/-! ### The `X_a` side, in the bundled shape -/

/-- **`X_{a^k} = X_a` for `k ≥ 1`, as an equality of opens.** -/
theorem nvOpen_powSec_of_one_le {d : ℕ} (a : powSections L d) (k : ℕ) (hk : 1 ≤ k) :
    nvOpen L (powSec L a k) = nvOpen L a :=
  Opens.ext (nvLocus_powSec_of_one_le L a k hk)

/-- **`X_a` for the ring power of a homogeneous element.** The nonvanishing locus of the
degree-`d * k` component of `α ^ k`, for `α = DirectSum.of _ d a` and `k ≥ 1`, is `X_a`. -/
theorem nvLocus_apply_of_pow {d : ℕ} (a : powSections L d) (k : ℕ) (hk : 1 ≤ k) :
    nvLocus L ((DirectSum.of (powSections L) d a ^ k) (d * k)) = nvLocus L a := by
  rw [apply_of_pow]
  exact nvLocus_powSec_of_one_le L a k hk

/-! ### The `D₊` side, in the section ring's vocabulary -/

/-- **`D₊(ab) = D₊(a) ⊓ D₊(b)`** for two homogeneous elements of `Γ_*(X, L)`: the analogue of
`Stacks.AmpleFiniteAvoidance.nvLocus_mul` on the `Proj` side. -/
theorem projBasicOpen_of_mul {d e : ℕ} (a : powSections L d) (b : powSections L e) :
    Proj.basicOpen (grading L) (DirectSum.of (powSections L) (d + e) (mul a b))
      = Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)
        ⊓ Proj.basicOpen (grading L) (DirectSum.of (powSections L) e b) := by
  have hmul : DirectSum.of (powSections L) (d + e) (mul a b)
      = DirectSum.of (powSections L) d a * DirectSum.of (powSections L) e b :=
    (DirectSum.of_mul_of a b).symm
  rw [hmul, Proj.basicOpen_mul]

/-- **`D₊(a^k) = D₊(a)` for `k ≥ 1`** for a homogeneous element of `Γ_*(X, L)`: the analogue of
`Stacks.SectionExtension.nvLocus_powSec_of_one_le` on the `Proj` side. -/
theorem projBasicOpen_of_powSec {d : ℕ} (a : powSections L d) (k : ℕ) (hk : 1 ≤ k) :
    Proj.basicOpen (grading L) (DirectSum.of (powSections L) (d * k) (powSec L a k))
      = Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) := by
  rw [← of_pow_eq_of_powSec, Proj.basicOpen_pow (grading L) _ k hk]

/-! ### The clause-(1) identity of Stacks Tag 01PZ propagates -/

/-- **`f ⁻¹ᵁ D₊(a) = X_a` passes to products.** If a morphism to `Proj Γ_*(X, L)` pulls the chart
of `a` back to `X_a` and the chart of `b` back to `X_b`, it pulls the chart of `ab` back to
`X_{ab}`. -/
theorem preimage_projBasicOpen_eq_nvOpen_mul {g : X ⟶ Proj (grading L)} {d e : ℕ}
    (a : powSections L d) (b : powSections L e)
    (ha : g ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) = nvOpen L a)
    (hb : g ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) e b) = nvOpen L b) :
    g ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) (d + e) (mul a b))
      = nvOpen L (mul a b) := by
  rw [projBasicOpen_of_mul, Scheme.Hom.preimage_inf, ha, hb]
  exact (Opens.ext (nvLocus_mul L a b)).symm

/-- **`f ⁻¹ᵁ D₊(a) = X_a` passes to positive powers:** the identity at `a` gives the identity at
`a ^ k` for `k ≥ 1`. -/
theorem preimage_projBasicOpen_eq_nvOpen_powSec {g : X ⟶ Proj (grading L)} {d : ℕ}
    (a : powSections L d) (k : ℕ) (hk : 1 ≤ k)
    (ha : g ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) = nvOpen L a) :
    g ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) (d * k) (powSec L a k))
      = nvOpen L (powSec L a k) := by
  rw [projBasicOpen_of_powSec L a k hk, ha, nvOpen_powSec_of_one_le L a k hk]

end Stacks.SectionRingProjOverlap

end
