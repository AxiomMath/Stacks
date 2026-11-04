module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SplitChart
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SplittingCover
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections

/-!
# The linear form cutting out the chart of a projective bundle over an affine open

`Stacks.ProjectiveBundleConormal.splitChartMap` identifies the affine bundle on `ker p` with the
standard open `D₊(ι s)` of `Proj(Sym_A M)`, for a linear form `p : M →ₗ[A] A` and an element
`s : M` with `p s = 1`. This file constructs such data for `A = Γ(X, U)` and `M = Γ(ℰ, U)`, where
`U` is an affine open on which the invertible quotient `q : ℰ ⟶ 𝓛` splits:

* `p` is `q` on sections over `U`, read in a frame `e : Γ(𝓛, U) ≃ₗ Γ(X, U)`, and
* `s` is a section of `ℰ` with `e (q s) = 1`.

The kernel of `p` is then identified with the sections over `U` of the kernel of `q`.

## Main definitions

* `Stacks.ProjectiveBundleConormal.chartLinearForm`: **the linear form** `Γ(ℰ, U) →ₗ Γ(X, U)`,
  namely `q` on sections read in the frame.
* `Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv`: **`Γ(ker q, U) ≃ₗ ker p`.**

## Main results

* `Stacks.ProjectiveBundleConormal.chartLinearForm_apply_eq_one`: `p s = 1` when `e (q s) = 1`.
* `Stacks.ProjectiveBundleConormal.span_singleton_app_eq_top_of_chartLinearForm_eq_one`: if
  `p s = 1`, then `q s` generates `Γ(𝓛, U)`.
* `Stacks.ProjectiveBundleConormal.ker_chartLinearForm`: the kernel of the linear form is the
  kernel of `q` on sections.
* `Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv_coe`: the identification is the
  inclusion of the kernel on sections.
* `Stacks.ProjectiveBundleConormal.exists_affine_open_chartLinearForm`: around every point of `X`
  there is an affine open carrying such a `p` and `s`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QcohLimits

universe u

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}} {E : X.Modules} (Q : Stacks.Divisors.InvertibleQuotient X E)
  (U : X.Opens) (e : Γ(Q.L, U) ≃ₗ[Γ(X, U)] Γ(X, U))

/-! ### The linear form -/

/-- **The linear form cutting out the chart**: the invertible quotient `q` read on sections over
`U` in the frame `e`, i.e. `x ↦ e (q x)`. -/
def chartLinearForm : Γ(E, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (e : Γ(Q.L, U) →ₗ[Γ(X, U)] Γ(X, U)).comp (appₗ Q.q U)

/-- The linear form cutting out the chart sends a section `x` of `ℰ` over `U` to `e (q x)`. -/
@[simp] theorem chartLinearForm_apply (x : Γ(E, U)) :
    chartLinearForm Q U e x = e (Q.q.app U x) := rfl

/-- If the frame carries the image of `s` to `1`, then the linear form cutting out the chart takes
the value `1` at `s`. -/
theorem chartLinearForm_apply_eq_one {s : Γ(E, U)} (hs : e (Q.q.app U s) = 1) :
    chartLinearForm Q U e s = 1 := hs

/-- **The frame section spans.** If the linear form cutting out the chart takes the value `1` at
`s` then the image of `s` generates `Γ(𝓛, U)` as a module over `Γ(X, U)`. -/
theorem span_singleton_app_eq_top_of_chartLinearForm_eq_one {s : Γ(E, U)}
    (hs : chartLinearForm Q U e s = 1) :
    Submodule.span Γ(X, U) {Q.q.app U s} = ⊤ := by
  have hs' : e (Q.q.app U s) = 1 := hs
  exact eq_top_iff.2 fun y _ =>
    Submodule.mem_span_singleton.2 ⟨e y, e.injective (by simp [hs'])⟩

/-- **Reading `q` in a frame does not change its kernel**, the frame being injective. -/
theorem ker_chartLinearForm :
    LinearMap.ker (chartLinearForm Q U e) = LinearMap.ker (appₗ Q.q U) :=
  LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_injective e.injective)

/-! ### The kernel of the form is the sections of the kernel -/

/-- **`Γ(ker q, U) ≃ₗ ker p`.** The sections over `U` of the kernel of the invertible quotient are
the kernel of the linear form cutting out the chart. -/
def kernelSectionsKerEquiv :
    Γ(kernel Q.q, U) ≃ₗ[Γ(X, U)] ↥(LinearMap.ker (chartLinearForm Q U e)) :=
  (kerEquivOfExact (appₗ (kernel.ι Q.q) U) (appₗ Q.q U) (injective_app_kernel_ι Q.q U)
      (exact_app_kernel Q.q U)).trans
    (LinearEquiv.ofEq _ _ (ker_chartLinearForm Q U e).symm)

/-- The identification `Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv` sends a section of
the kernel of `q` to its image under the inclusion of the kernel. -/
@[simp] theorem kernelSectionsKerEquiv_coe (x : Γ(kernel Q.q, U)) :
    ((kernelSectionsKerEquiv Q U e x : ↥(LinearMap.ker (chartLinearForm Q U e))) : Γ(E, U)) =
      (kernel.ι Q.q).app U x :=
  rfl

/-! ### The cover -/

/-- **The cover carrying the chart data.** Around every point of `X` there is an affine open `U`,
a frame for `𝓛` on `U` and a section `s` of `ℰ` on `U` at which the linear form
`Stacks.ProjectiveBundleConormal.chartLinearForm` takes the value `1`. -/
theorem exists_affine_open_chartLinearForm (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ (e : Γ(Q.L, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (s : Γ(E, U)), chartLinearForm Q U e s = 1 := by
  obtain ⟨U, hxU, hU, -, e, s, hs⟩ := exists_affine_open_splitting Q x
  exact ⟨U, hxU, hU, e, s, chartLinearForm_apply_eq_one Q U e hs⟩

end Stacks.ProjectiveBundleConormal

end
