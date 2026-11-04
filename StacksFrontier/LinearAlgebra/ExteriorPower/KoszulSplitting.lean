module

public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul

/-!
# Splitting an exterior power along a vector with a unimodular functional

Let `M` be a module over a commutative ring `R`, let `e : M` and let `φ : M →ₗ[R] R` be a linear
functional with `φ e = 1`. Then `M = R · e ⊕ N` for `N = ker φ`, and the exterior powers inherit
the decomposition

`⋀^{n+1} M = ⋀^{n+1} N ⊕ e ∧ ⋀^n N`.

This file proves that decomposition in the intrinsic form that the geometric application needs:
the first summand is realised as the kernel of the Koszul contraction against `φ` and the second
as the range of left wedge multiplication by `e`.

## Main results

* `exteriorPower.contraction_wedgeLeft_add_wedgeLeft_contraction_eq_self`: the Koszul identity of
  `StacksFrontier.LinearAlgebra.ExteriorPower.Koszul` when `φ e = 1`, which is the decomposition of
  a form into its two components.
* `exteriorPower.isCompl_ker_contraction_range_wedgeLeft`: **the splitting**, that the kernel of
  the contraction and the range of wedging with `e` are complementary submodules of `⋀^{n+1} M`.
* `exteriorPower.injective_wedgeLeft_of_mem_ker_contraction`: wedging with `e` is injective on
  the kernel of the contraction, so the second summand really is a copy of `⋀^n N`.

## Implementation notes

The complement is described by a kernel and a range rather than by exhibiting `N = ker φ` and its
exterior powers as submodules of `⋀ M`. That is what makes the statement usable where it is
applied: there the splitting comes from a functional whose existence is known but which is not
canonical, so no distinguished `N` is available, while the contraction and the wedge are written
down directly from `φ` and `e`.

The range of `exteriorPower.wedgeLeft e n` is the image of all of `⋀^n M`, not only of the
kernel of the contraction; the two agree, since wedging with `e` kills the part of `⋀^n M`
already divisible by `e`, and the kernel-free spelling avoids carrying a subtype.

Both summands are stated for `⋀^{n+1} M`, with the contraction `⋀^{n+1} M →ₗ ⋀^n M` indexed by
the lower degree, matching the indexing of `exteriorPower.contraction`. Degree zero is not a
special case to be stated separately: `⋀^0 M` has no contraction into negative degrees and the
decomposition there is vacuous.
-/

@[expose] public section

namespace exteriorPower

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **The Koszul identity for a unimodular functional.** If `φ e = 1` then every `(n+1)`-form is
the sum of its contraction-free part and `e` wedged with its contraction. -/
theorem contraction_wedgeLeft_add_wedgeLeft_contraction_eq_self (φ : M →ₗ[R] R) (e : M)
    (he : φ e = 1) (n : ℕ) (ω : ⋀[R]^(n + 1) M) :
    contraction φ (n + 1) (wedgeLeft e (n + 1) ω) + wedgeLeft e n (contraction φ n ω) = ω := by
  simpa only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, he, one_smul] using
    DFunLike.congr_fun (contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction φ e n) ω

/-- The contraction-free part of a form really is annihilated by the contraction: the contraction
squares to zero. -/
theorem contraction_wedgeLeft_mem_ker_contraction (φ : M →ₗ[R] R) (e : M) (n : ℕ)
    (ω : ⋀[R]^(n + 1) M) :
    contraction φ (n + 1) (wedgeLeft e (n + 1) ω) ∈ LinearMap.ker (contraction φ n) := by
  simpa only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.zero_apply] using
    DFunLike.congr_fun (contraction_comp_contraction φ n) (wedgeLeft e (n + 1) ω)

/-- Wedging with `e` twice is zero, in applied form. -/
theorem wedgeLeft_wedgeLeft_apply (e : M) (n : ℕ) (ξ : ⋀[R]^n M) :
    wedgeLeft (R := R) e (n + 1) (wedgeLeft e n ξ) = 0 := by
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] using
    DFunLike.congr_fun (wedgeLeft_comp_wedgeLeft (R := R) e n) ξ

/-- On the kernel of the contraction, wedging with `e` and then contracting is the identity. -/
private theorem contraction_wedgeLeft_eq_self_of_mem_ker (φ : M →ₗ[R] R) (e : M) (he : φ e = 1)
    (n : ℕ) {x : ⋀[R]^(n + 1) M} (hx : x ∈ LinearMap.ker (contraction φ n)) :
    contraction φ (n + 1) (wedgeLeft e (n + 1) x) = x := by
  simpa [LinearMap.mem_ker.1 hx] using
    contraction_wedgeLeft_add_wedgeLeft_contraction_eq_self φ e he n x

/-- **The exterior power splits along a vector with a unimodular functional.** For `φ e = 1` the
kernel of the contraction against `φ` and the range of wedge multiplication by `e` are
complementary submodules of `⋀^{n+1} M`. -/
theorem isCompl_ker_contraction_range_wedgeLeft (φ : M →ₗ[R] R) (e : M) (he : φ e = 1) (n : ℕ) :
    IsCompl (LinearMap.ker (contraction φ n)) (LinearMap.range (wedgeLeft (R := R) e n)) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hker ⟨ξ, hξ⟩
    rw [← contraction_wedgeLeft_eq_self_of_mem_ker φ e he n hker, ← hξ,
      wedgeLeft_wedgeLeft_apply, map_zero]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro ω
    rw [← contraction_wedgeLeft_add_wedgeLeft_contraction_eq_self φ e he n ω]
    exact Submodule.add_mem_sup (contraction_wedgeLeft_mem_ker_contraction φ e n ω)
      ⟨contraction φ n ω, rfl⟩

/-- Wedging with `e` is injective on the kernel of the contraction: the summand
`e ∧ ⋀^n N` of the splitting is a faithful copy of `⋀^n N`. -/
theorem injective_wedgeLeft_of_mem_ker_contraction (φ : M →ₗ[R] R) (e : M) (he : φ e = 1)
    (n : ℕ) {ξ η : ⋀[R]^(n + 1) M} (hξ : ξ ∈ LinearMap.ker (contraction φ n))
    (hη : η ∈ LinearMap.ker (contraction φ n))
    (h : wedgeLeft (R := R) e (n + 1) ξ = wedgeLeft e (n + 1) η) : ξ = η := by
  rw [← contraction_wedgeLeft_eq_self_of_mem_ker φ e he n hξ,
    ← contraction_wedgeLeft_eq_self_of_mem_ker φ e he n hη, h]

end exteriorPower

end
