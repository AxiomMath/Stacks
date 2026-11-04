module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Functionals dual to a power basis bound the cokernel of a trace map

Let `A` be a domain, `B` an `A`-algebra and `g ∈ B` such that every element of `B` has a nonzero
multiple in the `A`-span of `1, g, …, g^{n-1}`. Let `N = A ε` be a torsion free cyclic `A`-module
and `t ∈ A`. If `φ₀, …, φ_{n-1} : B → N` are `A`-linear with `φᵢ(gʲ) = δᵢⱼ t ε`, then every
`A`-linear `ψ : B → N` satisfies `t ψ ∈ span_A {φᵢ}`. Consequently, for any `A`-linear map `T`
into `Hom_A(B, N)` whose image contains the `φᵢ`, the element `t` annihilates the cokernel of `T`.

This is the lattice argument of the second paragraph of the proof of [Stacks, Tag 0B4U]: there
`A` is a complete regular local ring of dimension two, `B` the integral closure of `A` in a purely
inseparable extension `L = K[g]` of degree `p` of its fraction field, `N = ω_A = Ω^{e+2}_{A/A₀}`,
`t ε = θ = η ∧ df`, and the `φᵢ` are the images under `c : Ω^{e+2}_{B/A₀} ⟶ Hom_A(B, ω_A)` of the
forms `ωᵢ = η ∧ g^{p-1-i} dg`, whose values `φᵢ(gʲ) = Tr(η ∧ g^{p-1-i+j} dg) = δᵢⱼ θ` are the
explicit values of the trace of [Stacks, Tag 0AX5]. The argument only needs those values, the
fact that `1, g, …, g^{p-1}` span `L` over `K`, and that `ω_A` is free of rank one; it is stated
here at that generality. The same argument applies verbatim to the trace
`Γ(Y, ω_Y) ⟶ ω_B` of a normal modification `Y` of `Spec B` once its image is known to contain the
`φᵢ`, which is how the source concludes with [Stacks, Tag 0B4S].

## Main results

* `Stacks.ResolutionOfSurfaces.smul_mem_span_of_apply_pow_eq`: `t ψ` lies in the span of the
  `φᵢ`.
* `Stacks.ResolutionOfSurfaces.smul_eq_zero_of_apply_pow_eq_of_mem_range`: `t` annihilates the
  cokernel of any linear map into `Hom_A(B, N)` whose image contains the `φᵢ`.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public section

namespace Stacks.ResolutionOfSurfaces

variable {A B N : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module A N] [Module.IsTorsionFree A N]

/-- Let `g ∈ B` be such that every element of `B` has a nonzero `A`-multiple in the span of
`1, g, …, g^{n-1}`, let `N = A ε` be torsion free and cyclic, and let `φ₀, …, φ_{n-1} : B → N`
satisfy `φᵢ(gʲ) = δᵢⱼ t ε`. Then `t ψ` is an `A`-linear combination of the `φᵢ` for every
`A`-linear `ψ : B → N`: writing `ψ(gʲ) = cⱼ ε`, the map `t ψ - ∑ cᵢ φᵢ` vanishes on every `gʲ`,
hence on the span of the `gʲ`, hence on `B` because `N` is torsion free. -/
theorem smul_mem_span_of_apply_pow_eq {n : ℕ} (g : B)
    (hgen : ∀ b : B, ∃ a : A, a ≠ 0 ∧
      a • b ∈ Submodule.span A (Set.range fun j : Fin n => g ^ (j : ℕ)))
    (ε : N) (hε : ∀ x : N, ∃ c : A, x = c • ε) (t : A) (φ : Fin n → B →ₗ[A] N)
    (hφ : ∀ i j : Fin n, φ i (g ^ (j : ℕ)) = if i = j then t • ε else 0)
    (ψ : B →ₗ[A] N) : t • ψ ∈ Submodule.span A (Set.range φ) := by
  classical
  choose c hc using fun j : Fin n => hε (ψ (g ^ (j : ℕ)))
  have hχ : t • ψ = ∑ i, c i • φ i := by
    set χ : B →ₗ[A] N := t • ψ - ∑ i, c i • φ i with hχdef
    have hpow : ∀ j : Fin n, χ (g ^ (j : ℕ)) = 0 := by
      intro j
      simp only [hχdef, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, hφ,
        smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hc j, smul_smul,
        mul_comm t, sub_self]
    have hspan : ∀ x ∈ Submodule.span A (Set.range fun j : Fin n => g ^ (j : ℕ)), χ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact hpow j
      | zero => exact map_zero χ
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    have hzero : χ = 0 := by
      ext b
      obtain ⟨a, ha, hab⟩ := hgen b
      have h1 : a • χ b = a • (0 : N) := by rw [← map_smul, hspan _ hab, smul_zero]
      exact smul_right_injective N ha h1
    exact sub_eq_zero.mp hzero
  rw [hχ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- In the situation of `Stacks.ResolutionOfSurfaces.smul_mem_span_of_apply_pow_eq`, `t`
annihilates the cokernel of any `A`-linear map `T : M → Hom_A(B, N)` whose image contains the
functionals `φᵢ` dual to the powers of `g`. This is the form in which [Stacks, Tag 0B4U] uses the
lattice argument: once the image of the trace `Γ(Y, ω_Y) ⟶ ω_B = Hom_A(B, ω_A)` of a normal
modification `Y` of `Spec B` contains the `φᵢ`, its cokernel is annihilated by `t`. -/
theorem smul_eq_zero_of_apply_pow_eq_of_mem_range {M : Type*} [AddCommGroup M] [Module A M]
    {n : ℕ} (g : B)
    (hgen : ∀ b : B, ∃ a : A, a ≠ 0 ∧
      a • b ∈ Submodule.span A (Set.range fun j : Fin n => g ^ (j : ℕ)))
    (ε : N) (hε : ∀ x : N, ∃ c : A, x = c • ε) (t : A) (φ : Fin n → B →ₗ[A] N)
    (hφ : ∀ i j : Fin n, φ i (g ^ (j : ℕ)) = if i = j then t • ε else 0)
    (T : M →ₗ[A] (B →ₗ[A] N)) (hT : ∀ i, φ i ∈ LinearMap.range T)
    (z : (B →ₗ[A] N) ⧸ LinearMap.range T) : t • z = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H ψ =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.span_le.mpr ?_ (smul_mem_span_of_apply_pow_eq g hgen ε hε t φ hφ ψ)
    rintro _ ⟨i, rfl⟩
    exact hT i

end Stacks.ResolutionOfSurfaces

end
