module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The kernel of a map out of an injective module, from vanishing of `Hom(R/𝔞, -)`-cohomology

Let `J₀ --d₀--> J₁ --d₁--> J₂` be a complex of modules over a ring `R` with `J₀` injective. If
for every left ideal `𝔞` of `R` every `ψ : R/𝔞 → J₁` with `d₁ ∘ ψ = 0` is of the form `d₀ ∘ χ`
(the cohomology of `Hom_R(R/𝔞, J)` at `J₁` vanishes), then `ker d₀` is injective. Given
`φ : 𝔞 → ker d₀`, extend it to `ψ₀ : R → J₀`; then `d₀ ∘ ψ₀` factors through `R/𝔞` as a cocycle,
hence is `d₀ ∘ χ`, and `ψ₀ - χ` is an extension of `φ` with values in `ker d₀`. This is Baer's
criterion.

For a bounded below complex of injective modules `J` with `H^i(Hom_R(R/𝔞, J)) = 0` for `i > b`,
the cycles `Z^b(J)` are therefore injective and `J` is quasi-isomorphic to the bounded complex of
injective modules `τ_{≤ b} J`: the step from the vanishing of `Ext^{> b}` into `J` to finite
injective dimension, used for the perfectness of `RΓ_c(U_k̄, D(A[H]))` over the quasi-Frobenius
ring `(ℤ/ℓⁿ)[H]` in the proof of [Stacks, Tag 03UG].

## Main results

* `Module.baer_ker_of_injective_of_cocycle`: Baer's criterion for `ker d₀`.
* `Module.injective_ker_of_injective_of_cocycle`: `ker d₀` is injective.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [Ring R] {J₀ J₁ J₂ : Type v} [AddCommGroup J₀] [Module R J₀]
  [AddCommGroup J₁] [Module R J₁] [AddCommGroup J₂] [Module R J₂]

/-- **Baer's criterion for the kernel of a map out of an injective module** whose cokernel
cocycles out of every cyclic module `R/𝔞` are coboundaries. -/
theorem baer_ker_of_injective_of_cocycle [Small.{v} R] [Module.Injective R J₀]
    (d₀ : J₀ →ₗ[R] J₁) (d₁ : J₁ →ₗ[R] J₂) (hd : d₁ ∘ₗ d₀ = 0)
    (h : ∀ (I : Ideal R) (ψ : (R ⧸ I) →ₗ[R] J₁), d₁ ∘ₗ ψ = 0 →
      ∃ χ : (R ⧸ I) →ₗ[R] J₀, d₀ ∘ₗ χ = ψ) :
    Module.Baer R (LinearMap.ker d₀) := by
  intro I φ
  obtain ⟨ψ₀, hψ₀⟩ := Module.Baer.of_injective (R := R) (Q := J₀) inferInstance I
    ((LinearMap.ker d₀).subtype ∘ₗ φ)
  have hI : I ≤ LinearMap.ker (d₀ ∘ₗ ψ₀) := fun x hx => by
    simpa [hψ₀ x hx] using (φ ⟨x, hx⟩).2
  obtain ⟨χ, hχ⟩ := h I (I.liftQ (d₀ ∘ₗ ψ₀) hI) <|
    Submodule.linearMap_qext _ (LinearMap.ext fun x => LinearMap.congr_fun hd (ψ₀ x))
  have hker : ∀ x, (ψ₀ - χ ∘ₗ I.mkQ) x ∈ LinearMap.ker d₀ := fun x => by
    simp [← LinearMap.comp_apply d₀ χ, hχ]
  refine ⟨LinearMap.codRestrict _ _ hker, fun x hx => Subtype.ext ?_⟩
  simp [(Submodule.Quotient.mk_eq_zero I).2 hx, hψ₀ x hx]

/-- **The kernel of a map out of an injective module is injective** when the cohomology of
`Hom_R(R/𝔞, J)` vanishes at the next term, for every left ideal `𝔞`. -/
theorem injective_ker_of_injective_of_cocycle [Small.{v} R] [Module.Injective R J₀]
    (d₀ : J₀ →ₗ[R] J₁) (d₁ : J₁ →ₗ[R] J₂) (hd : d₁ ∘ₗ d₀ = 0)
    (h : ∀ (I : Ideal R) (ψ : (R ⧸ I) →ₗ[R] J₁), d₁ ∘ₗ ψ = 0 →
      ∃ χ : (R ⧸ I) →ₗ[R] J₀, d₀ ∘ₗ χ = ψ) :
    Module.Injective R (LinearMap.ker d₀) :=
  (baer_ker_of_injective_of_cocycle d₀ d₁ hd h).injective

end Module
