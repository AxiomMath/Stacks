module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of a two-periodic complex on a quotient

Let `φ` and `ψ` be endomorphisms of a module `M` whose composites `φ ∘ ψ` and `ψ ∘ φ` have the
same image. Both maps then descend to the quotient of `M` by that image, and the resulting
two-periodic sequence is exact as soon as the opposite map is injective.

## Main definitions

* `AlgebraicGeometry.periodicQuotientPhi` and `AlgebraicGeometry.periodicQuotientPsi` are the
  endomorphisms induced by `φ` and `ψ` on the quotient of `M` by the image of `φ ∘ ψ`.

## Main results

* `AlgebraicGeometry.exact_periodicQuotient_phi_psi` gives exactness at the occurrence between
  the induced maps of `φ` and `ψ`.
* `AlgebraicGeometry.exact_periodicQuotient_psi_phi` gives exactness at the other occurrence.

## Implementation notes

An exact `(2, 1)`-periodic complex is recorded by the two `Function.Exact` assertions for its
alternating differentials. The Noetherian, local, finite and dimension assumptions of the
source are not needed for exactness; they are used for the finite-length half of the same
result, which is `Module.isFiniteLength_quotient_range_of_injective`.

## References

* [Stacks Project, Tag 02PX](https://stacks.math.columbia.edu/tag/02PX)
-/

@[expose] public section

namespace AlgebraicGeometry

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The endomorphism induced by `φ` on the quotient by the image of `φ ∘ ψ`. -/
def periodicQuotientPhi (φ ψ : M →ₗ[R] M)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ)) :
    (M ⧸ LinearMap.range (φ ∘ₗ ψ)) →ₗ[R] (M ⧸ LinearMap.range (φ ∘ₗ ψ)) :=
  Submodule.mapQ _ _ φ (by
    intro y hy
    rw [hcomm] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨φ x, rfl⟩)

/-- The endomorphism induced by `ψ` on the quotient by the image of `φ ∘ ψ`. -/
def periodicQuotientPsi (φ ψ : M →ₗ[R] M)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ)) :
    (M ⧸ LinearMap.range (φ ∘ₗ ψ)) →ₗ[R] (M ⧸ LinearMap.range (φ ∘ₗ ψ)) :=
  Submodule.mapQ _ _ ψ (by
    intro y hy
    rw [hcomm]
    obtain ⟨x, rfl⟩ := hy
    exact ⟨ψ x, rfl⟩)

/-- Exactness of two maps induced on a quotient `M ⧸ p`, when `g` is injective. -/
private theorem exact_mapQ_of_injective {f g : M →ₗ[R] M} {p : Submodule R M}
    {hf : p ≤ p.comap f} {hg : p ≤ p.comap g} (hinj : Function.Injective g)
    (hfg : ∀ x, g (f x) ∈ p) (hker : ∀ x, g x ∈ p → ∃ z, g (f z) = g x) :
    Function.Exact (p.mapQ p f hf) (p.mapQ p g hg) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    constructor
    · intro hx
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨z, hz⟩ := hker x hx
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      rw [Submodule.mapQ_apply]
      exact congrArg _ (hinj hz)
    · rintro ⟨q, hq⟩
      rw [← hq]
      induction q using Submodule.Quotient.induction_on with
      | _ x =>
        rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hfg x

/-- On the quotient by the common composite image, the map induced by `φ` is exact before
the map induced by `ψ`. -/
@[stacks 02PX "periodic_exactness"]
theorem exact_periodicQuotient_phi_psi (φ ψ : M →ₗ[R] M)
    (hψ : Function.Injective ψ)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ)) :
    Function.Exact (periodicQuotientPhi φ ψ hcomm) (periodicQuotientPsi φ ψ hcomm) :=
  exact_mapQ_of_injective hψ (fun x => hcomm ▸ ⟨x, rfl⟩) fun x hx => by
    obtain ⟨z, hz⟩ := hcomm ▸ hx
    exact ⟨z, hz⟩

/-- On the quotient by the common composite image, the map induced by `ψ` is exact before
the map induced by `φ`. -/
@[stacks 02PX "periodic_exactness"]
theorem exact_periodicQuotient_psi_phi (φ ψ : M →ₗ[R] M)
    (hφ : Function.Injective φ)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ)) :
    Function.Exact (periodicQuotientPsi φ ψ hcomm) (periodicQuotientPhi φ ψ hcomm) :=
  exact_mapQ_of_injective hφ (fun x => ⟨x, rfl⟩) fun _ ⟨z, hz⟩ => ⟨z, hz⟩

end AlgebraicGeometry
