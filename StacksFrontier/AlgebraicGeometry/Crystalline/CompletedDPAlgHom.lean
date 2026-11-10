module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsOfCompletion

/-!
# Divided power algebra maps out of a `p`-adic completion

Let `(B₁, J₁, δ₁)` and `(B₂, J₂, δ₂)` be divided power rings over `A`, with `p` nilpotent modulo
`J₁` and `J₂`, and `B̂₁`, `B̂₂` their `p`-adic completions with the completed divided powers of
[Stacks, Tag 07KD].  A divided power `A`-algebra map `B₁ → B̂₂` extends uniquely to a divided power
`A`-algebra map `B̂₁ → B̂₂` (`Crystalline.exists_completedDPAlgHom`); in particular a divided
power `A`-algebra map `B₁ → B₂` has a completion (`Crystalline.completedDPAlgHom`).  Two algebra
maps out of `B̂₁` agreeing on `B₁` are equal (`Crystalline.completedAlgHom_ext`).

## References

* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public noncomputable section

open DividedPowers

universe u

namespace Crystalline

section Completion

variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (IntegersAtPrime p) A]
  {B₁ : Type u} [CommRing B₁] [Algebra A B₁] {J₁ : Ideal B₁} (h₁ : DividedPowers J₁)
  (hp₁ : IsNilpotent (Ideal.Quotient.mk J₁ (p : B₁)))
  {B₂ : Type u} [CommRing B₂] [Algebra A B₂] {J₂ : Ideal B₂} (h₂ : DividedPowers J₂)
  (hp₂ : IsNilpotent (Ideal.Quotient.mk J₂ (p : B₂)))

local notation "B̂₁" => AdicCompletion (pAdicIdeal (A := B₁) p) B₁
local notation "B̂₂" => AdicCompletion (pAdicIdeal (A := B₂) p) B₂

omit [Fact (Nat.Prime p)] in
/-- **Two ring maps out of `B̂₁` into a `p`-adic completion agreeing on `B₁` are equal.** -/
theorem completedRingHom_ext {φ ψ : B̂₁ →+* B̂₂}
    (h : ∀ b, φ (AdicCompletion.of _ B₁ b) = ψ (AdicCompletion.of _ B₁ b)) : φ = ψ := by
  have := adicCompletion_addMonoidHom_ext_of_of p (f := φ.toAddMonoidHom)
    (g := ψ.toAddMonoidHom) h
  exact RingHom.ext fun x ↦ DFunLike.congr_fun this x

omit [Fact (Nat.Prime p)] [Algebra (IntegersAtPrime p) A] in
/-- **Two algebra maps out of `B̂₁` into a `p`-adic completion agreeing on `B₁` are equal.** -/
theorem completedAlgHom_ext {φ ψ : B̂₁ →ₐ[A] B̂₂}
    (h : ∀ b, φ (AdicCompletion.of _ B₁ b) = ψ (AdicCompletion.of _ B₁ b)) : φ = ψ :=
  AlgHom.toRingHom_injective (completedRingHom_ext p (φ := φ.toRingHom) (ψ := ψ.toRingHom) h)

/-- **A divided power `A`-algebra map `B₁ → B̂₂` extends to `B̂₁`.** -/
theorem exists_completedDPAlgHom (f : B₁ →ₐ[A] B̂₂)
    (hf : IsDPMorphism h₁ (completionDividedPowers p h₂ hp₂) f.toRingHom) :
    ∃ φ : B̂₁ →ₐ[A] B̂₂,
      IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
        φ.toRingHom ∧ ∀ b, φ (AdicCompletion.of _ B₁ b) = f b := by
  let : Algebra (IntegersAtPrime p) B₁ :=
    ((algebraMap A B₁).comp (algebraMap (IntegersAtPrime p) A)).toAlgebra
  let : Algebra (IntegersAtPrime p) B̂₂ :=
    ((algebraMap A B̂₂).comp (algebraMap (IntegersAtPrime p) A)).toAlgebra
  obtain ⟨g, hg⟩ := exists_dPMorphism_from_completion J₁ h₁ (completionIdeal J₂ p hp₂)
    (completionDividedPowers p h₂ hp₂) p hp₁ (isNilpotent_mk_completionIdeal J₂ p hp₂)
    ⟨f.toRingHom, hf.1, hf.2⟩
  have hgof : ∀ b, g (AdicCompletion.of _ B₁ b) = f b := fun b ↦ by
    have := congrArg (fun r : B₁ →+* B̂₂ ↦ r b) hg
    simpa [AdicCompletion.algebraMap_apply] using this
  refine ⟨{ g.toRingHom with commutes' := fun c ↦ ?_ }, g.isDPMorphism, hgof⟩
  change g (algebraMap A B̂₁ c) = algebraMap A B̂₂ c
  rw [AdicCompletion.algebraMap_apply, hgof, f.commutes]

/-- **The completion of a divided power `A`-algebra map `B₁ → B₂`**, as a divided power
`A`-algebra map `B̂₁ → B̂₂`. -/
def completedDPAlgHom (f : B₁ →ₐ[A] B₂) (hf : IsDPMorphism h₁ h₂ f.toRingHom) : B̂₁ →ₐ[A] B̂₂ :=
  (exists_completedDPAlgHom p A h₁ hp₁ h₂ hp₂ ((completionAlgHom p A).comp f)
    ((isDPMorphism_completionAlgHom p A h₂ hp₂).comp _ hf)).choose

/-- The completion of a divided power morphism extends it and is a divided power morphism. -/
private theorem completedDPAlgHom_spec (f : B₁ →ₐ[A] B₂) (hf : IsDPMorphism h₁ h₂ f.toRingHom) :
    IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      (completedDPAlgHom p A h₁ hp₁ h₂ hp₂ f hf).toRingHom ∧
    ∀ b, completedDPAlgHom p A h₁ hp₁ h₂ hp₂ f hf (AdicCompletion.of _ B₁ b) =
      completionAlgHom p A (f b) :=
  (exists_completedDPAlgHom p A h₁ hp₁ h₂ hp₂ ((completionAlgHom p A).comp f)
    ((isDPMorphism_completionAlgHom p A h₂ hp₂).comp _ hf)).choose_spec

/-- The completion of a divided power morphism is a divided power morphism. -/
theorem isDPMorphism_completedDPAlgHom (f : B₁ →ₐ[A] B₂) (hf : IsDPMorphism h₁ h₂ f.toRingHom) :
    IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      (completedDPAlgHom p A h₁ hp₁ h₂ hp₂ f hf).toRingHom :=
  (completedDPAlgHom_spec p A h₁ hp₁ h₂ hp₂ f hf).1

/-- The completion of `f` extends `f`. -/
@[simp] theorem completedDPAlgHom_of (f : B₁ →ₐ[A] B₂) (hf : IsDPMorphism h₁ h₂ f.toRingHom)
    (b : B₁) :
    completedDPAlgHom p A h₁ hp₁ h₂ hp₂ f hf (AdicCompletion.of _ B₁ b) =
      AdicCompletion.of _ B₂ (f b) :=
  ((completedDPAlgHom_spec p A h₁ hp₁ h₂ hp₂ f hf).2 b).trans (completionAlgHom_apply p A (f b))

end Completion

end Crystalline

end
