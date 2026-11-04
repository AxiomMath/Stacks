module

public import StacksFrontier.RingTheory.FormsTrace.BaseChange

/-!
# Transport of trace maps on forms along isomorphisms of algebras

Let `φ : B ≃ₐ[A] B'` be an isomorphism of `A`-algebras. A family `Θ^p : Ω^p_B → Ω^p_A` transports
to the family `Θ^p ∘ φ^{-1,*} : Ω^p_{B'} → Ω^p_A`, and the conditions of Stacks, Lemma 0FLB and
Proposition 0FLC transport with it. This is how the trace maps of the algebra
`Carrier (ofBasis e)` of structure constants are carried to an algebra `B` with a basis `e`.

## Main definitions

* `Stacks.FormsTrace.formsMapEquiv`: the `A`-linear pull-back of forms along an isomorphism of
  `A`-algebras.
* `Stacks.FormsTrace.transport`: the transported family.

## Main results

* `Stacks.FormsTrace.trace_algEquiv`: the trace is invariant under isomorphisms of algebras.
* `Stacks.FormsTrace.IsFormsTrace.transport`, `Stacks.FormsTrace.IsWedgeLinear.transport`,
  `Stacks.FormsTrace.CommutesWithD.transport`: the conditions transport.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u

namespace Stacks.FormsTrace

variable {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']

/-- The pull-back of forms along an isomorphism of `A`-algebras `B' → B` (the inverse of
`φ : B ≃ₐ[A] B'`), as an `A`-linear map `Ω^p_{B'} → Ω^p_B`. -/
def formsMapEquiv (φ : B ≃ₐ[A] B') (p : ℕ) : ⋀[B']^p Ω[B'⁄ℤ] →ₗ[A] ⋀[B]^p Ω[B⁄ℤ] :=
  letI : Algebra B' B := φ.symm.toRingHom.toAlgebra
  haveI : IsScalarTower A B' B := IsScalarTower.of_algebraMap_eq fun a => (φ.symm.commutes a).symm
  { toFun := formsMap B' B p
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [← algebraMap_smul B' a x, map_smulₛₗ, ← IsScalarTower.algebraMap_apply,
        algebraMap_smul, RingHom.id_apply] }

/-- `formsMapEquiv` is the pull-back of forms. -/
theorem formsMapEquiv_apply (φ : B ≃ₐ[A] B') (p : ℕ) (x : ⋀[B']^p Ω[B'⁄ℤ]) :
    letI : Algebra B' B := φ.symm.toRingHom.toAlgebra
    formsMapEquiv φ p x = formsMap B' B p x :=
  rfl

/-- The pull-back of a pulled back form of `A` along `φ⁻¹` is the pulled back form. -/
theorem formsMapEquiv_formsMap (φ : B ≃ₐ[A] B') (p : ℕ) (ω : ⋀[A]^p Ω[A⁄ℤ]) :
    formsMapEquiv φ p (formsMap A B' p ω) = formsMap A B p ω := by
  let : Algebra B' B := φ.symm.toRingHom.toAlgebra
  have : IsScalarTower A B' B := IsScalarTower.of_algebraMap_eq fun a => (φ.symm.commutes a).symm
  exact formsMap_formsMap p ω

/-- `formsMapEquiv` is semilinear over `φ⁻¹`. -/
theorem formsMapEquiv_smul (φ : B ≃ₐ[A] B') (p : ℕ) (b : B') (x : ⋀[B']^p Ω[B'⁄ℤ]) :
    formsMapEquiv φ p (b • x) = φ.symm b • formsMapEquiv φ p x := by
  let : Algebra B' B := φ.symm.toRingHom.toAlgebra
  exact map_smulₛₗ (formsMap B' B p) b x

/-- `formsMapEquiv` is multiplicative for the wedge product. -/
theorem formsMapEquiv_wedgeMul (φ : B ≃ₐ[A] B') (q p : ℕ) (x : ⋀[B']^q Ω[B'⁄ℤ])
    (y : ⋀[B']^p Ω[B'⁄ℤ]) :
    formsMapEquiv φ (q + p) (exteriorPower.wedgeMul q p x y) =
      exteriorPower.wedgeMul q p (formsMapEquiv φ q x) (formsMapEquiv φ p y) := by
  let : Algebra B' B := φ.symm.toRingHom.toAlgebra
  rw [formsMapEquiv_apply, formsMapEquiv_apply, formsMapEquiv_apply]
  exact formsMap_wedgeMul q p x y

/-- `formsMapEquiv` commutes with the de Rham differential. -/
theorem formsMapEquiv_deRhamDifferential (φ : B ≃ₐ[A] B') (p : ℕ) (x : ⋀[B']^p Ω[B'⁄ℤ]) :
    formsMapEquiv φ (p + 1) (deRhamDifferential p x) =
      deRhamDifferential p (formsMapEquiv φ p x) := by
  let : Algebra B' B := φ.symm.toRingHom.toAlgebra
  rw [formsMapEquiv_apply, formsMapEquiv_apply]
  exact formsMap_deRhamDifferential p x

/-- **The trace is invariant under isomorphisms of algebras.** -/
theorem trace_algEquiv [Module.Finite A B] [Module.Projective A B] [Module.Finite A B']
    [Module.Projective A B'] (φ : B ≃ₐ[A] B') (b : B) : trace A B' (φ b) = trace A B b := by
  have h : Algebra.lmul A B' (φ b) =
      φ.toLinearEquiv.toLinearMap ∘ₗ (Algebra.lmul A B b ∘ₗ φ.toLinearEquiv.symm.toLinearMap) := by
    refine LinearMap.ext fun x => ?_
    simp [map_mul]
  rw [trace, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h,
    Stacks.Discriminant.finiteProjectiveTrace_conj]
  rfl

/-- **The transported family** `Θ^p ∘ φ^{-1,*} : Ω^p_{B'} → Ω^p_A`. -/
def transport (φ : B ≃ₐ[A] B') (Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]) (p : ℕ) :
    ⋀[B']^p Ω[B'⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ] :=
  Θ p ∘ₗ formsMapEquiv φ p

/-- `transport` unfolded. -/
theorem transport_apply (φ : B ≃ₐ[A] B') (Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ])
    (p : ℕ) (x : ⋀[B']^p Ω[B'⁄ℤ]) : transport φ Θ p x = Θ p (formsMapEquiv φ p x) :=
  rfl

/-- **Property (1) of Lemma 0FLB transports** along an isomorphism of algebras. -/
theorem IsFormsTrace.transport [Module.Finite A B] [Module.Projective A B] [Module.Finite A B']
    [Module.Projective A B'] (φ : B ≃ₐ[A] B') {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]}
    (hΘ : IsFormsTrace A B Θ) : IsFormsTrace A B' (FormsTrace.transport φ Θ) := by
  intro p b ω
  rw [transport_apply, formsMapEquiv_smul, formsMapEquiv_formsMap, hΘ, ← trace_algEquiv φ,
    AlgEquiv.apply_symm_apply]

/-- **Property (2) of Proposition 0FLC transports** along an isomorphism of algebras. -/
theorem IsWedgeLinear.transport (φ : B ≃ₐ[A] B')
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsWedgeLinear A B Θ) :
    IsWedgeLinear A B' (FormsTrace.transport φ Θ) := by
  intro q p ω η
  rw [transport_apply, transport_apply, formsMapEquiv_wedgeMul, formsMapEquiv_formsMap, hΘ]

/-- **Compatibility with the de Rham differential transports** along an isomorphism of
algebras. -/
theorem CommutesWithD.transport (φ : B ≃ₐ[A] B')
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : CommutesWithD A B Θ) :
    CommutesWithD A B' (FormsTrace.transport φ Θ) := by
  intro p η
  rw [transport_apply, transport_apply, formsMapEquiv_deRhamDifferential, hΘ]

end Stacks.FormsTrace

end
