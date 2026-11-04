module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import StacksCore.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Additivity

/-!
# The multiplicity of a product of two two-periodic complexes

Two pairs of mutually annihilating endomorphisms assemble into one such pair on the product
module, and the multiplicity of the resulting two-periodic complex is the sum of the two
multiplicities. The inclusion of the first factor and the projection to the second form a short
exact sequence of two-periodic complexes, so this is additivity of the multiplicity on a short
exact sequence.

## Main results

* `AlgebraicGeometry.prodMap_mul_prodMap_eq_zero`: if `φ₁ ψ₁ = 0` and `φ₂ ψ₂ = 0`, then
  `(φ₁ × φ₂)(ψ₁ × ψ₂) = 0`.
* `AlgebraicGeometry.periodicLength_prodMap`: the multiplicity of the product complex is the sum
  of the two multiplicities.

## Implementation notes

The two morphisms of complexes are built with
`AlgebraicGeometry.twoPeriodicComplexMap` from `LinearMap.inl` and `LinearMap.snd`, which
intertwine the differentials because the differential on the product is `LinearMap.prodMap` of
the two. Short exactness is checked degree by degree, using that a morphism of complexes over an
abelian category is a monomorphism, respectively an epimorphism, exactly when every component is,
and that in `ModuleCat` exactness of a short complex is exactness of the underlying maps.

## References

* [Stacks Project, Tag 0EA7](https://stacks.math.columbia.edu/tag/0EA7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable {R : Type u} [Ring R] {M₁ M₂ : Type v}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- If `φ₁ ψ₁ = 0` and `φ₂ ψ₂ = 0`, then `(φ₁ × φ₂)(ψ₁ × ψ₂) = 0` on `M₁ × M₂`. -/
theorem prodMap_mul_prodMap_eq_zero (φ₁ ψ₁ : Module.End R M₁) (h₁ : φ₁ * ψ₁ = 0)
    (φ₂ ψ₂ : Module.End R M₂) (h₂ : φ₂ * ψ₂ = 0) :
    LinearMap.prodMap φ₁ φ₂ * LinearMap.prodMap ψ₁ ψ₂ = 0 := by
  have e₁ : ∀ m, φ₁ (ψ₁ m) = 0 := fun m ↦ LinearMap.congr_fun h₁ m
  have e₂ : ∀ m, φ₂ (ψ₂ m) = 0 := fun m ↦ LinearMap.congr_fun h₂ m
  ext z <;> simp [e₁, e₂]

/-- The multiplicity of the two-periodic complex on a product module with the product
differentials is the sum of the multiplicities of the two factors. -/
theorem periodicLength_prodMap
    (φ₁ ψ₁ : Module.End R M₁) (h₁ : φ₁ * ψ₁ = 0) (h₁' : ψ₁ * φ₁ = 0)
    (φ₂ ψ₂ : Module.End R M₂) (h₂ : φ₂ * ψ₂ = 0) (h₂' : ψ₂ * φ₂ = 0)
    (hφψ : LinearMap.prodMap φ₁ φ₂ * LinearMap.prodMap ψ₁ ψ₂ = 0)
    (hψφ : LinearMap.prodMap ψ₁ ψ₂ * LinearMap.prodMap φ₁ φ₂ = 0)
    (hfin₁ : HasFiniteLengthHomology (twoPeriodicComplex φ₁ ψ₁ h₁ h₁'))
    (hfin₂ : HasFiniteLengthHomology (twoPeriodicComplex φ₂ ψ₂ h₂ h₂')) :
    periodicLength (twoPeriodicComplex (LinearMap.prodMap φ₁ φ₂) (LinearMap.prodMap ψ₁ ψ₂)
        hφψ hψφ) =
      periodicLength (twoPeriodicComplex φ₁ ψ₁ h₁ h₁') +
        periodicLength (twoPeriodicComplex φ₂ ψ₂ h₂ h₂') := by
  have hinl : ∀ (a : Module.End R M₁) (b : Module.End R M₂),
      (LinearMap.inl R M₁ M₂) ∘ₗ a = LinearMap.prodMap a b ∘ₗ LinearMap.inl R M₁ M₂ := by
    intros
    ext m <;> simp
  have hsnd : ∀ (a : Module.End R M₁) (b : Module.End R M₂),
      (LinearMap.snd R M₁ M₂) ∘ₗ LinearMap.prodMap a b = b ∘ₗ LinearMap.snd R M₁ M₂ := by
    intros
    ext z <;> simp
  set Fi := twoPeriodicComplexMap φ₁ ψ₁ h₁ h₁' (LinearMap.prodMap φ₁ φ₂)
    (LinearMap.prodMap ψ₁ ψ₂) hφψ hψφ (LinearMap.inl R M₁ M₂) (hinl _ _) (hinl _ _) with hFi
  set Fs := twoPeriodicComplexMap (LinearMap.prodMap φ₁ φ₂) (LinearMap.prodMap ψ₁ ψ₂) hφψ hψφ
    φ₂ ψ₂ h₂ h₂' (LinearMap.snd R M₁ M₂) (hsnd _ _) (hsnd _ _) with hFs
  have hzero : Fi ≫ Fs = 0 := by
    ext
    rfl
  let S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))) :=
    ShortComplex.mk Fi Fs hzero
  have hmono : Mono S.f := by
    rw [HomologicalComplex.mono_iff_degreewise_mono]
    intro i
    show Mono (ModuleCat.ofHom (LinearMap.inl R M₁ M₂))
    exact ConcreteCategory.mono_of_injective (ModuleCat.ofHom (LinearMap.inl R M₁ M₂))
      (LinearMap.inl_injective (R := R) (M := M₁) (M₂ := M₂))
  have hepi : Epi S.g := by
    rw [HomologicalComplex.epi_iff_degreewise_epi]
    intro i
    show Epi (ModuleCat.ofHom (LinearMap.snd R M₁ M₂))
    exact ConcreteCategory.epi_of_surjective (ModuleCat.ofHom (LinearMap.snd R M₁ M₂))
      (LinearMap.snd_surjective (R := R) (M := M₁) (M₂ := M₂))
  have hexact : S.Exact := by
    rw [HomologicalComplex.exact_iff_degreewise_exact]
    intro i
    refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up (ZMod 2)) i))).mpr ?_
    show Function.Exact (LinearMap.inl R M₁ M₂) (LinearMap.snd R M₁ M₂)
    exact Function.Exact.inl_snd
  exact periodicLength_additive_of_shortExact S
    (ShortComplex.ShortExact.mk' hexact hmono hepi) (Or.inr (Or.inl ⟨hfin₁, hfin₂⟩))

end AlgebraicGeometry

end
