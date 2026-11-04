module

public import StacksFrontier.RingTheory.Flat.EqualizerTensorExactFibres

/-!
# Exactness on the fibres gives exactness after every base change

Let `p₁ p₂ : C → D` be two maps of flat, finitely presented `A`-algebras such that the equalizer
sequence `0 → κ(𝔭) → κ(𝔭) ⊗_A C → κ(𝔭) ⊗_A D` is exact for every prime `𝔭` of `A`. Then
`0 → A' → A' ⊗_A C → A' ⊗_A D` is exact for every `A`-algebra `A'`: the base changes
`A' ⊗_A C → A' ⊗_A D` are flat and finitely presented over `A'`, and their fibres are field
extensions of fibres of `p₁, p₂`.

## Main results

* `AlgHom.EqualizerTensorExact.of_residueField_of_algebra`: the statement above.
-/

@[expose] public section

open TensorProduct

universe u

namespace AlgHom

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Exactness on the fibres gives exactness after every base change.** For two maps
`p₁ p₂ : C → D` of flat, finitely presented `A`-algebras whose equalizer sequence is exact on
every fibre, the sequence `0 → A' → A' ⊗_A C → A' ⊗_A D` is exact for every `A`-algebra `A'`. -/
theorem EqualizerTensorExact.of_residueField_of_algebra {A C D : Type u} [CommRing A]
    [CommRing C] [CommRing D] [Algebra A C] [Algebra A D] [Module.Flat A C] [Module.Flat A D]
    [Algebra.FinitePresentation A C] [Algebra.FinitePresentation A D] {p₁ p₂ : C →ₐ[A] D}
    (h : ∀ (P : Ideal A) [P.IsPrime], EqualizerTensorExact p₁ p₂ P.ResidueField)
    (A' : Type u) [CommRing A'] [Algebra A A'] :
    EqualizerTensorExact p₁ p₂ A' := by
  let p₁' : A' ⊗[A] C →ₐ[A'] A' ⊗[A] D := Algebra.TensorProduct.map (AlgHom.id A' A') p₁
  let p₂' : A' ⊗[A] C →ₐ[A'] A' ⊗[A] D := Algebra.TensorProduct.map (AlgHom.id A' A') p₂
  have h₁ : (IsScalarTower.toAlgHom A D (A' ⊗[A] D)).comp p₁ =
      (p₁'.restrictScalars A).comp (IsScalarTower.toAlgHom A C (A' ⊗[A] C)) := by
    ext c
    show (1 : A') ⊗ₜ _ = Algebra.TensorProduct.map (AlgHom.id A' A') _ ((1 : A') ⊗ₜ c)
    simp
  have h₂ : (IsScalarTower.toAlgHom A D (A' ⊗[A] D)).comp p₂ =
      (p₂'.restrictScalars A).comp (IsScalarTower.toAlgHom A C (A' ⊗[A] C)) := by
    ext c
    show (1 : A') ⊗ₜ _ = Algebra.TensorProduct.map (AlgHom.id A' A') _ ((1 : A') ⊗ₜ c)
    simp
  refine (equalizerTensorExact_iff_of_isPushout h₁ h₂ A').mp ?_
  refine EqualizerTensorExact.of_residueField fun Q _ => ?_
  refine (equalizerTensorExact_iff_of_isPushout h₁ h₂ Q.ResidueField).mpr ?_
  have : (Q.comap (algebraMap A A')).IsPrime := Ideal.comap_isPrime _ _
  exact EqualizerTensorExact.residueField_of_comap_eq (Q.comap (algebraMap A A')) Q
    (by rw [Algebra.algebraMap_self, Ideal.comap_id]) (h _)

end AlgHom
