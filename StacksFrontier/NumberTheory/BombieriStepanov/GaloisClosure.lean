module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsSepClosed

/-!
# A finite Galois closure of a finite separable extension

The normal closure of a finite separable extension `K/F₀` inside a separable closure of `F₀` is a
finite Galois extension of `F₀` containing `K`.

## Main results

* `Stacks.BombieriStepanov.exists_galoisClosure`
-/

@[expose] public noncomputable section

universe u

namespace Stacks.BombieriStepanov

/-- A finite separable extension has a finite Galois closure. -/
theorem exists_galoisClosure (F₀ K : Type u) [Field F₀] [Field K] [Algebra F₀ K]
    [FiniteDimensional F₀ K] [Algebra.IsSeparable F₀ K] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F₀ L) (_ : Algebra K L)
      (_ : IsScalarTower F₀ K L) (_ : IsGalois F₀ L), FiniteDimensional F₀ L := by
  let ε : K →ₐ[F₀] SeparableClosure F₀ := IsSepClosed.lift
  let : Algebra K (SeparableClosure F₀) := (ε : K →+* SeparableClosure F₀).toAlgebra
  have : IsScalarTower F₀ K (SeparableClosure F₀) :=
    IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  have h1 : IsScalarTower F₀ K (IntermediateField.normalClosure F₀ K (SeparableClosure F₀)) :=
    inferInstance
  exact ⟨_, inferInstance, inferInstance, inferInstance, h1,
    IsGalois.normalClosure F₀ K (SeparableClosure F₀),
    normalClosure.is_finiteDimensional F₀ K (SeparableClosure F₀)⟩

end Stacks.BombieriStepanov

end
