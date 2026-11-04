module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Finitely generated modules -/

@[expose] public section

add_to_stacks 0560 Module.Finite.of_restrictScalars_finite
add_to_stacks 00GL RingHom.Finite.comp

@[stacks 00GJ]
theorem Module.Finite.iff_scalarTower {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R S] [Module R M] [Module S M] [Module.Finite R S] [IsScalarTower R S M] :
    Module.Finite R M ↔ Module.Finite S M :=
  ⟨fun _ ↦ of_restrictScalars_finite R S M, fun _ ↦ trans S M⟩

/-- Replaced bogus `CommSemiring B₁` assumption with `Semiring B₁`. -/
theorem Module.Finite.of_equiv_equiv' {A₁ B₁ A₂ B₂ : Type*}
    [CommSemiring A₁] [Semiring B₁] [CommSemiring A₂] [Semiring B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp e₁ = .comp e₂ (algebraMap A₁ B₁))
    [Module.Finite A₁ B₁] : Module.Finite A₂ B₂ := by
  algebraize [e₁.toRingHom]
  let : Algebra A₁ B₂ := .compHom B₂ (algebraMap A₁ A₂)
  have : IsScalarTower A₁ A₂ B₂ := .of_algebraMap_eq fun x ↦ rfl
  have h (a₁) : algebraMap A₂ B₂ (e₁ a₁) = algebraMap A₁ B₂ a₁ := rfl
  let e₂' : B₁ ≃ₗ[A₁] B₂ :=
  { __ := e₂
    map_smul' a₁ b₁ := by simpa [Algebra.smul_def, h] using congr($he.symm a₁ * _) }
  have : Module.Finite A₁ B₂ := .equiv e₂'
  exact .of_restrictScalars_finite A₁ A₂ B₂

/-- Finiteness transfers across a pair of commuting ring isomorphisms `e₁ : A₁ ≃+* A₂` and
`e₂ : B₁ ≃+* B₂`: `B₁` is finite over `A₁` iff `B₂` is finite over `A₂`. -/
theorem Module.finite_iff_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*}
    [CommSemiring A₁] [Semiring B₁] [CommSemiring A₂] [Semiring B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp e₁ = .comp e₂ (algebraMap A₁ B₁)) :
    Module.Finite A₁ B₁ ↔ Module.Finite A₂ B₂ :=
  have he' (x) : algebraMap A₂ B₂ (e₁ x) = e₂ (algebraMap A₁ B₁ x) := congr($he x)
  ⟨fun _ ↦ .of_equiv_equiv' e₁ e₂ he, fun _ ↦ .of_equiv_equiv' e₁.symm e₂.symm <| by
    simp [RingHom.ext_iff, e₁.surjective.forall, he']⟩

theorem Module.finite_of_matrix {R M : Type*} (m n : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [Nonempty m] [Nonempty n] [Module.Finite R (Matrix m n M)] :
    Module.Finite R M := by
  obtain ⟨i⟩ := ‹Nonempty m›
  obtain ⟨j⟩ := ‹Nonempty n›
  exact .of_surjective (Matrix.entryLinearMap (R := R) (α := M) i j)
    fun x => ⟨.of fun _ _ => x, rfl⟩
