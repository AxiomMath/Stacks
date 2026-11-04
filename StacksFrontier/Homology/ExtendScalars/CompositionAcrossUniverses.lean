module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Extension of scalars in two steps, for rings in different universes

Let `ρ : R ⟶ A` and `η : A ⟶ T` be homomorphisms of commutative rings.  Extending the scalars of
an `R`-module first along `ρ` and then along `η` gives the same `T`-module as extending them in
one step along `η ∘ ρ`, because `T ⊗_A (A ⊗_R M) = T ⊗_R M`.

`ModuleCat.extendScalarsComp` is this statement as an isomorphism of functors, but only for
three rings in one and the same universe, with the module universe forced to be that universe as
well.  This file proves the object-level statement for `R` in an arbitrary universe, `A` in a
second one and `T` in a third containing the second.

## Main definitions

* `ModuleCat.extendScalarsCompObjIso`: the two-step base change of a module, for rings in
  different universes.

## Implementation notes

The hypothesis that the universe of `T` contains the universe of `A` cannot be stated as an
inequality, and is imposed instead by writing that universe as a maximum: `A : Type u₂` and
`T : Type (max u₂ u₃)`.  Without it the two sides do not live in the same category.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u₃ w

namespace ModuleCat

variable {R : Type u₁} {A : Type u₂} {T : Type (max u₂ u₃)}
  [CommRing R] [CommRing A] [CommRing T]

/-- **Extension of scalars in two steps**, for a module over `R`, an intermediate ring `A` and a
target ring `T` whose universe contains that of `A`: extending scalars along `ρ : R ⟶ A` and then
along `η : A ⟶ T` is extending them along `η ∘ ρ`, since `T ⊗_A (A ⊗_R M) = T ⊗_R M`. -/
def extendScalarsCompObjIso (ρ : R →+* A) (η : A →+* T) (M : ModuleCat.{w} R) :
    (extendScalars η).obj ((extendScalars ρ).obj M) ≅ (extendScalars (η.comp ρ)).obj M := by
  letI : Algebra R A := ρ.toAlgebra
  letI : Algebra A T := η.toAlgebra
  letI : Algebra R T := (η.comp ρ).toAlgebra
  have : IsScalarTower R A T := ⟨fun r a t => by
    change η (ρ r * a) * t = η (ρ r) * (η a * t)
    rw [map_mul, mul_assoc]⟩
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R A T T M).toModuleIso

end ModuleCat

end
