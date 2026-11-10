module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of a linear form along a pushout of commutative rings

Let

```
R₀ --c--> K
|a        |β
v         v
A  --α--> B
```

be a pushout square of commutative rings, so that `B = A ⊗_{R₀} K`. An `R₀`-linear map
`ℓ : K → R₀` extends `A`-linearly to `id_A ⊗ ℓ : B → A`, characterised by
`α x * β y ↦ x * a (ℓ y)`. This file constructs that extension and shows that it is natural for
morphisms of pushout squares under the same `R₀ → K`.

## Main definitions

* `CommRingCat.pushoutTrace`: the extension `B → A`.

## Main results

* `CommRingCat.pushoutTrace_mul`: it is `A`-linear for the `A`-module structure through `α`.
* `CommRingCat.pushoutTrace_β`: it is `a ∘ ℓ` on the image of `K`.
* `CommRingCat.pushoutTrace_naturality`: it commutes with morphisms of pushout squares.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommRingCat

variable {R₀ A K B : CommRingCat.{u}} {a : R₀ ⟶ A} {c : R₀ ⟶ K} {α : A ⟶ B} {β : K ⟶ B}
  (h : IsPushout c a β α) (ℓ : K →+ R₀) (hℓ : ∀ r y, ℓ (c r * y) = r * ℓ y)

include h in
/-- For the algebra structures given by `c`, `β` and `a ≫ α`, the tower `R₀ → K → B` is a scalar
tower. -/
theorem isScalarTower_K :
    letI : Algebra R₀ K := c.hom.toAlgebra
    letI : Algebra K B := β.hom.toAlgebra
    letI : Algebra R₀ B := (a ≫ α).hom.toAlgebra
    IsScalarTower R₀ K B := by
  let : Algebra R₀ K := c.hom.toAlgebra
  let : Algebra K B := β.hom.toAlgebra
  let : Algebra R₀ B := (a ≫ α).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun r => by
    change (a ≫ α) r = (c ≫ β) r
    rw [h.w])

/-- For the algebra structures given by `a`, `α` and `a ≫ α`, the tower `R₀ → A → B` is a scalar
tower. -/
theorem isScalarTower_A :
    letI : Algebra R₀ A := a.hom.toAlgebra
    letI : Algebra A B := α.hom.toAlgebra
    letI : Algebra R₀ B := (a ≫ α).hom.toAlgebra
    IsScalarTower R₀ A B := by
  let : Algebra R₀ A := a.hom.toAlgebra
  let : Algebra A B := α.hom.toAlgebra
  let : Algebra R₀ B := (a ≫ α).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

include h in
/-- The pushout square as an `Algebra.IsPushout`, for the algebra structures given by its four
ring maps. -/
theorem algebraIsPushout_of_isPushout :
    letI : Algebra R₀ K := c.hom.toAlgebra
    letI : Algebra R₀ A := a.hom.toAlgebra
    letI : Algebra K B := β.hom.toAlgebra
    letI : Algebra A B := α.hom.toAlgebra
    letI : Algebra R₀ B := (a ≫ α).hom.toAlgebra
    haveI := isScalarTower_K h
    haveI := isScalarTower_A (a := a) (α := α)
    Algebra.IsPushout R₀ A K B := by
  let : Algebra R₀ K := c.hom.toAlgebra
  let : Algebra R₀ A := a.hom.toAlgebra
  let : Algebra K B := β.hom.toAlgebra
  let : Algebra A B := α.hom.toAlgebra
  let : Algebra R₀ B := (a ≫ α).hom.toAlgebra
  have := isScalarTower_K h
  have := isScalarTower_A (a := a) (α := α)
  exact (CommRingCat.isPushout_iff_isPushout.mp h).symm

/-- **`id_A ⊗ ℓ : B → A`** for a pushout square `B = A ⊗_{R₀} K` and an `R₀`-linear form
`ℓ : K → R₀`. -/
def pushoutTrace : B →+ A :=
  letI : Algebra R₀ K := c.hom.toAlgebra
  letI : Algebra R₀ A := a.hom.toAlgebra
  letI : Algebra K B := β.hom.toAlgebra
  letI : Algebra A B := α.hom.toAlgebra
  letI : Algebra R₀ B := (a ≫ α).hom.toAlgebra
  haveI := isScalarTower_K h
  haveI := isScalarTower_A (a := a) (α := α)
  ((algebraIsPushout_of_isPushout h).out.lift
    ({ toFun := fun y => a (ℓ y)
       map_add' := fun y y' => by rw [map_add, map_add]
       map_smul' := fun r y => by
        change a (ℓ (c r * y)) = a r * a (ℓ y)
        rw [hℓ, map_mul] } : K →ₗ[R₀] A)).toAddMonoidHom

/-- `pushoutTrace` is `A`-linear for the `A`-module structure of `B` through `α`. -/
theorem pushoutTrace_mul (x : A) (z : B) :
    pushoutTrace h ℓ hℓ (α x * z) = x * pushoutTrace h ℓ hℓ z :=
  let : Algebra R₀ K := c.hom.toAlgebra
  let : Algebra R₀ A := a.hom.toAlgebra
  let : Algebra K B := β.hom.toAlgebra
  let : Algebra A B := α.hom.toAlgebra
  let : Algebra R₀ B := (a ≫ α).hom.toAlgebra
  have := isScalarTower_K h
  have := isScalarTower_A (a := a) (α := α)
  (((algebraIsPushout_of_isPushout h).out.lift
    ({ toFun := fun y => a (ℓ y)
       map_add' := fun y y' => by rw [map_add, map_add]
       map_smul' := fun r y => by
        change a (ℓ (c r * y)) = a r * a (ℓ y)
        rw [hℓ, map_mul] } : K →ₗ[R₀] A))).map_smul x z

/-- `pushoutTrace` is `a ∘ ℓ` on the image of `K`. -/
theorem pushoutTrace_β (y : K) : pushoutTrace h ℓ hℓ (β y) = a (ℓ y) :=
  let : Algebra R₀ K := c.hom.toAlgebra
  let : Algebra R₀ A := a.hom.toAlgebra
  let : Algebra K B := β.hom.toAlgebra
  let : Algebra A B := α.hom.toAlgebra
  let : Algebra R₀ B := (a ≫ α).hom.toAlgebra
  have := isScalarTower_K h
  have := isScalarTower_A (a := a) (α := α)
  IsBaseChange.lift_eq _ _ y

/-- `pushoutTrace` on a product `α x * β y`. -/
theorem pushoutTrace_α_mul_β (x : A) (y : K) :
    pushoutTrace h ℓ hℓ (α x * β y) = x * a (ℓ y) := by
  rw [pushoutTrace_mul, pushoutTrace_β]

/-- **`pushoutTrace` is natural** for a morphism from one pushout square to another under the same
`c : R₀ ⟶ K`. -/
theorem pushoutTrace_naturality {A' B' : CommRingCat.{u}} {a' : R₀ ⟶ A'} {α' : A' ⟶ B'}
    {β' : K ⟶ B'} (h' : IsPushout c a' β' α') (ψ : A ⟶ A') (φ : B ⟶ B')
    (ha : a ≫ ψ = a') (hα : α ≫ φ = ψ ≫ α') (hβ : β ≫ φ = β') (z : B) :
    pushoutTrace h' ℓ hℓ (φ z) = ψ (pushoutTrace h ℓ hℓ z) := by
  let : Algebra R₀ K := c.hom.toAlgebra
  let : Algebra R₀ A := a.hom.toAlgebra
  let : Algebra K B := β.hom.toAlgebra
  let : Algebra A B := α.hom.toAlgebra
  let : Algebra R₀ B := (a ≫ α).hom.toAlgebra
  have := isScalarTower_K h
  have := isScalarTower_A (a := a) (α := α)
  induction z using (algebraIsPushout_of_isPushout h).out.inductionOn with
  | tmul y =>
    change pushoutTrace h' ℓ hℓ (φ (β y)) = ψ (pushoutTrace h ℓ hℓ (β y))
    rw [pushoutTrace_β, ← ConcreteCategory.comp_apply, hβ, pushoutTrace_β,
      ← ConcreteCategory.comp_apply, ha]
  | smul s n ih =>
    change pushoutTrace h' ℓ hℓ (φ (α s * n)) = ψ (pushoutTrace h ℓ hℓ (α s * n))
    rw [map_mul, ← ConcreteCategory.comp_apply, hα, ConcreteCategory.comp_apply,
      pushoutTrace_mul, pushoutTrace_mul, map_mul, ih]
  | add n₁ n₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂, map_add]

end CommRingCat

end
