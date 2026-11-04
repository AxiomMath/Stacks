module

public import Mathlib.RingTheory.Etale.Weakly

@[expose] public section

-- Required by the `ULift` transport steps in `MulFlat.ulift_iff` and
-- `MulFlat.trans`: without it the rewrites there fail on the `ULift.algebra'`
-- instance, which is only reducibly equal to the one inferred.
set_option backward.isDefEq.respectTransparency false

universe u₁ u₂ u₃

/-!
# Base change and composition of weakly étale ring maps

For a commutative `R`-algebra `S`, `Algebra.MulFlat R S` is flatness of the multiplication map
`S ⊗[R] S → S`, the second of the two conditions defining a weakly étale ring map
(`Algebra.WeaklyEtale`). This file shows that flatness of the multiplication map, and weak
étaleness, are stable under base change and under composition.

## Main definitions

* `Algebra.MulFlat`: flatness of the multiplication map `S ⊗[R] S → S`.

## Main results

* `mulFlat_baseChange`: if the multiplication map of `A → B` is flat, so is that of
  `A' → A' ⊗[A] B`.
* `weaklyEtale_baseChange`: if `A → B` is weakly étale, so is `A' → A' ⊗[A] B`.
* `mulFlat_comp`: if the multiplication maps of `A → B` and `B → C` are flat, so is that of
  `A → C`.
* `weaklyEtale_comp`: if `A → B` and `B → C` are weakly étale, so is `A → C`.

## Implementation notes

The base change of `B` along `A → A'` is taken to be `A' ⊗[A] B`, with the base ring on the
left, the form for which Mathlib provides the algebra instances. A composite `A → B → C` is
expressed by `Algebra A B`, `Algebra B C`, `Algebra A C` and `IsScalarTower A B C`.

## References

* [Stacks Project, Tag 092H](https://stacks.math.columbia.edu/tag/092H)
* [Stacks Project, Tag 092J](https://stacks.math.columbia.edu/tag/092J)
-/

open scoped TensorProduct

namespace Algebra

/-- Flatness of the multiplication map (codiagonal) `μ_{S/R} : S ⊗[R] S → S`, i.e.
flatness of `S` as a module over `S ⊗[R] S` via `s₁ ⊗ s₂ ↦ s₁ s₂`. This is the
second of the two conditions defining a weakly étale ring map, the field
`Algebra.WeaklyEtale.flat_lmul'` of `Algebra.WeaklyEtale`. -/
abbrev MulFlat (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  (Algebra.TensorProduct.lmul' R (S := S)).Flat

/-- If the multiplication map `μ_{B/A} : B ⊗[A] B → B` is flat, then so is the
multiplication map `μ_{B'/A'} : B' ⊗[A'] B' → B'` of the base change
`B' = A' ⊗[A] B`. -/
theorem MulFlat.baseChange {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (h : MulFlat A B) : MulFlat A' (A' ⊗[A] B) := by
  let e : (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) ≃ₐ[A'] A' ⊗[A] (B ⊗[A] B) :=
    (Algebra.TensorProduct.cancelBaseChange A A' A' _ _).trans (Algebra.TensorProduct.assoc ..)
  have heq : Algebra.TensorProduct.lmul' A' (S := A' ⊗[A] B) =
      (Algebra.TensorProduct.map (.id A' A')
        (Algebra.TensorProduct.lmul' A (S := B))).comp e.toAlgHom := by
    ext <;> simp [e, Algebra.TensorProduct.one_def]
  show (Algebra.TensorProduct.lmul' A' (S := A' ⊗[A] B)).Flat
  rw [heq]
  exact .comp (.of_bijective e.bijective)
    (.tensorProductMap (.of_bijective Function.bijective_id) h)

attribute [local instance] ULift.algebra' in
/-- `MulFlat` is invariant under `ULift`ing both rings. `MulFlat.trans` uses it to reduce to
a single universe, in which `RingHom.Flat.mapOfCompatibleSMul` is stated. -/
theorem MulFlat.ulift_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    MulFlat (ULift.{u₁} R) (ULift.{u₂} S) ↔ MulFlat R S := by
  show (Algebra.TensorProduct.lmul' (ULift.{u₁} R) (S := ULift.{u₂} S)).Flat ↔
    (Algebra.TensorProduct.lmul' R (S := S)).Flat
  conv_rhs => rw [← RingHom.Flat.ulift_iff.{u₁, u₂}]
  rw [Algebra.TensorProduct.lmul'_ulift, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  exact RingHom.Flat.comp_iff_of_bijective_right (Equiv.bijective _)

attribute [local instance] Algebra.TensorProduct.rightAlgebra ULift.algebra' in
/-- If the multiplication maps `μ_{B/A}` and `μ_{C/B}` are both flat, then the
multiplication map `μ_{C/A}` of the composite `A → C` is flat. -/
theorem MulFlat.trans (A : Type u₁) (B : Type u₂) (C : Type u₃) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : MulFlat A B) (hBC : MulFlat B C) : MulFlat A C := by
  rw [← MulFlat.ulift_iff.{max u₁ u₂ u₃, max u₁ u₂ u₃}] at hAB hBC ⊢
  show (Algebra.TensorProduct.lmul' (ULift.{max u₁ u₂ u₃} A)
    (S := ULift.{max u₁ u₂ u₃} C)).Flat
  have heq : Algebra.TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} C)
        (ULift.{max u₁ u₂ u₃} A) =
      AlgHom.comp ((Algebra.TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} C)
        (ULift.{max u₁ u₂ u₃} B)).restrictScalars (ULift.{max u₁ u₂ u₃} A))
        (Algebra.TensorProduct.mapOfCompatibleSMul ..) := by
    ext <;> simp
  rw [heq]
  exact .comp (hAB.mapOfCompatibleSMul (ULift.{max u₁ u₂ u₃} C) (ULift.{max u₁ u₂ u₃} C)) hBC

end Algebra

/-- If the multiplication map `μ_{B/A} : B ⊗[A] B → B` is flat, then the multiplication map
`μ_{B'/A'} : B' ⊗[A'] B' → B'` of the base change `B' = A' ⊗[A] B` is flat.

Under the canonical `A'`-algebra isomorphism
`e : (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) ≃ₐ[A'] A' ⊗[A] (B ⊗[A] B)` one has
`μ_{B'/A'} = (id_{A'} ⊗ μ_{B/A}) ∘ e`, and `id_{A'} ⊗ μ_{B/A}` is flat by
`RingHom.Flat.tensorProductMap`. -/
@[stacks 092H "(1)"]
theorem mulFlat_baseChange (A : Type u₁) (B : Type u₂) (A' : Type u₃)
    [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A']
    (h : Algebra.MulFlat A B) :
    Algebra.MulFlat A' (A' ⊗[A] B) := by
  exact Algebra.MulFlat.baseChange h

/-- If `A → B` is weakly étale, then `A' → B'` is weakly étale, where `B' = A' ⊗[A] B` is the
base change. This is Mathlib's base-change instance for `Algebra.WeaklyEtale`. -/
@[stacks 092H "(2)"]
theorem weaklyEtale_baseChange (A : Type u₁) (B : Type u₂) (A' : Type u₃)
    [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A']
    (h : Algebra.WeaklyEtale A B) :
    Algebra.WeaklyEtale A' (A' ⊗[A] B) :=
  have := h
  inferInstance

/-- If the multiplication maps `μ_{B/A}` and `μ_{C/B}` are both flat, then the multiplication
map `μ_{C/A}` is flat.

After reducing to a single universe with `Algebra.MulFlat.ulift_iff`, this is the
factorisation `μ_{C/A} = μ_{C/B} ∘ (C ⊗_A C → C ⊗_B C)` together with
`RingHom.Flat.mapOfCompatibleSMul` and `RingHom.Flat.comp`. -/
@[stacks 092J "(1)"]
theorem mulFlat_comp (A : Type u₁) (B : Type u₂) (C : Type u₃) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.MulFlat A B) (hBC : Algebra.MulFlat B C) : Algebra.MulFlat A C := by
  exact Algebra.MulFlat.trans A B C hAB hBC

/-- If `A → B` and `B → C` are both weakly étale, then the composite `A → C` is weakly étale.
This is Mathlib's `Algebra.WeaklyEtale.trans`. -/
@[stacks 092J "(2)"]
theorem weaklyEtale_comp (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.WeaklyEtale A B) (hBC : Algebra.WeaklyEtale B C) :
    Algebra.WeaklyEtale A C :=
  have := hAB
  have := hBC
  Algebra.WeaklyEtale.trans A B C
