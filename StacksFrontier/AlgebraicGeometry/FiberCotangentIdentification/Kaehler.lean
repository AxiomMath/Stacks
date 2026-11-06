module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Kähler differentials over a pushout square, after a further extension of scalars

Let `A → A'` and `A → B` be ring maps and let `B'` complete them to a pushout square, so that
`B'` is the base change `B ⊗[A] A'`.  For any `B'`-algebra `κ`, **the two relative cotangent
spaces agree**:

```
κ ⊗[B] Ω[B⁄A]  ≃  κ ⊗[B'] Ω[B'⁄A']
```

compatibly with universal differentials.

## Main definitions

* `Stacks.FiberCotangentIdentification.kaehlerTensorEquivOfIsPushout`: the identification above.

## Main results

* `Stacks.FiberCotangentIdentification.isPushout_quotient`: for an ideal `I` of `A`, the square of
  `A → A ⧸ I`, `A → B` and the two quotient maps is a pushout, that is, `B ⧸ IB` is the base
  change `B ⊗[A] A ⧸ I`.
* `Stacks.FiberCotangentIdentification.kaehlerTensorEquivOfIsPushout_tmul_D`: the identification
  carries `1 ⊗ d b` to `1 ⊗ d` of the image of `b` in `B'`.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.FiberCotangentIdentification

/-- **A quotient square is a pushout square.**  For an `A`-algebra `B` and an ideal `I` of `A`,
the square formed by `A → A ⧸ I`, `A → B` and the two quotient maps is a pushout: `B ⧸ IB` is the
base change `B ⊗[A] A ⧸ I`. -/
public theorem isPushout_quotient {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) : Algebra.IsPushout A (A ⧸ I) B (B ⧸ I.map (algebraMap A B)) := by
  refine Algebra.IsPushout.symm ⟨IsBaseChange.of_equiv (Ideal.quotMapEquivTensorQuot B).symm ?_⟩
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [LinearEquiv.symm_apply_eq]
  simp [Ideal.quotMapEquivTensorQuot, LinearEquiv.eq_symm_apply, Algebra.smul_def]

variable (A B A' B' κ : Type*) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing κ]
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A A' B B']
  [Algebra B' κ] [Algebra B κ] [IsScalarTower B B' κ]

/-- **The relative cotangent space of a pushout square does not depend on which side it is
computed on.**  For a pushout square of `A → A'`, `A → B` and `B`, `A' → B'`, and any
`B'`-algebra `κ`,

```
κ ⊗[B] Ω[B⁄A] ≃ κ ⊗[B'] Ω[B'⁄A'].
```
-/
public noncomputable def kaehlerTensorEquivOfIsPushout :
    κ ⊗[B] (KaehlerDifferential A B) ≃ₗ[κ] κ ⊗[B'] (KaehlerDifferential A' B') :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' κ κ
      (KaehlerDifferential A B)).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ)
      (KaehlerDifferential.tensorKaehlerEquiv A A' B B'))

/-- **The identification carries universal differentials to universal differentials**: `1 ⊗ d b`
goes to `1 ⊗ d` of the image of `b` in `B'`. -/
public theorem kaehlerTensorEquivOfIsPushout_tmul_D (b : B) :
    kaehlerTensorEquivOfIsPushout A B A' B' κ
        ((1 : κ) ⊗ₜ[B] KaehlerDifferential.D A B b) =
      (1 : κ) ⊗ₜ[B'] KaehlerDifferential.D A' B' (algebraMap B B' b) := by
  have hc : TensorProduct.AlgebraTensorModule.cancelBaseChange B B' κ κ
      (KaehlerDifferential A B) ((1 : κ) ⊗ₜ[B'] ((1 : B') ⊗ₜ[B]
        KaehlerDifferential.D A B b)) = (1 : κ) ⊗ₜ[B] KaehlerDifferential.D A B b := by
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp
  rw [kaehlerTensorEquivOfIsPushout, LinearEquiv.trans_apply, ← hc,
    LinearEquiv.symm_apply_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]

end Stacks.FiberCotangentIdentification

end
