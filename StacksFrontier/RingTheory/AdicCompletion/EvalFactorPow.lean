module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The transition maps between the quotients by the powers of an ideal

For an ideal `I` of a ring `R`, the algebra maps `AdicCompletion.evalₐ I n` onto the truncations
`R ⧸ I ^ n` form a compatible family for the transition maps `Ideal.Quotient.factorPow`: this is
the ring-level counterpart of Mathlib's module-level `AdicCompletion.transitionMap_comp_eval`.
`evalₐ_eq_mk` and `val_eq_mk` read an evaluation off a representative and back, and
`Ideal.Quotient.factorPow_comp_quotientMap` is the square relating the transition maps to the
maps induced by a ring homomorphism.
-/

@[expose] public section

namespace Ideal

/-- `(I B) ^ n` and `(I ^ n) B` are the same ideal of `B`, so the two quotients agree. -/
noncomputable def quotientMapPowAlgEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) (n : ℕ) :
    (B ⧸ (I ^ n).map (algebraMap A B)) ≃ₐ[A] (B ⧸ (I.map (algebraMap A B)) ^ n) :=
  Ideal.quotientEquivAlgOfEq A (Ideal.map_pow _ _ _)

/-- `quotientMapPowAlgEquiv` is the identity on residue classes. -/
theorem quotientMapPowAlgEquiv_mk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) (b : B) :
    quotientMapPowAlgEquiv I n (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b := rfl

/-- The inverse of `quotientMapPowAlgEquiv` is the identity on residue classes. -/
theorem quotientMapPowAlgEquiv_symm_mk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) (b : B) :
    (quotientMapPowAlgEquiv I n).symm (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b := rfl

end Ideal

namespace Ideal.Quotient

/-- The maps `Ideal.quotientMap` induced by a ring map `f` on the quotients by the powers of `J`
and of `I` commute with the transition maps `Ideal.Quotient.factorPow`. -/
theorem factorPow_comp_quotientMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) (I : Ideal B) {m n : ℕ} (hmn : m ≤ n)
    (h : J ^ n ≤ (I ^ n).comap f) (h' : J ^ m ≤ (I ^ m).comap f) :
    (Ideal.Quotient.factorPow I hmn).comp (Ideal.quotientMap (I ^ n) f h)
      = (Ideal.quotientMap (I ^ m) f h').comp (Ideal.Quotient.factorPow J hmn) := by
  ext a
  simp

end Ideal.Quotient

namespace AdicCompletion

/-- The residue class of `t` at level `n` computes `AdicCompletion.evalₐ`. -/
theorem evalₐ_eq_mk {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : AdicCompletion I R) (t : R) (ht : x.val n = Submodule.Quotient.mk t) :
    evalₐ I n x = Ideal.Quotient.mk (I ^ n) t := by
  simp [evalₐ, AdicCompletion.eval, ht]

/-- The level-`n` component of `x` is the residue class of `t`, read off the evaluation; this is
`evalₐ_eq_mk` backwards. -/
theorem val_eq_mk {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : AdicCompletion I R) (t : R) (ht : evalₐ I n x = Ideal.Quotient.mk (I ^ n) t) :
    x.val n = Submodule.Quotient.mk t := by
  have h := AdicCompletion.factor_evalₐ_eq_eval I (n := n) x (by simp)
  rw [ht] at h
  exact h.symm

/-- The evaluations `AdicCompletion I R → R ⧸ I ^ n` are compatible with the transition maps
`R ⧸ I ^ n → R ⧸ I ^ m` for `m ≤ n`. -/
theorem factorPow_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← Submodule.neg_mem_iff, neg_sub]
    simpa using SModEq.sub_mem.mp (a.property hmn)

end AdicCompletion
