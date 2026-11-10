module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Algebra.Ring.Aut

/-!
# Twisted translation automorphisms of a polynomial ring

Let `σ` be a ring automorphism of a commutative ring `R`. The *twisted translation* of `R[X]`
by `σ` is the ring automorphism acting on coefficients by `σ` and sending `X` to `X + 1`. It
restricts to `σ` on the constants, so it is a lift of `σ` along `Polynomial.C`, and its `n`-th
power sends `X` to `X + n` and acts on the constants by `σ ^ n`.

Untwisted — that is, for `σ = 1` — this is translation by one on the affine line, and the
twisted form is what acts on the affine line over a field in a way compatible with a
nontrivial automorphism of the field.

## Main definitions

* `Polynomial.translationEquiv` is translation by one, the automorphism of `R[X]` fixing the
  constants and sending `X` to `X + 1`.
* `Polynomial.twistedTranslationEquiv` is its twist by a ring automorphism of `R`.

## Main results

* `Polynomial.twistedTranslationEquiv_comp_C` and
  `Polynomial.twistedTranslationEquiv_zpow_comp_C`: the twisted translation and each of its
  integer powers lift `σ`, resp. `σ ^ n`, along `Polynomial.C`.
* `Polynomial.twistedTranslationEquiv_X` and `Polynomial.twistedTranslationEquiv_zpow_X`: the
  effect on `X` is `X + 1`, resp. `X + n`.
* `Polynomial.twistedTranslationEquiv_eq_eval₂RingHom`: the twisted translation written as an
  evaluation homomorphism.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Translation by one on `R[X]`: the automorphism fixing the constants and sending `X` to
`X + 1`. -/
noncomputable def translationEquiv (R : Type*) [CommRing R] : R[X] ≃+* R[X] :=
  RingEquiv.ofRingHom (eval₂RingHom C (X + C (1 : R))) (eval₂RingHom C (X - C (1 : R)))
    (by
      apply ringHom_ext
      · intro a; simp
      · simp [eval₂_sub])
    (by
      apply ringHom_ext
      · intro a; simp
      · simp [eval₂_add])

/-- Translation by one fixes the constants. -/
@[simp]
theorem translationEquiv_C (a : R) : translationEquiv R (C a) = C a := by
  simp [translationEquiv]

/-- Translation by one sends `X` to `X + 1`. -/
@[simp]
theorem translationEquiv_X : translationEquiv R (X : R[X]) = X + 1 := by
  simp [translationEquiv]

/-- The inverse of translation by one fixes the constants. -/
@[simp]
theorem translationEquiv_symm_C (a : R) : (translationEquiv R).symm (C a) = C a := by
  simp [translationEquiv, RingEquiv.ofRingHom]

/-- The inverse of translation by one sends `X` to `X - 1`. -/
@[simp]
theorem translationEquiv_symm_X : (translationEquiv R).symm (X : R[X]) = X - 1 := by
  simp [translationEquiv, RingEquiv.ofRingHom]

/-- The twisted translation of `R[X]` by a ring automorphism `σ` of `R`: it acts on the
coefficients by `σ` and sends `X` to `X + 1`. -/
noncomputable def twistedTranslationEquiv (σ : R ≃+* R) : R[X] ≃+* R[X] :=
  (mapEquiv σ).trans (translationEquiv R)

/-- The twisted translation by `σ` sends the constant `C a` to `C (σ a)`. -/
@[simp]
theorem twistedTranslationEquiv_C (σ : R ≃+* R) (a : R) :
    twistedTranslationEquiv σ (C a) = C (σ a) := by
  simp [twistedTranslationEquiv]

/-- The twisted translation sends `X` to `X + 1`. -/
@[simp]
theorem twistedTranslationEquiv_X (σ : R ≃+* R) :
    twistedTranslationEquiv σ (X : R[X]) = X + 1 := by
  simp [twistedTranslationEquiv]

/-- The inverse of the twisted translation by `σ` sends the constant `C a` to `C (σ.symm a)`. -/
@[simp]
theorem twistedTranslationEquiv_symm_C (σ : R ≃+* R) (a : R) :
    (twistedTranslationEquiv σ).symm (C a) = C (σ.symm a) := by
  apply (twistedTranslationEquiv σ).injective
  rw [RingEquiv.apply_symm_apply, twistedTranslationEquiv_C, RingEquiv.apply_symm_apply]

/-- The inverse of the twisted translation sends `X` to `X - 1`. -/
@[simp]
theorem twistedTranslationEquiv_symm_X (σ : R ≃+* R) :
    (twistedTranslationEquiv σ).symm (X : R[X]) = X - 1 := by
  simp [twistedTranslationEquiv]

/-- The twisted translation lifts `σ` along `Polynomial.C`. -/
theorem twistedTranslationEquiv_comp_C (σ : R ≃+* R) :
    (twistedTranslationEquiv σ).toRingHom.comp (C : R →+* R[X]) =
      (C : R →+* R[X]).comp σ.toRingHom := by
  ext a
  simp

/-- The twisted translation as an evaluation homomorphism: it is evaluation of the
`σ`-twisted coefficients at `X + 1`. -/
theorem twistedTranslationEquiv_eq_eval₂RingHom (σ : R ≃+* R) :
    (twistedTranslationEquiv σ).toRingHom =
      eval₂RingHom ((C : R →+* R[X]).comp σ.toRingHom) (X + C (1 : R)) := by
  apply ringHom_ext
  · intro a
    change (twistedTranslationEquiv σ) (C a) = _
    simp
  · change (twistedTranslationEquiv σ) X = _
    simp

private theorem ringEquiv_zpow_apply_comm {A : Type*} [CommRing A] (e : A ≃+* A) (n : ℤ)
    (x : A) : e ((e ^ n) x) = (e ^ n) (e x) := by
  have h := congrArg (fun ψ : A ≃+* A => ψ x) ((Commute.refl e).zpow_right n).eq
  simpa using h

/-- If `e` carries the sequence `f` one step forward and `f 0 = x`, then `(e ^ n) x = f n`. -/
private theorem ringEquiv_zpow_apply_of_step {A : Type*} [CommRing A] (e : A ≃+* A) (f : ℤ → A)
    (x : A) (h0 : f 0 = x) (hs : ∀ n, e (f n) = f (n + 1)) (n : ℤ) : (e ^ n) x = f n := by
  induction n using Int.induction_on with
  | zero => simp [h0]
  | succ i ih =>
      rw [add_comm, zpow_add, zpow_one, RingAut.mul_apply, ih, hs, add_comm]
  | pred i ih =>
      rw [sub_eq_neg_add, zpow_add, zpow_neg_one, RingAut.mul_apply, ih, RingAut.inv_apply,
        e.symm_apply_eq, hs]
      congr 1
      ring

/-- The `n`-th power of the twisted translation by `σ` sends the constant `C a` to
`C ((σ ^ n) a)`. -/
theorem twistedTranslationEquiv_zpow_C (σ : R ≃+* R) (n : ℤ) (a : R) :
    (twistedTranslationEquiv σ ^ n) (C a) = C ((σ ^ n) a) :=
  ringEquiv_zpow_apply_of_step _ (fun n => C ((σ ^ n) a)) _ (by simp) (fun n => by
    simp [zpow_add_one, ringEquiv_zpow_apply_comm]) n

/-- Each integer power of the twisted translation lifts the corresponding power of `σ` along
`Polynomial.C`. -/
theorem twistedTranslationEquiv_zpow_comp_C (σ : R ≃+* R) (n : ℤ) :
    (twistedTranslationEquiv σ ^ n).toRingHom.comp (C : R →+* R[X]) =
      (C : R →+* R[X]).comp (σ ^ n).toRingHom :=
  RingHom.ext fun a => twistedTranslationEquiv_zpow_C σ n a

/-- The `n`-th power of the twisted translation sends `X` to `X + n`. -/
theorem twistedTranslationEquiv_zpow_X (σ : R ≃+* R) (n : ℤ) :
    (twistedTranslationEquiv σ ^ n) (X : R[X]) = X + (n : R[X]) :=
  ringEquiv_zpow_apply_of_step _ (fun n => X + (n : R[X])) _ (by simp) (fun n => by
    simp [add_assoc, add_comm]) n

end Polynomial

end
