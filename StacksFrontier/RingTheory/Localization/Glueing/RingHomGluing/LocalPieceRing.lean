module

public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.GlueRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local pieces of the glued datum are rings, and the comparison is multiplicative

The local pieces of the glueing datum of Stacks 0EAE are localizations of the base ring, and so
carry a ring structure. This file gives that ring structure in the spelling the datum uses and
shows that `Stacks.RingHomGluing.genericCompare`, the comparison of a local piece with the
localized glued target, is multiplicative and unital.

## Main definitions

* `Stacks.RingHomGluing.localPieceRing` — the ring structure of a local piece of the canonical
  datum, in the `restrictFromAway` spelling.

## Main results

* `Stacks.RingHomGluing.smul_mul_localizedModule` — the action of the base ring on a localization
  of an algebra is compatible with its multiplication.
* `Stacks.RingHomGluing.localPiece_smul_mul` — the action of the base ring on a local piece is
  compatible with its multiplication.
* `Stacks.RingHomGluing.canonicalLocalMk_mul` and
  `Stacks.RingHomGluing.canonicalLocalMk_one` — the denominator-one map into a local piece is
  multiplicative and unital, packaged as `Stacks.RingHomGluing.localPieceRingHom`.
* `Stacks.RingHomGluing.genericCompare_mul` and `Stacks.RingHomGluing.genericCompare_one` — the
  comparison of a local piece with the localized glued target is multiplicative and unital.

## References

* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public noncomputable section

universe u v w t

namespace Stacks.RingHomGluing

open CategoryTheory Cech TensorProduct FormalGlueing

/-! ### Localizations of a ring, as rings -/

section General

/-- An element acting invertibly on a module acts injectively. -/
theorem injective_smul_of_isUnit {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] (c : R) (h : IsUnit (algebraMap R (Module.End R N) c)) :
    Function.Injective fun z : N ↦ c • z := by
  have hfun : ⇑(algebraMap R (Module.End R N) c) = fun z : N ↦ c • z := by
    ext z
    simp [Algebra.algebraMap_eq_smul_one]
  rw [Module.End.isUnit_iff, hfun] at h
  exact h.1

/-- The action of the base ring on a localization of an algebra is compatible with its
multiplication. -/
theorem smul_mul_localizedModule {R : Type*} [CommRing R] (S : Submonoid R) {M : Type*}
    [CommRing M] [Algebra R M] (c : R) (p p' : LocalizedModule S M) :
    (c • p) * p' = c • (p * p') := by
  induction p using LocalizedModule.induction_on with
  | _ a s =>
    induction p' using LocalizedModule.induction_on with
    | _ b s' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.mk_mul_mk,
        LocalizedModule.smul'_mk, smul_mul_assoc]

/-- Multiplication of two denominator-one fractions. -/
@[ega "0 1.2.2" "partial"]
theorem localizedModule_mk_one_mul {R : Type*} [CommRing R] (S : Submonoid R) {M : Type*}
    [CommRing M] [Algebra R M] (a b : M) :
    LocalizedModule.mk a (1 : S) * LocalizedModule.mk b 1 = LocalizedModule.mk (a * b) 1 := by
  rw [LocalizedModule.mk_mul_mk, mul_one]

/-- The denominator-one fraction on `1`. -/
@[ega "0 1.2.2" "i_A^S preserves 1"]
theorem localizedModule_mk_one_one {R : Type*} [CommRing R] (S : Submonoid R) {M : Type*}
    [CommRing M] [Algebra R M] :
    LocalizedModule.mk (1 : M) (1 : S) = 1 :=
  OreLocalization.one_def.symm

end General

/-! ### The ring structure of a local piece -/

section LocalPiece

variable {A : Type u} [CommRing A] {r : ℕ} (x : Fin r → A)

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The action of the base ring through the away localization is compatible with the
multiplication. -/
theorem algebraMap_smul_mul_localizedModule (j : Fin r) (c : A)
    (p p' : LocalizedModule.Away (x j) (ULift.{t} A)) :
    (algebraMap A (Localization.Away (x j)) c • p) * p' =
      algebraMap A (Localization.Away (x j)) c • (p * p') := by
  rw [IsScalarTower.algebraMap_smul (Localization.Away (x j)) c p,
    IsScalarTower.algebraMap_smul (Localization.Away (x j)) c (p * p')]
  exact smul_mul_localizedModule (Submonoid.powers (x j)) c p p'

/-- The ring structure of the `j`-th local piece of the canonical datum, in the spelling the
datum uses. -/
@[instance_reducible] def localPieceRing (j : Fin r) :
    CommRing (restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, t} A) j)) :=
  inferInstanceAs (CommRing (LocalizedModule.Away (x j) (ULift.{t} A)))

attribute [local instance] localPieceRing

/-- The action of the base ring on a local piece is compatible with its multiplication. -/
theorem localPiece_smul_mul (j : Fin r) (c : A)
    (p p' : restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, t} A) j)) :
    (c • p) * p' = c • (p * p') :=
  algebraMap_smul_mul_localizedModule x j c p p'

/-- The denominator-one map into a local piece is multiplicative. -/
theorem canonicalLocalMk_mul (j : Fin r) (a b : ULift.{t} A) :
    canonicalLocalMk x (liftedBase.{u, t} A) j (a * b) =
      canonicalLocalMk x (liftedBase.{u, t} A) j a *
        canonicalLocalMk x (liftedBase.{u, t} A) j b :=
  (localizedModule_mk_one_mul (Submonoid.powers (x j)) a b).symm

/-- The denominator-one map into a local piece is unital. -/
theorem canonicalLocalMk_one (j : Fin r) :
    canonicalLocalMk x (liftedBase.{u, t} A) j 1 = 1 :=
  localizedModule_mk_one_one (Submonoid.powers (x j))

/-- The denominator-one map of the base ring into the `j`-th local piece, as a ring map. -/
def localPieceRingHom (j : Fin r) :
    A →+* restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, t} A) j) where
  toFun a := canonicalLocalMk x (liftedBase.{u, t} A) j (ULift.up a)
  map_one' := canonicalLocalMk_one x j
  map_mul' a b := canonicalLocalMk_mul x j (ULift.up a) (ULift.up b)
  map_zero' := map_zero _
  map_add' _ _ := map_add (canonicalLocalMk x (liftedBase.{u, t} A) j) _ _

/-- The ring map of the base ring into a local piece, evaluated. -/
theorem localPieceRingHom_apply (j : Fin r) (a : A) :
    localPieceRingHom x j a = canonicalLocalMk x (liftedBase.{u, t} A) j (ULift.up a) := rfl

end LocalPiece

/-! ### The comparison with the localized glued target is a ring map -/

section Compare

variable {A : Type u} [CommRing A] {I : Type w} [Finite I] (m : I → Ideal A)
  [∀ i, (m i).IsMaximal]
  {T : Type max u v w} [CommRing T] [Algebra (∀ i, Localization.AtPrime (m i)) T]
  {r : ℕ} (x : Fin r → A)

attribute [local instance] localPieceRing

omit [Finite I] in
/-- The comparison carries the action of a power of `x j` to the action of the image of that
power. -/
theorem genericCompare_pow_smul (j : Fin r) (k : ℕ)
    (y : restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) :
    algebraMap A (∀ i, Localization.AtPrime (m i)) (x j) ^ k •
        genericCompare.{u, v, w} m x (T := T) j y =
      genericCompare.{u, v, w} m x (T := T) j ((x j ^ k : A) • y) := by
  rw [genericCompare_smul, map_pow]

omit [Finite I] in
/-- **The comparison is multiplicative.** -/
theorem genericCompare_mul (j : Fin r)
    (y y' : restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) :
    genericCompare.{u, v, w} m x (T := T) j (y * y') =
      genericCompare.{u, v, w} m x (T := T) j y * genericCompare.{u, v, w} m x (T := T) j y' := by
  have hloc := canonicalLocalMk_isLocalized x (liftedBase.{u, max v w} A) j
  obtain ⟨⟨a, s⟩, hsy : (s : A) • y = canonicalLocalMk x (liftedBase.{u, max v w} A) j a⟩ :=
    IsLocalizedModule.surj (Submonoid.powers (x j)) (canonicalLocalMk x (liftedBase A) j) y
  obtain ⟨⟨b, s'⟩, hsy' : (s' : A) • y' = canonicalLocalMk x (liftedBase.{u, max v w} A) j b⟩ :=
    IsLocalizedModule.surj (Submonoid.powers (x j)) (canonicalLocalMk x (liftedBase A) j) y'
  obtain ⟨k, hk : x j ^ k = (s : A)⟩ := s.2
  obtain ⟨k', hk' : x j ^ k' = (s' : A)⟩ := s'.2
  refine injective_pow_smul_localizedModule.{u, v, w} m x j (k + k') ?_
  have hprod : (x j ^ (k + k') : A) • (y * y') =
      canonicalLocalMk x (liftedBase.{u, max v w} A) j (a * b) := by
    rw [pow_add, ← smul_mul_smul_of_smul_mul (localPiece_smul_mul x j), hk, hk', hsy, hsy',
      canonicalLocalMk_mul]
  have key : ∀ (n : ℕ) (z : restrictFromAway (R := A) x j
        (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) (c : ULift.{max v w} A),
      (x j ^ n : A) • z = canonicalLocalMk x (liftedBase.{u, max v w} A) j c →
      algebraMap A (∀ i, Localization.AtPrime (m i)) (x j) ^ n •
          genericCompare.{u, v, w} m x (T := T) j z =
        LocalizedModule.mk (algebraMap (∀ i, Localization.AtPrime (m i)) T
          (algebraMap A (∀ i, Localization.AtPrime (m i)) c.down)) 1 := fun n z c h ↦ by
    rw [genericCompare_pow_smul, h, genericCompare_mk]
  have hL := key (k + k') _ _ hprod
  have hRa := key k y a (hk ▸ hsy)
  have hRb := key k' y' b (hk' ▸ hsy')
  beta_reduce
  rw [hL, pow_add, ← smul_mul_smul_of_smul_mul smul_mul_assoc _ _ _ _,
    hRa, hRb, LocalizedModule.mk_mul_mk, mul_one, ULift.mul_down, map_mul, map_mul]

omit [Finite I] in
/-- The comparison is unital. -/
theorem genericCompare_one (j : Fin r) :
    genericCompare.{u, v, w} m x (T := T) j 1 = 1 := by
  rw [← canonicalLocalMk_one x j, genericCompare_mk]
  show LocalizedModule.mk (algebraMap (∀ i, Localization.AtPrime (m i)) T
    (algebraMap A (∀ i, Localization.AtPrime (m i)) (1 : A))) 1 = 1
  rw [map_one, map_one, OreLocalization.one_def]

end Compare

end Stacks.RingHomGluing

end
