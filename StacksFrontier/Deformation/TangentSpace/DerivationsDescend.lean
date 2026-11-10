module

public import StacksFrontier.Deformation.TangentSpace.SquareZero

/-!
# Derivations that kill the maximal ideal come from the residue field

Let `R` be a Noetherian complete local `Λ`-algebra with residue field identified with `k`,
and let `D : R → k` be a `Λ`-derivation, where `R` acts on `k` through the augmentation
`q : R → k`. If `D` vanishes on the maximal ideal of `R`, then `D` is `δ ∘ q` for a
`Λ`-derivation `δ` of `k`.

## Main results

* `Deformation.exists_residueDerivation_of_eq_zero_on_maximalIdeal`: a `Λ`-derivation of `R`
  into `k` vanishing on `m_R` factors through the augmentation.
-/

@[expose] public section

open IsLocalRing

namespace Deformation

section

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A `Λ`-derivation of a Noetherian complete local `Λ`-algebra `R` into its residue field
`k` which vanishes on the maximal ideal of `R` is the composite of the augmentation
`R → k` with a `Λ`-derivation of `k`. -/
public theorem exists_residueDerivation_of_eq_zero_on_maximalIdeal
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (D : Derivations R k)
    (hD : ∀ r : R, r ∈ maximalIdeal R → D r = 0) :
    ∃ δ : Derivation Λ k k, ∀ r : R, D r = δ (residueHom R r) := by
  classical
  let : Module R k := Module.compHom k (residueHom R).toRingHom
  have ⟨hadd, hone, hleib, hscal⟩ : (∀ a b : R, D (a + b) = D a + D b) ∧ D 1 = 0 ∧
      (∀ x y : R, D (x * y) = residueHom R x * D y + residueHom R y * D x) ∧
      ∀ (a : Λ) (x : R), D (algebraMap Λ R a * x) = algebraMap Λ k a * D x := by
    let : Module Λ k := Module.compHom k (algebraMap Λ k)
    refine ⟨fun a b => D.map_add a b, D.map_one_eq_zero, fun x y => ?_, fun a x => ?_⟩
    · rw [D.leibniz]
      rfl
    · rw [D.leibniz, D.map_algebraMap, smul_zero, add_zero]
      change residueHom R (algebraMap Λ R a) * D x = _
      rw [(residueHom R).commutes]
  have hker : ∀ a : R, residueHom R a = 0 → a ∈ maximalIdeal R := by
    intro a h
    refine (IsLocalRing.residue_eq_zero_iff a).mp (R.residueEquiv.injective ?_)
    rw [map_zero]
    exact h
  have hsurj : Function.Surjective (residueHom R) := fun x =>
    ⟨(IsLocalRing.residue_surjective (R.residueEquiv.symm x)).choose, by
      change R.residueEquiv (IsLocalRing.residue R _) = x
      rw [(IsLocalRing.residue_surjective (R.residueEquiv.symm x)).choose_spec,
        R.residueEquiv.apply_symm_apply]⟩
  have hwd : ∀ a b : R, residueHom R a = residueHom R b → D a = D b := by
    intro a b hab
    have h := hD (a - b) (hker (a - b) (by rw [map_sub, hab, sub_self]))
    have h2 : D a = D b + D (a - b) := by
      rw [← hadd b (a - b), show b + (a - b) = a by ring]
    rw [h, add_zero] at h2
    exact h2
  let s : k → R := fun x => (hsurj x).choose
  have hs : ∀ x, residueHom R (s x) = x := fun x => (hsurj x).choose_spec
  refine ⟨{ toFun := fun x => D (s x)
            map_add' := ?_
            map_smul' := ?_
            map_one_eq_zero' := ?_
            leibniz' := ?_ }, fun r => hwd _ _ (hs _).symm⟩
  · intro x y
    have h1 : D (s (x + y)) = D (s x + s y) := hwd _ _ (by rw [hs, map_add, hs, hs])
    rw [h1, hadd]
  · intro a x
    simp only [Algebra.smul_def]
    have h1 : D (s (algebraMap Λ k a * x)) = D (algebraMap Λ R a * s x) :=
      hwd _ _ (by rw [hs, map_mul, (residueHom R).commutes, hs])
    rw [h1, hscal]
    rfl
  · change D (s 1) = 0
    have h1 : D (s 1) = D 1 := hwd _ _ (by rw [hs, map_one])
    rw [h1, hone]
  · intro x y
    change D (s (x * y)) = x • D (s y) + y • D (s x)
    have h1 : D (s (x * y)) = D (s x * s y) := hwd _ _ (by rw [hs, map_mul, hs, hs])
    rw [h1, hleib, hs, hs]
    simp only [smul_eq_mul]

end

end Deformation

end
