module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The maximal ideal of a local ring lands in the Jacobson radical of an integral algebra

For `T` integral over a local ring `R`, every maximal ideal of `T` contracts to a maximal ideal of
`R`, hence to `𝔪`; so `𝔪T` lies in the Jacobson radical of `T`.
-/

@[expose] public section

open IsLocalRing

public lemma map_maximalIdeal_le_jacobson (R : Type*) [CommRing R] [IsLocalRing R] (T : Type*)
    [CommRing T] [Algebra R T] [Algebra.IsIntegral R T] :
    (maximalIdeal R).map (algebraMap R T) ≤ Ideal.jacobson (⊥ : Ideal T) := by
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro J ⟨-, hJ⟩
  rw [Ideal.map_le_iff_le_comap]
  exact
    le_of_eq
      (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) J)).symm
