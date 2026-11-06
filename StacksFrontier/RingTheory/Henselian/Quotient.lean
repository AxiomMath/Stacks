module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Quotients of henselian local rings

A quotient of a henselian local ring by a proper ideal is again a henselian local ring, and
reduction modulo an ideal of the base is a pushout square of commutative rings.

## Main results

* `Stacks.Henselian.henselianLocalRing_quotient`
* `Stacks.Henselian.isPushout_quotient_map`
-/

@[expose] public section

open IsLocalRing

namespace Stacks.Henselian

/-- A quotient of a henselian local ring by a proper ideal is a henselian local ring: a monic
polynomial over `R ⧸ I` and an approximate root of it lift to `R`, where the approximate root is
refined to an honest one, and that root projects back. -/
theorem henselianLocalRing_quotient {R : Type*} [CommRing R] [HenselianLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) : HenselianLocalRing (R ⧸ I) := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hloc : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hlh : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have key : ∀ (p : Polynomial R) (x : R), Ideal.Quotient.mk I (p.eval x) =
      (p.map (Ideal.Quotient.mk I)).eval (Ideal.Quotient.mk I x) := fun p x => by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  refine ⟨fun f hf a₀ ha₀ hunit => ?_⟩
  obtain ⟨g, hgmap, -, hgmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts f).mpr fun n =>
      ⟨_, (Ideal.Quotient.mk_surjective (f.coeff n)).choose_spec⟩) hf
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a₀
  have hmem : g.eval r ∈ maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk I), Ideal.mem_comap, key, hgmap, hr]
    exact ha₀
  have hunit' : IsUnit ((Polynomial.derivative g).eval r) := by
    refine hlh.map_nonunit _ ?_
    rw [key, ← Polynomial.derivative_map, hgmap, hr]
    exact hunit
  obtain ⟨a, haroot, hasub⟩ := HenselianLocalRing.is_henselian g hgmonic r hmem hunit'
  refine ⟨Ideal.Quotient.mk I a, ?_, ?_⟩
  · rw [Polynomial.IsRoot, ← hgmap, ← key, haroot, map_zero]
  · rw [← hr, ← map_sub, ← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]
    exact hasub

/-- For an `R`-algebra `S` and an ideal `I` of `R`, the square of `R → R ⧸ I`, `R → S` and the two
quotient maps is a pushout square: `S ⧸ IS` is the base change `S ⊗[R] R ⧸ I`. -/
theorem isPushout_quotient_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Algebra.IsPushout R (R ⧸ I) S (S ⧸ I.map (algebraMap R S)) := by
  refine Algebra.IsPushout.symm ⟨IsBaseChange.of_equiv (Ideal.quotMapEquivTensorQuot S).symm ?_⟩
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [LinearEquiv.symm_apply_eq]
  simp [Ideal.quotMapEquivTensorQuot, LinearEquiv.eq_symm_apply, Algebra.smul_def]

end Stacks.Henselian

end
