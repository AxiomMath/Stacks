module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite modules isomorphic to the restriction of their Frobenius base change

A finite module `M` over a Noetherian local ring of prime characteristic is free if `F_* F^* M`,
the Frobenius base change of `M` with its scalars restricted back along Frobenius, is isomorphic
to `M`.

## Main definitions

* `frobeniusBaseChange` is the Frobenius base change `ULift A ⊗[A] M`, as an `A`-module through the
  source factor `M`, that is, `F_* F^* M`.

## Main results

* `free_of_frobenius_baseChange_equiv` proves freeness from `F_* F^* M ≅ M`.

## Implementation notes

The `A`-module structure on `frobeniusBaseChange A p M` is the source action `a • (b ⊗ m) =
b ⊗ a m = (a ^ p * b) ⊗ m`, not multiplication on the target factor. The hypothesis
`F_* F^* M ≅ M` is much stronger than `F^* M ≅ M`: for `M ≠ 0` it forces `A` to be a field, which
is how the proof goes. Stacks Tag 0EBV, with `A` acting on the target factor, is
`free_of_frobeniusPullback_equiv`.
-/

@[expose] public section

open scoped TensorProduct

universe u v

/-- The Frobenius base change `ULift A ⊗[A] M` of an `A`-module `M`, where `A` acts on `ULift A`
through Frobenius. Its `A`-module structure is the source action, so as an `A`-module it is
`F_* F^* M`. -/
def frobeniusBaseChange
    (A : Type u) (p : ℕ) (M : Type v) [CommRing A] [Fact p.Prime] [CharP A p]
    [AddCommGroup M] [Module A M] : Type (max u v) :=
  let : Module A (ULift.{u} A) :=
    Module.compHom (ULift.{u} A)
      ((ULift.ringEquiv.symm.toRingHom).comp (frobenius A p))
  (ULift.{u} A) ⊗[A] M

/-- The additive group structure on the Frobenius base change of `M`, as a tensor product. -/
instance (A : Type u) (p : ℕ) (M : Type v)
    [CommRing A] [Fact p.Prime] [CharP A p] [AddCommGroup M] [Module A M] :
    AddCommGroup (frobeniusBaseChange A p M) := by
  unfold frobeniusBaseChange
  infer_instance

/-- The `A`-module structure on the Frobenius base change of `M`. It is the source action
`a • (b ⊗ m) = b ⊗ a m`, not multiplication on the target factor: the proof of
`free_of_frobenius_baseChange_equiv` uses it as the standard `A`-module structure of the tensor
product. -/
instance (A : Type u) (p : ℕ) (M : Type v)
    [CommRing A] [Fact p.Prime] [CharP A p] [AddCommGroup M] [Module A M] :
    Module A (frobeniusBaseChange A p M) := by
  let : Module A (ULift.{u} A) :=
    Module.compHom (ULift.{u} A)
      ((ULift.ringEquiv.symm.toRingHom).comp (frobenius A p))
  let : Algebra A (ULift.{u} A) :=
    ((ULift.ringEquiv.symm.toRingHom).comp (frobenius A p)).toAlgebra
  let : Module (ULift.{u} A) (frobeniusBaseChange A p M) := by
    unfold frobeniusBaseChange
    infer_instance
  exact Module.compHom _ ULift.ringEquiv.symm.toRingHom

/-- The image of an ideal under the Frobenius endomorphism lies in its `p`-th power. -/
private lemma map_frobenius_le_pow {A : Type*} [CommSemiring A]
    (I : Ideal A) (p : ℕ) [ExpChar A p] :
    Ideal.map (frobenius A p) I ≤ I ^ p := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change frobenius A p x ∈ I ^ p
  simpa only [frobenius_def] using Ideal.pow_mem_pow hx p

/-- A finite module `M` over a Noetherian local ring of characteristic `p` with `F_* F^* M ≅ M` is
free. The `A`-action on `frobeniusBaseChange A p M` is the source action, so the hypothesis forces
`A` to be a field when `M ≠ 0`; Stacks Tag 0EBV is `free_of_frobeniusPullback_equiv`. -/
theorem free_of_frobenius_baseChange_equiv
    {A : Type u} {M : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : ℕ) [Fact p.Prime] [CharP A p]
    (h : Nonempty (frobeniusBaseChange A p M ≃ₗ[A] M)) :
    Module.Free A M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact Module.Free.of_subsingleton A M
  · let κ := IsLocalRing.ResidueField A
    let B := ULift.{u} A
    let rho : A ≃+* B := ULift.ringEquiv.symm
    let φ : A →+* B := rho.toRingHom.comp (frobenius A p)
    let : Algebra A B := φ.toAlgebra
    let : Module A B := Algebra.toModule
    obtain ⟨e⟩ := h
    let e' : (B ⊗[A] M) ≃ₗ[A] M := e
    let V := κ ⊗[A] M
    let W := κ ⊗[A] B
    have : Nontrivial V := not_subsingleton_iff_nontrivial.mp fun hV =>
      not_subsingleton M (IsLocalRing.subsingleton_tensorProduct.mp hV)
    let eV : V ≃ₗ[κ] W ⊗[κ] V :=
      (LinearEquiv.baseChange A κ _ _ e').symm.trans
        (TensorProduct.AlgebraTensorModule.distribBaseChange A κ B M)
    have hdim : Module.finrank κ W = 1 := by
      have hh := eV.finrank_eq
      rw [Module.finrank_tensorProduct (R := κ) (S := κ) (M := W) (M' := V)] at hh
      exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos (by simpa using hh.symm)
    let m := IsLocalRing.maximalIdeal A
    let J := Ideal.map φ m
    let Q := B ⧸ J
    let : Algebra κ Q := Ideal.Quotient.algebraQuotientMapQuotient
    let eQ : Q ≃ₐ[κ] W := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m
    have hbij := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := κ) (E := Q)).mp
      (eQ.toLinearEquiv.finrank_eq.trans hdim)
    have hmle : m ≤ m ^ p := by
      intro a ha
      have hpow : (Ideal.Quotient.mk J (rho a)) ^ p = 0 := by
        rw [← map_pow]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        change (rho a) ^ p ∈ Ideal.map φ m
        simpa [φ, frobenius_def] using Ideal.mem_map_of_mem φ ha
      obtain ⟨z, hz⟩ := hbij.2 (Ideal.Quotient.mk J (rho a))
      have hzpow : z ^ p = 0 := hbij.1 (by simpa only [map_pow, map_zero, hz] using hpow)
      have hmem : rho a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (by
        rw [← hz, eq_zero_of_pow_eq_zero hzpow, map_zero])
      have hh := Ideal.mem_map_of_mem rho.symm.toRingHom hmem
      change rho.symm (rho a) ∈ Ideal.map rho.symm.toRingHom (Ideal.map φ m) at hh
      rw [rho.symm_apply_apply, Ideal.map_map] at hh
      have hfrob : rho.symm.toRingHom.comp φ = frobenius A p := by
        ext x
        simp [φ]
      rw [hfrob] at hh
      exact map_frobenius_le_pow m p hh
    have hm2 : m ≤ m * m := by
      simpa [pow_two] using hmle.trans
        (Ideal.pow_le_pow_right (Nat.Prime.two_le (Fact.out : p.Prime)))
    have hfield : IsField A := by
      by_contra h
      exact (not_lt_of_ge (by simpa [m, pow_two] using hm2))
        ((IsLocalRing.maximalIdeal_sq_lt_maximalIdeal A).mpr h)
    let := hfield.toField
    infer_instance
