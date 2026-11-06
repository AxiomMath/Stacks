module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smallness of a quotient by an ideal multiple

Mathlib proves that `M ⧸ I • N` is finite as soon as `R ⧸ I` and `M ⧸ N` are finite and `N` is
finitely generated (`Submodule.finite_quotient_smul`), and deduces that `R ⧸ I ^ n` is finite
(`Ideal.finite_quotient_pow`). Here are the same two statements with `Finite` replaced by
`Small.{v}`, together with the smallness of a quotient by an infimum of ideals.

## Main results

* `Submodule.small_quotient_smul`: `M ⧸ I • N` is small when `R ⧸ I` and `M ⧸ N` are and `N` is
  finitely generated.
* `Ideal.small_quotient_pow`: `R ⧸ I ^ n` is small when `R ⧸ I` is and `I` is finitely generated.
* `Ideal.small_quotient_iInf`: a quotient by an infimum of a small family of two-sided ideals is
  small when each quotient is.
-/

@[expose] public section

open scoped TensorProduct

universe v

/-- Dividing a finitely generated submodule by an ideal multiple keeps the quotient small, as
soon as the quotients by the ideal and by the submodule are small. -/
public theorem Submodule.small_quotient_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M)
    [Small.{v} (R ⧸ I)] [Small.{v} (M ⧸ N)] (hN : N.FG) : Small.{v} (M ⧸ I • N) := by
  let e : (N ⧸ (I • N).comap N.subtype) ≃ₗ[R] (R ⧸ I) ⊗[R] N :=
    Submodule.quotEquivOfEq _ (I • (⊤ : Submodule R N))
      (Submodule.map_injective_of_injective N.injective_subtype
        (by simp [Submodule.smul_le_right])) ≪≫ₗ
      (TensorProduct.quotTensorEquivQuotSMul N I).symm
  have : Module.Finite R N := .of_fg hN
  have : Small.{v} ((R ⧸ I) ⊗[R] N) := Module.Finite.small (R ⧸ I) _
  have : Small.{v} (N ⧸ (I • N).comap N.subtype) := small_map e.toEquiv
  have : Small.{v} (M ⧸ N.toAddSubgroup) := inferInstanceAs (Small.{v} (M ⧸ N))
  have : Small.{v} (N.toAddSubgroup ⧸
      (I • N).toAddSubgroup.addSubgroupOf N.toAddSubgroup) :=
    inferInstanceAs (Small.{v} (N ⧸ (I • N).comap N.subtype))
  exact small_map (AddSubgroup.quotientEquivProdOfLE
    (show (I • N).toAddSubgroup ≤ N.toAddSubgroup from Submodule.smul_le_right))

/-- Every quotient of a commutative ring by a power of a finitely generated ideal is small as
soon as the quotient by the ideal itself is. -/
public theorem Ideal.small_quotient_pow {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    [Small.{v} (R ⧸ I)] (n : ℕ) : Small.{v} (R ⧸ I ^ n) := by
  induction n with
  | zero => simp only [pow_zero, Ideal.one_eq_top]; infer_instance
  | succ n hn => exact Submodule.small_quotient_smul (I ^ n) I hI

/-- A quotient by the infimum of a small family of two-sided ideals is small as soon as each
quotient by a member of the family is. -/
public theorem Ideal.small_quotient_iInf {R : Type*} [Ring R] {ι : Type*} [Small.{v} ι]
    (J : ι → Ideal R) [∀ i, (J i).IsTwoSided] [∀ i, Small.{v} (R ⧸ J i)] :
    Small.{v} (R ⧸ ⨅ i, J i) :=
  small_of_injective (Ideal.quotientInfToPiQuotient_inj J)

end
