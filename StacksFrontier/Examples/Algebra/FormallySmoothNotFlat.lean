module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import StacksCore.Tactic.StacksAttribute

/-!
# A formally smooth ring map which is not flat

There exists a formally smooth homomorphism of commutative rings which is not flat.

The witness is the augmentation `A = 𝔽₂[ℚ] → 𝔽₂` of the group algebra of the additive group of
the rationals over the field with two elements. Its kernel `J` is idempotent: in characteristic
two the generator `x^q - 1` of `J` equals `(x^{q/2} - 1)²`, and divisibility of `ℚ` lets this be
done for every `q`, so `J = J²`. A surjection with idempotent kernel is formally smooth. On the
other hand `x² - 1` is a nonzerodivisor of `A` killing the generator of `𝔽₂`, so `𝔽₂` is not a
torsion-free, hence not a flat, `A`-module.

## Main results

* `Stacks.Examples.exists_formallySmooth_not_flat`: there is a formally smooth, non-flat ring map.

## Implementation notes

Both properties are stated for the same ring homomorphism; Mathlib's `RingHom.FormallySmooth`
and `RingHom.Flat` use the algebra structure induced by that map. The statement is universe
polymorphic, so the construction is transported along `ULift`.

## References

* [Stacks Project, Tag 057W](https://stacks.math.columbia.edu/tag/057W)
-/

@[expose] public section

namespace Stacks.Examples

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private abbrev charTwoField := ZMod 2

private abbrev rationalGroupAlgebra := AddMonoidAlgebra charTwoField ℚ

private def trivialChar : Multiplicative ℚ →* charTwoField where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' _ _ := by simp

private noncomputable def augmentation :
    rationalGroupAlgebra →ₐ[charTwoField] charTwoField :=
  AddMonoidAlgebra.lift charTwoField charTwoField ℚ trivialChar

private lemma augmentation_apply (x : rationalGroupAlgebra) :
    augmentation x = x.coeff.sum (fun _ c => c) := by
  simp [augmentation, AddMonoidAlgebra.lift_apply, trivialChar]

private lemma augmentation_single (q : ℚ) (c : charTwoField) :
    augmentation (AddMonoidAlgebra.single q c) = c := by
  simp [augmentation, trivialChar]

private lemma augmentation_surjective :
    Function.Surjective (augmentation : rationalGroupAlgebra →+* charTwoField) :=
  fun x => ⟨AddMonoidAlgebra.single (0 : ℚ) x, by simp [augmentation]⟩

private lemma generator_eq_sq (q : ℚ) :
    (AddMonoidAlgebra.single q (1 : charTwoField) - 1 : rationalGroupAlgebra) =
      (AddMonoidAlgebra.single (q / 2) (1 : charTwoField) - 1) ^ 2 := by
  rw [sub_sq, pow_two, AddMonoidAlgebra.single_mul_single, add_halves]
  simp only [one_mul]
  have h2 : (2 : rationalGroupAlgebra) = 0 :=
    (map_natCast (algebraMap charTwoField rationalGroupAlgebra) 2).symm.trans <|
      (congrArg (algebraMap charTwoField rationalGroupAlgebra) (ZMod.natCast_self 2)).trans
        (map_zero _)
  have hm : (-1 : rationalGroupAlgebra) = 1 :=
    neg_eq_iff_add_eq_zero.mpr (one_add_one_eq_two.trans h2)
  simp [h2, hm, sub_eq_add_neg]

private lemma single_sub_one_mem_ker (q : ℚ) :
    (AddMonoidAlgebra.single q (1 : charTwoField) - 1 : rationalGroupAlgebra) ∈
      RingHom.ker (augmentation : rationalGroupAlgebra →+* charTwoField) := by
  change augmentation (AddMonoidAlgebra.single q 1 - 1) = 0
  simp only [map_sub, augmentation_single, map_one, sub_self]

private lemma single_sub_one_mem_ker_sq (q : ℚ) :
    (AddMonoidAlgebra.single q (1 : charTwoField) - 1 : rationalGroupAlgebra) ∈
      RingHom.ker (augmentation : rationalGroupAlgebra →+* charTwoField) ^ 2 := by
  rw [generator_eq_sq q]
  exact Ideal.pow_mem_pow (single_sub_one_mem_ker _) 2

private lemma augmentation_ker_le_sq :
    RingHom.ker (augmentation : rationalGroupAlgebra →+* charTwoField) ≤
      (RingHom.ker (augmentation : rationalGroupAlgebra →+* charTwoField)) ^ 2 := by
  intro x hx
  have hsum : ∑ q ∈ x.coeff.support, x.coeff q = 0 :=
    (augmentation_apply x).symm.trans (RingHom.mem_ker.mp hx)
  let e : charTwoField →+ rationalGroupAlgebra :=
    (AddMonoidAlgebra.singleZeroAlgHom (R := charTwoField) (A := charTwoField)
      (M := ℚ)).toAddMonoidHom
  have hsecond :
      (∑ q ∈ x.coeff.support, AddMonoidAlgebra.single (0 : ℚ) (x.coeff q)) = 0 := by
    simpa [e, AddMonoidAlgebra.singleZeroAlgHom] using
      (map_sum e (fun q : ℚ => x.coeff q) x.coeff.support).symm.trans
        (congrArg e hsum)
  have hdecomp : x = x.coeff.sum
      (fun q c => AddMonoidAlgebra.single q c - AddMonoidAlgebra.single (0 : ℚ) c) := by
    simp only [Finsupp.sum, Finset.sum_sub_distrib, hsecond, sub_zero]
    exact (AddMonoidAlgebra.sum_coeff_single x).symm
  rw [hdecomp]
  simp only [Finsupp.sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  have hcq : (AddMonoidAlgebra.single q (x.coeff q) -
      AddMonoidAlgebra.single (0 : ℚ) (x.coeff q) : rationalGroupAlgebra) =
      AddMonoidAlgebra.single (0 : ℚ) (x.coeff q) * (AddMonoidAlgebra.single q 1 - 1) := by
    simp [mul_sub, AddMonoidAlgebra.single_mul_single]
  rw [hcq]
  exact Ideal.mul_mem_left _ _ (single_sub_one_mem_ker_sq q)

private lemma augmentation_ker_isIdempotentElem :
    IsIdempotentElem (RingHom.ker (augmentation : rationalGroupAlgebra →+* charTwoField)) := by
  unfold IsIdempotentElem
  refine le_antisymm Ideal.mul_le_right ?_
  simpa [pow_two] using augmentation_ker_le_sq

private lemma generator_two_ne_zero :
    (AddMonoidAlgebra.single (2 : ℚ) (1 : charTwoField) - 1 : rationalGroupAlgebra) ≠ 0 := by
  intro h
  have hcoeff :
      ((AddMonoidAlgebra.single (2 : ℚ) (1 : charTwoField) - 1 :
        rationalGroupAlgebra).coeff) (2 : ℚ) = 1 := by
    simp [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.one_def]
  rw [h] at hcoeff
  simp at hcoeff

private lemma augmentation_not_flat : ¬ augmentation.toRingHom.Flat := by
  intro hf
  let : Algebra rationalGroupAlgebra charTwoField := augmentation.toRingHom.toAlgebra
  have : Module.Flat rationalGroupAlgebra charTwoField := hf
  let r : rationalGroupAlgebra := AddMonoidAlgebra.single (2 : ℚ) (1 : charTwoField) - 1
  have hr : r ∈ nonZeroDivisors rationalGroupAlgebra :=
    (mem_nonZeroDivisors_iff_ne_zero).2 generator_two_ne_zero
  have hkill : r • (1 : charTwoField) = 0 := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]
    exact RingHom.mem_ker.mp (single_sub_one_mem_ker 2)
  exact one_ne_zero
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hr hkill : (1 : charTwoField) = 0)

universe u v

private lemma augmentation_ulift_ker_isIdempotentElem :
    IsIdempotentElem (RingHom.ker (augmentation.toRingHom.ulift.{u, v})) := by
  let eA : ULift.{u, 0} rationalGroupAlgebra ≃+* rationalGroupAlgebra := ULift.ringEquiv.{0, u}
  let J : Ideal rationalGroupAlgebra := RingHom.ker augmentation.toRingHom
  let JU : Ideal (ULift.{u, 0} rationalGroupAlgebra) :=
    RingHom.ker (augmentation.toRingHom.ulift.{u, v})
  have hker : JU = Ideal.comap eA.toRingHom J := by
    ext x
    change (ULift.up (augmentation x.down) : ULift.{v} charTwoField) = ULift.up 0 ↔
      augmentation x.down = 0
    exact ULift.up_inj
  have hmap : Ideal.map eA.toRingHom JU = J := by
    rw [hker, Ideal.map_comap_of_surjective eA.toRingHom eA.surjective]
  have hinj : Function.Injective (Ideal.map eA.toRingHom) := by
    intro I J h
    have h' := congrArg (Ideal.comap eA.toRingHom) h
    rw [Ideal.comap_map_of_surjective eA.toRingHom eA.surjective,
      Ideal.comap_map_of_surjective eA.toRingHom eA.surjective,
      Ideal.comap_bot_of_injective eA.toRingHom eA.injective] at h'
    simpa only [sup_bot_eq] using h'
  change JU * JU = JU
  apply hinj
  have hsq : J ^ 2 = J := (pow_two J).trans augmentation_ker_isIdempotentElem
  simpa only [← pow_two, Ideal.map_pow, hmap] using hsq

private lemma augmentation_ulift_formallySmooth :
    (augmentation.toRingHom.ulift.{u, v} :
      ULift.{u} rationalGroupAlgebra →+* ULift.{v} charTwoField).FormallySmooth := by
  let fU : ULift.{u, 0} rationalGroupAlgebra →+* ULift.{v, 0} charTwoField :=
    augmentation.toRingHom.ulift.{u, v}
  have hsurj : Function.Surjective fU := by
    intro y
    obtain ⟨x, hx⟩ := augmentation_surjective y.down
    exact ⟨ULift.up x, ULift.ext (by simp [fU, RingHom.ulift_apply, hx])⟩
  let : Algebra (ULift.{u, 0} rationalGroupAlgebra) (ULift.{v, 0} charTwoField) := fU.toAlgebra
  have hsurjA : Function.Surjective
      (algebraMap (ULift.{u, 0} rationalGroupAlgebra) (ULift.{v, 0} charTwoField)) := hsurj
  have hIdem : IsIdempotentElem
      (RingHom.ker (algebraMap (ULift.{u, 0} rationalGroupAlgebra)
        (ULift.{v, 0} charTwoField))) := augmentation_ulift_ker_isIdempotentElem
  change Algebra.FormallySmooth (ULift.{u, 0} rationalGroupAlgebra) (ULift.{v, 0} charTwoField)
  exact (Algebra.FormallySmooth.iff_of_surjective
    (R := ULift.{u, 0} rationalGroupAlgebra) hsurjA).2 hIdem

/-- There exists a formally smooth ring map which is not flat. -/
@[stacks 057W]
public theorem exists_formallySmooth_not_flat :
    ∃ (R S : Type*) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
      f.FormallySmooth ∧ ¬ f.Flat :=
  ⟨ULift rationalGroupAlgebra, ULift charTwoField, inferInstance, inferInstance,
    augmentation.toRingHom.ulift, augmentation_ulift_formallySmooth,
    fun hf => augmentation_not_flat (RingHom.Flat.ulift_iff.mp hf)⟩

end Stacks.Examples

end
