module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Formal unramifiedness descends along a nilpotent ideal

Let `R` be a ring, `I ⊆ R` a nilpotent ideal and `S` an `R`-algebra. If the induced map
`R ⧸ I → S ⧸ IS` is formally unramified, so is `R → S`.

This is the algebra translation of part (5) of Stacks 09ZW: with `A' = R`, `B' = S`, `A = R ⧸ I`
and `B = S ⧸ IS`, the base change of Kähler differentials gives
`Ω_{B/A} = Ω_{B'/A'} ⊗_{B'} B = Ω_{B'/A'} / I Ω_{B'/A'}`, so `Ω_{B/A} = 0` forces
`Ω_{B'/A'} = I Ω_{B'/A'}`, and a nilpotent ideal annihilates a module equal to its own
extension: `Ω_{B'/A'} = I^n Ω_{B'/A'} = 0`.

Unlike the usual Nakayama argument, no finiteness of `Ω_{B'/A'}` is needed, because the ideal is
nilpotent rather than merely contained in the Jacobson radical.

## Main results

* `Algebra.formallyUnramified_of_isNilpotent_quotient`: formal unramifiedness of the quotient map
  descends to the original algebra when the ideal is nilpotent.

## Implementation notes

The base change isomorphism is Mathlib's `KaehlerDifferential.tensorKaehlerEquiv`, which consumes
the pushout square `R → R ⧸ I`, `S → S ⧸ IS` in the form of an `Algebra.IsPushout` instance.
That instance is provided here from `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, the
identification of `S ⧸ IS` with `(R ⧸ I) ⊗[R] S`. The passage from
`(S ⧸ IS) ⊗[S] Ω[S⁄R]` back to a quotient of `Ω[S⁄R]` is
`TensorProduct.quotTensorEquivQuotSMul`.

## References

* [Stacks Project, Tag 00RV](https://stacks.math.columbia.edu/tag/00RV)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
-/

@[expose] public section

open TensorProduct

namespace Algebra

variable (R : Type*) [CommRing R] (I : Ideal R) (S : Type*) [CommRing S] [Algebra R S]

/-- The identification of `S ⧸ IS` with `(R ⧸ I) ⊗[R] S`, as a linear equivalence over
`R ⧸ I`. -/
private noncomputable def quotientSMulEquiv :
    (R ⧸ I) ⊗[R] S ≃ₗ[R ⧸ I] (S ⧸ I.map (algebraMap R S)) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

/-- The square `R → R ⧸ I`, `S → S ⧸ IS` is a pushout: `S ⧸ IS = (R ⧸ I) ⊗[R] S`. -/
private instance isPushout_quotient_map_quotient :
    Algebra.IsPushout R (R ⧸ I) S (S ⧸ I.map (algebraMap R S)) := by
  refine ⟨IsBaseChange.of_equiv (quotientSMulEquiv R I S) fun x => ?_⟩
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm_apply_eq.mpr
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk S I x).symm

/-- A module equal to its own extension by a nilpotent ideal vanishes: if `⊤ ≤ J • ⊤` then
`⊤ ≤ J ^ (n + 1) • ⊤` for every `n`, by iterating. -/
private theorem top_le_pow_smul_top {M : Type*} [AddCommGroup M] [Module S M] (J : Ideal S)
    (h : (⊤ : Submodule S M) ≤ J • ⊤) (n : ℕ) :
    (⊤ : Submodule S M) ≤ J ^ (n + 1) • (⊤ : Submodule S M) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact h.trans (Submodule.smul_mono le_rfl ih)

/-- **Formal unramifiedness descends along a nilpotent ideal.** Let `I` be a nilpotent ideal of
`R` and let `S` be an `R`-algebra. If `R ⧸ I → S ⧸ IS` is formally unramified then so is
`R → S`.

The module of relative differentials of `R ⧸ I → S ⧸ IS` is the reduction of `Ω[S⁄R]` modulo
`IS`, so the hypothesis says `Ω[S⁄R] = IS · Ω[S⁄R]`; since `IS` is nilpotent, iterating gives
`Ω[S⁄R] = 0`. -/
theorem formallyUnramified_of_isNilpotent_quotient (hI : IsNilpotent I)
    (hu : Algebra.FormallyUnramified (R ⧸ I) (S ⧸ I.map (algebraMap R S))) :
    Algebra.FormallyUnramified R S := by
  have hsub : Subsingleton ((S ⧸ I.map (algebraMap R S)) ⊗[S] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquiv R (R ⧸ I) S
      (S ⧸ I.map (algebraMap R S))).toEquiv.subsingleton
  have hquot :
      Subsingleton (Ω[S⁄R] ⧸ (I.map (algebraMap R S) • ⊤ : Submodule S Ω[S⁄R])) :=
    (TensorProduct.quotTensorEquivQuotSMul Ω[S⁄R]
      (I.map (algebraMap R S))).symm.toEquiv.subsingleton
  have htop : (⊤ : Submodule S Ω[S⁄R]) ≤ I.map (algebraMap R S) • ⊤ := by
    intro x _
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    exact hquot.allEq _ _
  obtain ⟨n, hn⟩ := hI
  have hI' : I ^ (n + 1) = ⊥ := by rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot]
  have hJ : I.map (algebraMap R S) ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_pow, hI', Ideal.map_bot]
  have hbot : (⊤ : Submodule S Ω[S⁄R]) ≤ ⊥ := by
    have h := top_le_pow_smul_top S (I.map (algebraMap R S)) htop n
    rwa [hJ, Submodule.bot_smul] at h
  have hzero (a : Ω[S⁄R]) : a = 0 := (Submodule.mem_bot S).mp (hbot Submodule.mem_top)
  exact ⟨⟨fun a b => by rw [hzero a, hzero b]⟩⟩

end Algebra

end
