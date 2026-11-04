module

public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksFrontier.RingTheory.PowerSeries.RegularRing
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Power series over a regular factorial ring

Let `R` be a regular domain whose invertible modules are all free. Then `R⟦X⟧` is a unique
factorization domain.

## Main results

* `CommRing.Pic.subsingleton_of_ringEquiv`: triviality of the Picard group transports along a
  ring isomorphism.
* `PowerSeries.X_mem_jacobson_bot`: `X` lies in the Jacobson radical of `R⟦X⟧`.
* `PowerSeries.subsingleton_pic`: the Picard group of `R⟦X⟧` is trivial when that of `R` is.
* `PowerSeries.uniqueFactorizationMonoid`: `R⟦X⟧` is factorial for `R` a regular domain with
  trivial Picard group.
* `PowerSeries.uniqueFactorizationMonoid_mvPolynomial`: `k[x_1, …, x_n][[t]]` is factorial. In
  particular `k[x,y][[t]]` is a unique factorization domain.
-/

@[expose] public noncomputable section

universe u v

open PowerSeries TensorProduct

/-- **Triviality of the Picard group transports along a ring isomorphism.** -/
public theorem CommRing.Pic.subsingleton_of_ringEquiv {S R : Type u} [CommRing S] [CommRing R]
    (e : S ≃+* R) [Subsingleton (CommRing.Pic R)] : Subsingleton (CommRing.Pic S) := by
  have key : ∀ M : CommRing.Pic S, CommRing.Pic.mapRingHom (f := (e.symm : R →+* S))
      (CommRing.Pic.mapRingHom (f := (e : S →+* R)) M) = M := by
    intro M
    rw [CommRing.Pic.mapRingHom_mapRingHom,
      show (e.symm : R →+* S).comp (e : S →+* R) = RingHom.id S from by ext; simp,
      CommRing.Pic.mapRingHom_id_apply]
  exact (Function.LeftInverse.injective (f := CommRing.Pic.mapRingHom (f := (e : S →+* R)))
    key).subsingleton

namespace PowerSeries

variable {R : Type u} [CommRing R]

/-- **The variable lies in the Jacobson radical of `R⟦X⟧`.** -/
public theorem X_mem_jacobson_bot : (X : R⟦X⟧) ∈ (⊥ : Ideal R⟦X⟧).jacobson :=
  Ideal.mem_jacobson_bot.2 fun y => isUnit_iff_constantCoeff.2 (by simp)

/-- **The Picard group of `R⟦X⟧` is trivial as soon as that of `R` is.** -/
public instance subsingleton_pic [Subsingleton (CommRing.Pic R)] :
    Subsingleton (CommRing.Pic R⟦X⟧) := by
  rw [CommRing.Pic.subsingleton_iff]
  intro L _ _ hinv
  let := hinv
  let : Subsingleton (CommRing.Pic (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)})) :=
    CommRing.Pic.subsingleton_of_ringEquiv quotientSpanXEquiv
  let : Module.Flat R⟦X⟧ L := Module.Flat.of_projective
  let : Module.FinitePresentation R⟦X⟧ L := Module.finitePresentation_of_projective _ L
  let : Module.Invertible (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)}) (QuotSMulTop (X : R⟦X⟧) L) :=
    Module.Invertible.congr
      ((QuotSMulTop.equivQuotTensor (X : R⟦X⟧) L).extendScalarsOfSurjective
        (Ideal.Quotient.mk_surjective (I := Ideal.span {(X : R⟦X⟧)}))).symm
  rw [← Module.free_quotSMulTop_iff_free R⟦X⟧ L X_mem_jacobson_bot
    (Module.Flat.isSMulRegular_of_nonZeroDivisors X_mem_nonZeroDivisors)]
  infer_instance

/-- **The power series ring over a regular domain with trivial Picard group is a unique
factorization domain.** -/
@[ega "IV 21.13.9" "partial"]
public theorem uniqueFactorizationMonoid [IsDomain R] [IsRegularRing R]
    [Subsingleton (CommRing.Pic R)] : UniqueFactorizationMonoid R⟦X⟧ := by
  refine UniqueFactorizationMonoid.of_localization_maximal_of_pic_subsingleton fun P hP => ?_
  let : P.IsMaximal := hP
  let : IsRegularLocalRing (Localization.AtPrime P) :=
    IsRegularRing.isRegularLocalRing_localization P
  exact IsRegularLocalRing.uniqueFactorizationMonoid _

/-- **`k[x_1, …, x_n][[t]]` is a unique factorization domain**; in particular `k[x,y][[t]]` is. -/
public theorem uniqueFactorizationMonoid_mvPolynomial (k : Type u) [Field k] (ι : Type v)
    [Finite ι] : UniqueFactorizationMonoid (MvPolynomial ι k)⟦X⟧ :=
  PowerSeries.uniqueFactorizationMonoid

end PowerSeries

end
