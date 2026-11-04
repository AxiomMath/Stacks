module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs

/-!
# Transport of the integral closure and the delta invariant along a ring isomorphism

An isomorphism of commutative rings carries the integral closure of one in its total ring of
fractions to that of the other, compatibly with the structure maps, and therefore preserves the
delta invariant.

## Main definitions

* `Ring.integralClosureFractionRingCongr` transports the integral closure in the total ring of
  fractions along an isomorphism of the base rings.

## Main results

* `Ring.integralClosureFractionRingCongr_algebraMap` says this transport commutes with the
  canonical maps from the base rings.
* `Ring.deltaInvariant_eq_of_ringEquiv` says the delta invariant is an isomorphism invariant.

## Implementation notes

The two base rings are allowed to live in different universes, so the transport is stated for
`e : R ≃+* S` with `R : Type u` and `S : Type v`.  The underlying map is Mathlib's
`IsFractionRing.ringEquivOfRingEquiv e`, restricted to the integral closures; integrality is
carried across by `RingEquiv.isIntegral_iff` together with `isIntegral_algEquiv`, for which the
two base rings are temporarily regarded as acting on each other's fraction field.

The invariance of the delta invariant is not a formal consequence of the transport, because the
two quotients it compares are modules over *different* rings.  The proof therefore identifies
the quotient for `R` with the quotient for `S` as `R`-modules and then changes the base along
the surjection `algebraMap R S`, using `Module.length_eq_of_surjective`.

## References

* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
-/

@[expose] public noncomputable section

universe u v

namespace Ring

/-- An isomorphism `e : R ≃+* S` of commutative rings induces an isomorphism of the integral
closure of `R` in its total ring of fractions with that of `S`. -/
def integralClosureFractionRingCongr
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] (e : R ≃+* S) :
    integralClosure R (FractionRing R) ≃+*
      integralClosure S (FractionRing S) := by
  let eK : FractionRing R ≃+* FractionRing S :=
    IsFractionRing.ringEquivOfRingEquiv e
  letI : Algebra R (FractionRing S) :=
    ((algebraMap S (FractionRing S)).comp e.toRingHom).toAlgebra
  letI : Algebra S (FractionRing R) :=
    ((algebraMap R (FractionRing R)).comp e.symm.toRingHom).toAlgebra
  let eKR : FractionRing R ≃ₐ[R] FractionRing S :=
    { eK with
      commutes' := IsFractionRing.ringEquivOfRingEquiv_algebraMap e }
  let eKS : FractionRing S ≃ₐ[S] FractionRing R :=
    { eK.symm with
      commutes' := IsFractionRing.ringEquivOfRingEquiv_algebraMap e.symm }
  have hRS : (algebraMap S (FractionRing S)).comp e.toRingHom =
      algebraMap R (FractionRing S) := rfl
  have hSR : (algebraMap R (FractionRing R)).comp e.symm.toRingHom =
      algebraMap S (FractionRing R) := rfl
  let f : integralClosure R (FractionRing R) →+*
      integralClosure S (FractionRing S) :=
    { toFun := fun x => ⟨eK x.1,
        (e.isIntegral_iff hRS (eK x.1)).mp ((isIntegral_algEquiv eKR).mpr x.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  exact RingEquiv.ofBijective f
    ⟨fun x y h => Subtype.ext (eK.injective (congrArg Subtype.val h)),
      fun y => ⟨⟨eK.symm y.1, (e.symm.isIntegral_iff hSR (eK.symm y.1)).mp
        ((isIntegral_algEquiv eKS).mpr y.2)⟩, Subtype.ext (eK.apply_symm_apply y.1)⟩⟩

/-- The transport of the integral closure along `e : R ≃+* S` commutes with the canonical maps
from the base rings. -/
theorem integralClosureFractionRingCongr_algebraMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (e : R ≃+* S) (r : R) :
    integralClosureFractionRingCongr R S e
        (algebraMap R (integralClosure R (FractionRing R)) r) =
      algebraMap S (integralClosure S (FractionRing S)) (e r) :=
  Subtype.ext (IsFractionRing.ringEquivOfRingEquiv_algebraMap e r)

/-- The delta invariant is invariant under isomorphism of rings. -/
theorem deltaInvariant_eq_of_ringEquiv
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    deltaInvariant R = deltaInvariant S := by
  let CR := integralClosure R (FractionRing R)
  let CS := integralClosure S (FractionRing S)
  let QR := CR ⧸ LinearMap.range (Algebra.linearMap R CR)
  let QS := CS ⧸ LinearMap.range (Algebra.linearMap S CS)
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Algebra R CS := ((algebraMap S CS).comp e.toRingHom).toAlgebra
  let : Module R CS := Algebra.toModule
  let : Module R QS := Module.compHom QS e.toRingHom
  let : SMul R CS := (inferInstance : Module R CS).toSMul
  let : SMul R QS := (inferInstance : Module R QS).toSMul
  have : IsScalarTower R S CS := IsScalarTower.of_algebraMap_smul (by
    intro r x
    simp only [Algebra.smul_def]
    rfl)
  have : IsScalarTower R S QS := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eC : CR ≃ₐ[R] CS :=
    { integralClosureFractionRingCongr R S e with
      commutes' := integralClosureFractionRingCongr_algebraMap R S e }
  let f : CR →ₗ[R] QS :=
    (LinearMap.range (Algebra.linearMap S CS)).mkQ.restrictScalars R |>.comp
      eC.toLinearEquiv.toLinearMap
  have hsurj : Function.Surjective f :=
    (Submodule.mkQ_surjective _).comp eC.surjective
  have hker : f.ker = LinearMap.range (Algebra.linearMap R CR) := by
    ext x
    refine ⟨fun hx => ?_, ?_⟩
    · obtain ⟨s, hs⟩ : eC x ∈ LinearMap.range (Algebra.linearMap S CS) :=
        (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hx)
      refine ⟨e.symm s, eC.injective ?_⟩
      change eC (algebraMap R CR (e.symm s)) = eC x
      rw [eC.commutes]
      change algebraMap S CS (e (e.symm s)) = eC x
      simpa using hs
    · rintro ⟨r, rfl⟩
      exact LinearMap.mem_ker.mpr
        ((Submodule.Quotient.mk_eq_zero _).mpr ⟨e r, (eC.commutes r).symm⟩)
  let eQ : QR ≃ₗ[R] QS :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (f.quotKerEquivOfSurjective hsurj)
  have hlen := eQ.length_eq
  rwa [Module.length_eq_of_surjective (S := R) (R := S) (M := QS) e.surjective] at hlen

end Ring
