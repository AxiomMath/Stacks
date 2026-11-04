module

public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Reduction
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch

/-!
# Geometric unibranchness through the integral closure of the ring itself

A local ring `A` is geometrically unibranch when the integral closure of its reduction
`A_red = A ⧸ nilradical A` in the fraction field of `A_red` is local with purely inseparable
residue extension. The integral closure of `A` *itself* in that fraction field is the same
subring, because `A → A_red` is surjective and hence integral. This module records the resulting
restatement, in the form in which the stalk of the pushforward of the structure sheaf of the
normalization of a scheme is computed by [Stacks, Tag 0C3B].

## Main results

* `IsGeometricallyUnibranchRing.exists_isLocalRing_of_algEquiv_integralClosure`: for a
  geometrically unibranch local ring, every `A`-algebra isomorphic to the integral closure of `A`
  in the fraction field of its reduction is local, its structure map is a local homomorphism, and
  the induced residue-field extension is purely inseparable.

## Implementation notes

The `A`-algebra structure on `Frac(A_red)` is `reductionFractionRingHom`, which is also the one
used by [Stacks, Tag 0C3B], so the two integral closures are subalgebras of the same algebra and
`isIntegral_trans` together with `IsIntegral.tower_top` identifies their underlying sets.

Local-ringness of the integral closure is part of the data of geometric unibranchness rather than
an instance, and local-ringness of the target is in turn needed before its residue field and the
locality of the structure map can even be stated. The conclusion therefore produces all three
existentially, exactly as `IsGeometricallyUnibranchRing` consumes them. It is stated for an
arbitrary isomorphic `A`-algebra so that a consumer holding such an isomorphism -- for instance
the stalk of the pushforward of the structure sheaf of a normalization -- needs no further
transport.

## References

* [Stacks Project, Tag 0BPZ](https://stacks.math.columbia.edu/tag/0BPZ)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open Stacks.NormalizationStalkAmbient

universe u v

namespace IsGeometricallyUnibranchRing

variable {A : Type u} [CommRing A]

/-- **Geometric unibranchness, through the integral closure of the ring itself.** Let `A` be a
geometrically unibranch local ring and let `B` be an `A`-algebra isomorphic to the integral
closure of `A` in the fraction field of the reduction of `A`. Then `B` is a local ring, its
structure map is a local homomorphism, and the induced extension of residue fields is purely
inseparable. -/
public theorem exists_isLocalRing_of_algEquiv_integralClosure [IsLocalRing A]
    (hA : _root_.IsGeometricallyUnibranchRing A) {B : Type v} [CommRing B] [Algebra A B]
    (eB :
      letI : Algebra A (FractionRing (A ⧸ nilradical A)) :=
        (reductionFractionRingHom A).toAlgebra
      B ≃ₐ[A] integralClosure A (FractionRing (A ⧸ nilradical A))) :
    ∃ hloc : IsLocalRing B, ∃ _ : IsLocalHom (algebraMap A B),
      letI := hloc
      IsPurelyInseparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  obtain ⟨hred, hnormal, hpure⟩ := hA
  let Ared := A ⧸ nilradical A
  let q : A →+* Ared := Ideal.Quotient.mk (nilradical A)
  let : IsDomain Ared := hred
  let : IsLocalRing Ared := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let : Algebra A (FractionRing Ared) := (reductionFractionRingHom A).toAlgebra
  let : SMul Ared (FractionRing Ared) := Algebra.toSMul
  let : SMul A (FractionRing Ared) := Algebra.toSMul
  let : IsScalarTower A Ared (FractionRing Ared) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsIntegral A Ared :=
    ⟨RingHom.isIntegral_of_surjective q Ideal.Quotient.mk_surjective⟩
  let D := integralClosure Ared (FractionRing Ared)
  let C := integralClosure A (FractionRing Ared)
  let : IsLocalRing D := hnormal
  let g : A →+* D := (algebraMap Ared D).comp q
  let : Algebra A D := g.toAlgebra
  let : IsLocalHom g := RingHom.isLocalHom_comp _ _
  have hmem : ∀ z : FractionRing Ared, z ∈ D ↔ z ∈ C := fun z =>
    ⟨fun hz => isIntegral_trans (R := A) (A := Ared) z hz, fun hz => hz.tower_top⟩
  let eDC : D ≃ₐ[A] C :=
    { toFun := fun z => ⟨z.1, (hmem z.1).1 z.2⟩
      invFun := fun z => ⟨z.1, (hmem z.1).2 z.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      commutes' := fun _ => Subtype.ext rfl }
  let eDB : D ≃ₐ[A] B := eDC.trans eB.symm
  have hloc : IsLocalRing B := eDB.toRingEquiv.isLocalRing
  refine ⟨hloc, ?_⟩
  let : IsLocalHom (eDB.toRingEquiv : D →+* B) :=
    IsLocalHom.of_surjective _ eDB.surjective
  have hmap : (eDB.toRingEquiv : D →+* B).comp g = algebraMap A B :=
    RingHom.ext fun a => eDB.commutes a
  have hlh : IsLocalHom (algebraMap A B) := by
    rw [← hmap]
    exact RingHom.isLocalHom_comp _ _
  exact ⟨hlh, (IsLocalRing.ResidueField.mapAlgEquiv' eDB).isPurelyInseparable_iff.mp hpure⟩

end IsGeometricallyUnibranchRing

end
