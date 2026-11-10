module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import StacksFrontier.Deformation.Basic

/-!
# The residue field itself as an object of the base category

The base category `𝒞_Λ` has a canonical object supported on the residue field `k`: the field
`k` is an Artinian local `Λ`-algebra, its maximal ideal is zero, and so its residue field is
canonically `k` again. This file records that object together with the computation of its
residue-field identification on representatives.

## Main definitions

* `Deformation.Examples.residueFieldBase`: the residue field `k` as an object of `𝒞_Λ`.

## Main results

* `Deformation.Examples.residueFieldBase_residueEquiv_residue`: its residue-field
  identification sends the class of `a` to `a`.
* `Deformation.Examples.maximalIdeal_residueFieldBase`: its maximal ideal vanishes.

## Implementation notes

`Deformation.residueFieldObject` is the analogous object whose carrier is `ULift k`. The
deformation problems of Stacks 93.4–93.7 carry a module, a representation or a graded algebra
over `k` itself, so they use the object whose carrier is literally `k`. The two objects are
isomorphic in `𝒞_Λ` whenever both are formed, but they are not the same object, and the deformed
datum does not transport across the difference for free.

## References

* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
-/

@[expose] public section

namespace Deformation.Examples

universe u w

variable (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue field `k`, regarded as an object of `𝒞_Λ` with carrier exactly `k`. -/
public noncomputable abbrev residueFieldBase : ArtinianLocalAlgCat.{u, w, w} Λ k where
  carrier := k
  residueEquiv :=
    (Ideal.quotientEquivAlgOfEq Λ (IsLocalRing.maximalIdeal_eq_bot (R := k))).trans
      (AlgEquiv.quotientBot Λ k)

/-- The residue-field identification of `residueFieldBase` is the inverse of the residue map:
it sends the class of `a` back to `a`. -/
public theorem residueFieldBase_residueEquiv_residue (a : k) :
    (residueFieldBase Λ k).residueEquiv (IsLocalRing.residue k a) = a := by
  change ((Ideal.quotientEquivAlgOfEq Λ (IsLocalRing.maximalIdeal_eq_bot (R := k))).trans
    (AlgEquiv.quotientBot Λ k)) (Ideal.Quotient.mk _ a) = a
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]

/-- The maximal ideal of `residueFieldBase` vanishes: its carrier is the field `k`. -/
@[simp]
public theorem maximalIdeal_residueFieldBase :
    IsLocalRing.maximalIdeal (residueFieldBase.{u, w} Λ k) = ⊥ :=
  IsLocalRing.maximalIdeal_eq_bot (R := k)

end Deformation.Examples
