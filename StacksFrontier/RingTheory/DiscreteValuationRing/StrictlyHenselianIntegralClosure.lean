module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integral closures of a strictly henselian discrete valuation ring

Let `A` be a strictly henselian discrete valuation ring with fraction field `K` and let `L / K`
be a finite extension. This file records that the integral closure `C = integralClosure A L` is
again a *strictly henselian* discrete valuation ring, and describes its residue field.

The discrete valuation ring half is
`Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure`, which only
needs `A` henselian. The strictly henselian half needs neither the discrete valuation ring
hypothesis nor finiteness of `L / K`: a domain integral over a henselian local ring is henselian
local with a separably closed residue field as soon as the base residue field is separably
closed, which is Stacks 092X in the form
`RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain`. So the general statement
`strictlyHenselianLocalRing_integralClosure` is proved for an arbitrary field `L` over an
arbitrary strictly henselian local ring `A`, and the discrete valuation ring package is assembled
from it.

The residue field extension `κ(A) → κ(C)` is purely inseparable, again by Stacks 092X. When
`κ(A)` is moreover algebraically closed — the situation of a strictly henselian discrete
valuation ring in residue characteristic zero — the extension is an isomorphism, so `C` has the
same residue field as `A`.

## Main results

* `Stacks.Henselian.strictlyHenselianLocalRing_of_isIntegral_of_isDomain`: a domain integral over
  a strictly henselian local ring is strictly henselian local.
* `Stacks.Henselian.strictlyHenselianLocalRing_integralClosure`: the integral closure of a
  strictly henselian local ring in a field is strictly henselian local.
* `Stacks.Henselian.isDiscreteValuationRing_strictlyHenselian_integralClosure`: the integral
  closure of a strictly henselian discrete valuation ring in a finite extension of its fraction
  field is a strictly henselian discrete valuation ring, the structure map is local, and `L` is
  its fraction field.
* `Stacks.Henselian.isDiscreteValuationRing_strictlyHenselian_module_finite_integralClosure`: the
  same for a finite *separable* extension, with module-finiteness over the base added.
* `Stacks.Henselian.isPurelyInseparable_residueField_map_integralClosure`: the induced residue
  field extension is purely inseparable.
* `Stacks.Henselian.bijective_residueField_map_integralClosure`: that extension is bijective
  once the residue field of `A` is algebraically closed.

## References

* [The Stacks Project, Tag 092X](https://stacks.math.columbia.edu/tag/092X)
* [The Stacks Project, Tag 03QK](https://stacks.math.columbia.edu/tag/03QK)
* [The Stacks Project, Tag 032L](https://stacks.math.columbia.edu/tag/032L)
-/

@[expose] public section

universe uA uK uL

open IsLocalRing

namespace Stacks.Henselian

/-! ### Strict henselianness along an integral domain extension -/

/-- A domain integral over a strictly henselian local ring is strictly henselian local.

Stacks 092X supplies the henselian structure, the locality of the structure map and — from the
residue field of the base being separably closed — the separable closedness of the residue field
of the target. -/
theorem strictlyHenselianLocalRing_of_isIntegral_of_isDomain
    (A : Type uA) (B : Type uL) [CommRing A] [CommRing B] [StrictlyHenselianLocalRing A]
    [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B] : StrictlyHenselianLocalRing B := by
  obtain ⟨hB, hlocal, hres⟩ :=
    (algebraMap A B).exists_henselianLocalRing_of_isIntegral_of_isDomain
      (fun x => Algebra.IsIntegral.isIntegral x)
  let : HenselianLocalRing B := hB
  let : IsLocalRing B := hB.toIsLocalRing
  let : IsLocalHom (algebraMap A B) := hlocal
  let : IsSepClosed (ResidueField B) := (hres inferInstance).1
  exact ⟨⟩

/-- The structure map of a domain integral over a strictly henselian local ring is a local
homomorphism. -/
theorem isLocalHom_algebraMap_of_isIntegral_of_isDomain
    (A : Type uA) (B : Type uL) [CommRing A] [CommRing B] [StrictlyHenselianLocalRing A]
    [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B] : IsLocalHom (algebraMap A B) :=
  ((algebraMap A B).exists_henselianLocalRing_of_isIntegral_of_isDomain
    (fun x => Algebra.IsIntegral.isIntegral x)).choose_spec.choose

/-- The residue field extension of a domain integral over a strictly henselian local ring is
purely inseparable: it is algebraic over a separably closed field. -/
@[sga "7 XIII 0.2" "special case"]
theorem isPurelyInseparable_residueField_map_of_isIntegral_of_isDomain
    (A : Type uA) (B : Type uL) [CommRing A] [CommRing B] [StrictlyHenselianLocalRing A]
    [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B] :
    letI : StrictlyHenselianLocalRing B :=
      strictlyHenselianLocalRing_of_isIntegral_of_isDomain A B
    letI : IsLocalHom (algebraMap A B) :=
      isLocalHom_algebraMap_of_isIntegral_of_isDomain A B
    (ResidueField.map (algebraMap A B)).IsPurelyInseparable := by
  obtain ⟨hB, hlocal, hres⟩ :=
    (algebraMap A B).exists_henselianLocalRing_of_isIntegral_of_isDomain
      (fun x => Algebra.IsIntegral.isIntegral x)
  exact (hres inferInstance).2

/-! ### The integral closure in a field extension -/

/-- **The integral closure of a strictly henselian local ring in a field is strictly henselian
local.** -/
theorem strictlyHenselianLocalRing_integralClosure
    (A : Type uA) (L : Type uL) [CommRing A] [StrictlyHenselianLocalRing A]
    [Field L] [Algebra A L] : StrictlyHenselianLocalRing (integralClosure A L) :=
  strictlyHenselianLocalRing_of_isIntegral_of_isDomain A (integralClosure A L)

/-- The structure map into the integral closure is a local homomorphism. -/
theorem isLocalHom_algebraMap_integralClosure_of_strictlyHenselian
    (A : Type uA) (L : Type uL) [CommRing A] [StrictlyHenselianLocalRing A]
    [Field L] [Algebra A L] : IsLocalHom (algebraMap A (integralClosure A L)) :=
  isLocalHom_algebraMap_of_isIntegral_of_isDomain A (integralClosure A L)

/-- The residue field of the integral closure is purely inseparable over the residue field of a
strictly henselian local base. -/
theorem isPurelyInseparable_residueField_map_integralClosure
    (A : Type uA) (L : Type uL) [CommRing A] [StrictlyHenselianLocalRing A]
    [Field L] [Algebra A L] :
    letI : StrictlyHenselianLocalRing (integralClosure A L) :=
      strictlyHenselianLocalRing_integralClosure A L
    letI : IsLocalHom (algebraMap A (integralClosure A L)) :=
      isLocalHom_algebraMap_integralClosure_of_strictlyHenselian A L
    (ResidueField.map (algebraMap A (integralClosure A L))).IsPurelyInseparable :=
  isPurelyInseparable_residueField_map_of_isIntegral_of_isDomain A (integralClosure A L)

/-- When the residue field of the strictly henselian base is algebraically closed, the integral
closure has the *same* residue field: the extension is algebraic over an algebraically closed
field, hence bijective.

This is the form the consumers over a strictly henselian discrete valuation ring in residue
characteristic zero use, where the residue field is algebraically closed. -/
theorem bijective_residueField_map_integralClosure
    (A : Type uA) (L : Type uL) [CommRing A] [StrictlyHenselianLocalRing A]
    [Field L] [Algebra A L] [IsAlgClosed (ResidueField A)] :
    letI : StrictlyHenselianLocalRing (integralClosure A L) :=
      strictlyHenselianLocalRing_integralClosure A L
    letI : IsLocalHom (algebraMap A (integralClosure A L)) :=
      isLocalHom_algebraMap_integralClosure_of_strictlyHenselian A L
    Function.Bijective (ResidueField.map (algebraMap A (integralClosure A L))) := by
  let : StrictlyHenselianLocalRing (integralClosure A L) :=
    strictlyHenselianLocalRing_integralClosure A L
  let : IsLocalHom (algebraMap A (integralClosure A L)) :=
    isLocalHom_algebraMap_integralClosure_of_strictlyHenselian A L
  have : Algebra.IsIntegral A (ResidueField (integralClosure A L)) :=
    Algebra.IsIntegral.trans (integralClosure A L)
  have : Algebra.IsIntegral (ResidueField A) (ResidueField (integralClosure A L)) :=
    Algebra.IsIntegral.tower_top A
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-! ### The discrete valuation ring package -/

section DiscreteValuationRing

variable (A : Type uA) (K : Type uK) (L : Type uL) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [StrictlyHenselianLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K in
/-- **The integral closure of a strictly henselian discrete valuation ring in a finite extension
of its fraction field is again a strictly henselian discrete valuation ring.**

The discrete valuation ring half is Krull–Akizuki together with the henselian locality of the
integral closure, i.e.
`Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure`; the strictly
henselian half is `strictlyHenselianLocalRing_integralClosure`, which needs no finiteness. The
structure map is local and `L` is the fraction field of the integral closure, so the extension is
one of strictly henselian discrete valuation rings in the expected sense. -/
@[sga "6 X 7.13.3" "strictly henselian base", sga "6 X 7.16" "special case"]
theorem isDiscreteValuationRing_strictlyHenselian_integralClosure :
    IsDiscreteValuationRing (integralClosure A L) ∧
      StrictlyHenselianLocalRing (integralClosure A L) ∧
      IsLocalHom (algebraMap A (integralClosure A L)) ∧
      IsFractionRing (integralClosure A L) L :=
  ⟨Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure A K L,
    strictlyHenselianLocalRing_integralClosure A L,
    isLocalHom_algebraMap_integralClosure_of_strictlyHenselian A L,
    Stacks.DiscreteValuationRing.Ramification.isFractionRing_integralClosure A K L⟩

include K in
/-- The separable case of `isDiscreteValuationRing_strictlyHenselian_integralClosure`, with the
module-finiteness of the integral closure over the base (Stacks 032L) added: this is the form in
which a finite separable extension of a strictly henselian discrete valuation ring is again one.
-/
@[sga "6 X 7.13.3" "special case"]
theorem isDiscreteValuationRing_strictlyHenselian_module_finite_integralClosure
    [Algebra.IsSeparable K L] :
    IsDiscreteValuationRing (integralClosure A L) ∧
      StrictlyHenselianLocalRing (integralClosure A L) ∧
      IsLocalHom (algebraMap A (integralClosure A L)) ∧
      IsFractionRing (integralClosure A L) L ∧
      Module.Finite A (integralClosure A L) :=
  ⟨Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure A K L,
    strictlyHenselianLocalRing_integralClosure A L,
    isLocalHom_algebraMap_integralClosure_of_strictlyHenselian A L,
    Stacks.DiscreteValuationRing.Ramification.isFractionRing_integralClosure A K L,
    Stacks.DiscreteValuationRing.Ramification.module_finite_integralClosure A K L⟩

end DiscreteValuationRing

end Stacks.Henselian

end
