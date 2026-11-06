module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs

@[expose] public section

/-!
# Branches of a local ring

A local ring is *unibranch* when its reduction is a domain and the normalization of that
reduction in its fraction field is local. It is *geometrically unibranch* when, in addition,
the induced extension of residue fields is purely inseparable.

Quantitatively, the number of branches of a local ring is the number of minimal primes of a
henselization; replacing the henselization by a strict henselization gives the number of
geometric branches. Both invariants take values in the extended natural numbers, so an
infinite set of minimal primes has value infinity.

## Main definitions

* `IsUnibranch`: the reduction is a domain and its normalization is local.
* `IsGeometricallyUnibranch`: a unibranch local ring whose normalization has a purely
  inseparable residue-field extension.
* `numberOfBranches`: the number of minimal primes of a henselization.
* `numberOfGeometricBranches`: the number of minimal primes of a strict henselization.

## Implementation notes

The reduction of `A` is represented by `A ⧸ nilradical A`, and its normalization by
`integralClosure (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))`. In the geometric
condition, the residue-field map is induced by the canonical composite from `A` to this
normalization. This composite is local because the quotient map is surjective and the map from
the reduced local domain to its local integral closure is local.

Henselizations are supplied as local algebras satisfying `IsLocalRing.IsHenselization`. A strict
henselization is the same notion with residue field a separable closure. Cardinality is measured
by `Set.encard`, whose value is infinity exactly when the set is infinite.

## References

* [Grothendieck and Dieudonné, *Éléments de géométrie algébrique IV*][EGA4],
  Chapter 0, 23.2.1
* [The Stacks Project, Tag 0BPZ](https://stacks.math.columbia.edu/tag/0BPZ)
* [The Stacks Project, Tag 0C26](https://stacks.math.columbia.edu/tag/0C26)
-/

universe u v

open IsLocalRing

/-- A local ring is unibranch if its reduction is a domain and the integral closure of its
reduction in its field of fractions is local. -/
@[stacks 0BPZ "(1)", ega "0 23.2.1" "def. of unibranch", ega "III 4.3.6" "unibranch local ring"]
def IsUnibranch (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  let Ared := A ⧸ nilradical A
  IsDomain Ared ∧
    IsLocalRing (integralClosure Ared (FractionRing Ared))

/-- A local ring is geometrically unibranch if it is unibranch and the residue field of the
normalization of its reduction is purely inseparable over its residue field. -/
@[stacks 0BPZ "(2)", ega "0 23.2.1" "def. of geom. unibranch"]
noncomputable def IsGeometricallyUnibranch
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  IsUnibranch A ∧
    let Ared := A ⧸ nilradical A
    let A' := integralClosure Ared (FractionRing Ared)
    ∀ (hred : IsDomain Ared) (hlocal : IsLocalRing A'),
      letI := hred
      letI := hlocal
      letI : IsLocalRing Ared :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      letI : IsLocalHom (Ideal.Quotient.mk (nilradical A)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      let f : A →+* A' :=
        (algebraMap Ared A').comp (Ideal.Quotient.mk (nilradical A))
      letI : IsLocalHom f := by
        let g : Ared →+* A' := algebraMap _ _
        have hg : IsLocalHom g := by
          apply ((IsLocalRing.local_hom_TFAE g).out 5 1).mp
          exact (maximal_ideal_unique Ared).unique
            (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal A')) inferInstance
        exact RingHom.isLocalHom_comp _ _
      (ResidueField.map f).IsPurelyInseparable

/-- The number of branches of a local ring is the extended-natural cardinality of the set of
minimal primes of a henselization. -/
@[stacks 0C26 "number of branches"]
noncomputable def numberOfBranches (A Ah : Type u) [CommRing A] [IsLocalRing A]
    [CommRing Ah]
    [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah] : ℕ∞ :=
  (minimalPrimes Ah).encard

/-- The number of geometric branches of a local ring is the extended-natural cardinality of the
set of minimal primes of a strict henselization. -/
@[stacks 0C26 "number of geometric branches"]
noncomputable def numberOfGeometricBranches (A : Type u) (ksep : Type v) (Ash : Type u)
    [CommRing A] [IsLocalRing A] [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep] [CommRing Ash] [IsLocalRing Ash]
    [Algebra A Ash] [IsLocalRing.IsHenselization A ksep Ash] : ℕ∞ :=
  (minimalPrimes Ash).encard
