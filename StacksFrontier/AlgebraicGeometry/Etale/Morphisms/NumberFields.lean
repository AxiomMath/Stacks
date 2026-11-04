module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.RingHom.Unramified
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Unramified

/-!
# Agreement of the two notions of unramifiedness for number fields

For an extension of number fields, scheme-theoretic unramifiedness of the induced map on
spectra of the rings of integers agrees, at a nonzero prime, with the classical condition:
ramification index one together with a separable residue field extension. At the generic point
the map is unramified, and the extension of fraction fields is separable.

## Main definitions

* `AlgebraicGeometry.ringOfIntegersSpecMap` is the morphism of spectra induced by the map on
  rings of integers.

## Main results

* `AlgebraicGeometry.unramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable` gives the
  agreement at a nonzero prime.
* `AlgebraicGeometry.unramifiedAt_genericPoint` gives unramifiedness at the generic point.
* `Algebra.isUnramifiedAt_bot` gives the conventional generic-point assertion.

## Implementation notes

The classical condition retains both the ramification-index and residue-separability clauses,
even though residue fields of nonzero primes of rings of integers are finite and hence the
second clause is automatic. The finiteness needed to form
`AlgebraicGeometry.StalkwiseUnramifiedAt` is installed from the integral-closure description of
rings of integers.

## References

* [The Stacks Project, Tag 024Z](https://stacks.math.columbia.edu/tag/024Z)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

open NumberField

universe u

noncomputable section

/-- The morphism of spectra induced by an extension of rings of integers. -/
abbrev ringOfIntegersSpecMap (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] :
    Spec (.of (RingOfIntegers L)) ⟶ Spec (.of (RingOfIntegers K)) :=
  Scheme.Spec.map
    (CommRingCat.ofHom (algebraMap (RingOfIntegers K) (RingOfIntegers L))).op

/-- On the spectrum of a ring, stalkwise unramifiedness of a morphism induced by an algebra map
is unramifiedness of the algebra at the corresponding prime. -/
private theorem specMap_stalk_unramified_iff
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocallyNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of R)))]
    [LocallyOfFiniteType (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)]
    (q : PrimeSpectrum S) :
    StalkwiseUnramifiedAt
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op) q ↔
      Algebra.IsUnramifiedAt R q.asIdeal := by
  let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let p : Ideal R := q.asIdeal.under R
  let Q : Ideal S := q.asIdeal
  have : Q.IsPrime := q.isPrime
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver p Q
  let : Localization.AtPrime.IsLiesOverAlgebra p Q := inferInstance
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime Q)
  · let := (Scheme.Spec.map f.op).stalkMap q |>.hom.toAlgebra
    rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (R := CommRingCat.of R) (S := CommRingCat.of S) f q)
  exact ⟨fun _ ↦ Algebra.FormallyUnramified.comp R (Localization.AtPrime p)
      (Localization.AtPrime Q),
    fun _ ↦ Algebra.FormallyUnramified.of_restrictScalars R (Localization.AtPrime p)
      (Localization.AtPrime Q)⟩

/-- For rings of integers, stalkwise unramifiedness at a prime is unramifiedness of the algebra
at that prime. -/
private theorem stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (q : PrimeSpectrum (RingOfIntegers L)) :
    letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
      IsIntegralClosure.finite (RingOfIntegers K) K L (RingOfIntegers L)
    letI : IsFinite (ringOfIntegersSpecMap K L) := (IsFinite.SpecMap_iff _).2
      (IsIntegralClosure.finite (RingOfIntegers K) K L (RingOfIntegers L))
    letI : LocallyOfFiniteType (ringOfIntegersSpecMap K L) := inferInstance
    StalkwiseUnramifiedAt (ringOfIntegersSpecMap K L) q ↔
      Algebra.IsUnramifiedAt (RingOfIntegers K) q.asIdeal := by
  let : IsFinite (ringOfIntegersSpecMap K L) := (IsFinite.SpecMap_iff _).2
    (IsIntegralClosure.finite (RingOfIntegers K) K L (RingOfIntegers L))
  let : LocallyOfFiniteType (ringOfIntegersSpecMap K L) := inferInstance
  let : IsLocallyNoetherian
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of (RingOfIntegers K)))) :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of (RingOfIntegers K))).2 inferInstance
  exact specMap_stalk_unramified_iff (R := RingOfIntegers K) (S := RingOfIntegers L) q

/-- **Stacks Project, Tag 024Z.** At a nonzero prime of the larger ring of integers,
scheme-theoretic unramifiedness is equivalent to ramification index one together with
separability of the residue extension. -/
@[stacks 024Z "agreement_of_unramifiedness"]
theorem unramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (q : PrimeSpectrum (RingOfIntegers L)) (hq : q.asIdeal ≠ ⊥) :
    letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
      IsIntegralClosure.finite (RingOfIntegers K) K L (RingOfIntegers L)
    letI : IsFinite (ringOfIntegersSpecMap K L) := (IsFinite.SpecMap_iff _).2
      (IsIntegralClosure.finite (RingOfIntegers K) K L (RingOfIntegers L))
    letI : LocallyOfFiniteType (ringOfIntegersSpecMap K L) := inferInstance
    StalkwiseUnramifiedAt (ringOfIntegersSpecMap K L) q ↔
      (letI := Localization.AtPrime.algebraOfLiesOver
          (q.asIdeal.under (RingOfIntegers K)) q.asIdeal
       Ideal.ramificationIdx q.asIdeal (RingOfIntegers K) = 1 ∧
        Algebra.IsSeparable (q.asIdeal.under (RingOfIntegers K)).ResidueField
          q.asIdeal.ResidueField) := by
  let p := q.asIdeal.under (RingOfIntegers K)
  let : Finite (RingOfIntegers K ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.under_ne_bot _ hq)
  let : PerfectField p.ResidueField := inferInstance
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  let : Localization.AtPrime.IsLiesOverAlgebra p q.asIdeal := inferInstance
  rw [stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff K L q]
  refine ⟨fun h ↦ ?_, fun h ↦ (Ideal.ramificationIdx_eq_one_iff (q := q.asIdeal)).1 h.1⟩
  have : Algebra.IsUnramifiedAt (RingOfIntegers K) q.asIdeal := h
  exact ⟨(Ideal.ramificationIdx_eq_one_iff (q := q.asIdeal)).2 h, inferInstance⟩

/-- **Stacks Project, Tag 024Z.** The morphism on spectra of rings of integers is unramified at
the generic point. -/
@[stacks 024Z "agreement_of_unramifiedness"]
theorem unramifiedAt_genericPoint
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L] :
    letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
      IsIntegralClosure.finite (RingOfIntegers K) K L (RingOfIntegers L)
    letI : IsFinite (ringOfIntegersSpecMap K L) := (IsFinite.SpecMap_iff _).2
      (IsIntegralClosure.finite (RingOfIntegers K) K L (RingOfIntegers L))
    letI : LocallyOfFiniteType (ringOfIntegersSpecMap K L) := inferInstance
    StalkwiseUnramifiedAt (ringOfIntegersSpecMap K L)
      (⟨⊥, inferInstance⟩ : PrimeSpectrum (RingOfIntegers L)) := by
  exact (stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff K L _).2 Algebra.isUnramifiedAt_bot

add_to_stacks 024Z "agreement_of_unramifiedness" Algebra.isUnramifiedAt_bot

end

end AlgebraicGeometry
