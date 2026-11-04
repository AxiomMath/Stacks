module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings of schemes of finite type over a complete local ring

Let `R` be a Noetherian complete local ring and `X` a scheme locally of finite type over
`Spec R`. A Noetherian complete local ring is excellent ([Stacks, Tag 07QW]), and excellence
passes to algebras essentially of finite type ([Stacks, Tag 07QU]); the local rings of `X` are
essentially of finite type over the local rings of `Spec R`, which are localizations of `R`, so
they are excellent. Consequently they are Nagata rings ([Stacks, Tag 07QV]), and the completion
of a normal one is a normal domain: an excellent ring is a G-ring, so the map to its completion
is regular ([Stacks, Tag 0AH2]), and normality ascends along regular maps.

These facts are used in the inductive step of the proof of [Stacks, Tag 0BGN], where `X` is a
normal modification of the spectrum of a complete local domain.

## Main results

* `AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent`: the local rings of
  a scheme locally of finite type over an excellent ring are excellent.
* `AlgebraicGeometry.isNormalDomain_adicCompletion_of_isExcellent`: the completion of an excellent
  normal local ring is a normal domain.
* `AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isPrecomplete`: the local rings
  of a scheme locally of finite type over a Noetherian complete local ring are excellent.
* `AlgebraicGeometry.isNagataRing_stalk_of_locallyOfFiniteType_of_isPrecomplete`: they are
  Nagata rings.
* `AlgebraicGeometry.isNormalDomain_adicCompletion_stalk_of_locallyOfFiniteType`: the completion
  of such a local ring at its maximal ideal is a normal domain as soon as the local ring is
  normal.

## Implementation notes

Completeness enters only through precompleteness, which is all that [Stacks, Tag 07QW] uses.

## References

* [Stacks Project, Tag 07QW](https://stacks.math.columbia.edu/tag/07QW)
* [Stacks Project, Tag 07QU](https://stacks.math.columbia.edu/tag/07QU)
* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Excellence ascends along algebras essentially of finite type. -/
private theorem isExcellent_of_essFiniteType {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] (h : IsExcellent A) : IsExcellent B :=
  (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 h

/-- **The local rings of a scheme locally of finite type over an excellent ring are
excellent.** The local rings of the base are localizations of it, and the local rings of the
scheme are essentially of finite type over those ([Stacks, Tag 07QU]). -/
@[ega "IV 7.8.3" "(ii), special case"]
theorem isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent (R : Type u) [CommRing R]
    (hR : IsExcellent R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (x : X) : IsExcellent (X.presheaf.stalk x) := by
  let q := f.base x
  have : q.asIdeal.IsPrime := q.isPrime
  -- the local ring of the base at the image of `x` is a localization of `R`
  have hloc : IsExcellent (Localization.AtPrime q.asIdeal) := by
    have : Algebra.EssFiniteType R (Localization.AtPrime q.asIdeal) :=
      Algebra.EssFiniteType.of_isLocalization _ q.asIdeal.primeCompl
    exact isExcellent_of_essFiniteType hR
  have hbase : IsExcellent ((Spec (.of R)).presheaf.stalk q) := by
    let e := (Spec.stalkIso (.of R) q).commRingCatIsoToRingEquiv.symm
    let : Algebra (Localization.AtPrime q.asIdeal) ((Spec (.of R)).presheaf.stalk q) :=
      e.toRingHom.toAlgebra
    have : Algebra.EssFiniteType (Localization.AtPrime q.asIdeal)
        ((Spec (.of R)).presheaf.stalk q) := by
      rw [← RingHom.essFiniteType_algebraMap]
      exact (RingHom.FiniteType.of_surjective _ e.surjective).essFiniteType
    exact isExcellent_of_essFiniteType hloc
  -- the local ring of `X` is essentially of finite type over it
  algebraize [(f.stalkMap x).hom]
  have hess : Algebra.EssFiniteType ((Spec (.of R)).presheaf.stalk q) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  exact isExcellent_of_essFiniteType hbase

/-- **The local rings of a scheme locally of finite type over a Noetherian complete local ring
are excellent.** The base is excellent ([Stacks, Tag 07QW]). -/
@[ega "IV 7.8.3" "more general"]
theorem isExcellent_stalk_of_locallyOfFiniteType_of_isPrecomplete (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (maximalIdeal R) R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (x : X) :
    IsExcellent (X.presheaf.stalk x) :=
  isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent R
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 R) f x

/-- **The local rings of a scheme locally of finite type over a Noetherian complete local ring
are Nagata rings**, being excellent ([Stacks, Tag 07QV]). -/
theorem isNagataRing_stalk_of_locallyOfFiniteType_of_isPrecomplete (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (maximalIdeal R) R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (x : X) :
    IsNagataRing (X.presheaf.stalk x) :=
  isNagataRing_of_isQuasiExcellent
    (isExcellent_stalk_of_locallyOfFiniteType_of_isPrecomplete R f x).1

/-- **The completion of an excellent normal local ring is a normal domain.** An excellent ring
is a G-ring, so the map to its completion is regular ([Stacks, Tag 0AH2]); normality ascends
along a regular map, and a normal local ring is a domain. -/
@[ega "IV 2.3.9" "special case", ega "IV 7.8.3" "(v), special case"]
theorem isNormalDomain_adicCompletion_of_isExcellent (A : Type u) [CommRing A] [IsLocalRing A]
    (hexc : IsExcellent A) (hA : IsNormalRing A) :
    IsNormalDomain (AdicCompletion (maximalIdeal A) A) := by
  have : IsNoetherianRing A := hexc.1.1
  have hreg : IsRegularRingHom (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
    isRegularRingHom_algebraMap_adicCompletion hexc.1.2.1 _
  rw [isRegularRingHom_iff_of_eq_algebraMap _ rfl] at hreg
  obtain ⟨hdomain, hclosed⟩ := (isNormalRing_of_flat_of_isGeometricallyRegular_fiber A
    (AdicCompletion (maximalIdeal A) A) hA fun q _ => (hreg.2 q).2).of_isLocalRing
  exact ⟨hdomain, hclosed⟩

/-- **The completion of a normal local ring of a scheme locally of finite type over a Noetherian
complete local ring is a normal domain**, the local ring being excellent. -/
@[sga "4 XV 3.4" "special case"]
theorem isNormalDomain_adicCompletion_stalk_of_locallyOfFiniteType (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (maximalIdeal R) R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (x : X)
    (hx : IsNormalRing (X.presheaf.stalk x)) :
    IsNormalDomain (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
  isNormalDomain_adicCompletion_of_isExcellent _
    (isExcellent_stalk_of_locallyOfFiniteType_of_isPrecomplete R f x) hx

end AlgebraicGeometry

end
