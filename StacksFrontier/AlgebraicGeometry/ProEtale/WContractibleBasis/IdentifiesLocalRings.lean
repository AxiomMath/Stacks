module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.Bijective
public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings
public import StacksCore.Tactic.StacksAttribute

/-!
# Permanence properties of ring maps that identify local rings

`Algebra.IdentifiesLocalRings`, defined in
`StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings`, says of an algebra `A → B` that for every
prime `q` of `B` the canonical map `A_{q ∩ A} → B_q` between localizations is bijective. This file
records which algebras have that property and how it propagates along towers. It is the companion
of the local isomorphism property: a local isomorphism identifies local rings, but not conversely.

## Main results

* `Algebra.IdentifiesLocalRings.bijective_localRingHom`: the defining bijection, read off at an
  arbitrary spelling of the prime of the source.
* `Algebra.IdentifiesLocalRings.of_isLocalization`: a localization identifies local rings.
* `Algebra.IdentifiesLocalRings.of_isStandardOpenImmersion`: a standard open immersion identifies
  local rings.
* `Algebra.IdentifiesLocalRings.of_isLocalIso`: a local isomorphism identifies local rings.
* `Algebra.IdentifiesLocalRings.trans`: a composition of two ring maps identifying local rings
  identifies local rings.
* `Algebra.identifiesLocalRings_iff_stalkwise`: the property is exactly bijectivity of every stalk
  map of the induced morphism of affine schemes.

## Implementation notes

`Algebra.IdentifiesLocalRings` is a plain `Prop`-valued statement, not a class, so every result
here takes the properties it assumes as explicit arguments; the class in this area is Mathlib's
`Algebra.IsLocalIso`, which carries the other clause of the same source definition.

The defining condition fixes the prime of the source at `q.comap (algebraMap R S)`, whereas
`Localization.localRingHom` accepts any prime of the source together with a proof that it is the
contraction. `Algebra.IdentifiesLocalRings.bijective_localRingHom` recovers that flexibility, and
the tower arguments below need it: a form fixed at `q.comap (algebraMap R S)` would force a
transport along `Ideal.comap_comap` inside the type `Localization.AtPrime _`.

The comparison map is `Localization.localRingHom` and the condition imposed on it is
`Function.Bijective` rather than invertibility of a morphism of `CommRingCat`. With that spelling
the property is literally `AlgebraicGeometry.stalkwise (fun f ↦ Function.Bijective f)` applied to
`Spec.map` of the structure map, by `AlgebraicGeometry.stalkwise_SpecMap_iff`; that comparison is
recorded as `Algebra.identifiesLocalRings_iff_stalkwise`. `Function.Bijective` is also the shape in
which Mathlib states the meta-properties of this class of ring maps, as in
`RingHom.Bijective.respectsIso`.

The carriers are `CommSemiring`, as for `Algebra.IsLocalIso`. The comparison with `stalkwise` is
stated for `CommRing`s in a single universe, since `AlgebraicGeometry.stalkwise` quantifies over
ring homomorphisms between carriers in one fixed universe.

## References

* [Stacks Project, Tag 096G](https://stacks.math.columbia.edu/tag/096G)
* [Stacks Project, Tag 096H](https://stacks.math.columbia.edu/tag/096H)
* [Stacks Project, Tag 096I](https://stacks.math.columbia.edu/tag/096I)
-/

@[expose] public section

universe u

namespace Algebra.IdentifiesLocalRings

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The defining bijection of an algebra that identifies local rings, at a prime `p` of the
source presented as an arbitrary ideal together with a proof that it is the contraction of the
prime `q` of the target, so that no transport is needed when it arises in another form. -/
public theorem bijective_localRingHom (hRS : Algebra.IdentifiesLocalRings R S) (p : Ideal R)
    [p.IsPrime] (q : Ideal S) [q.IsPrime] (h : p = q.comap (algebraMap R S)) :
    Function.Bijective (Localization.localRingHom p q (algebraMap R S) h) := by
  subst h
  exact hRS q

/-- A localization of `R` identifies local rings over `R`. -/
public theorem of_isLocalization (M : Submonoid R) [IsLocalization M S] :
    Algebra.IdentifiesLocalRings R S := by
  intro q _
  have : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (T := Localization.AtPrime q) q
  set p := q.comap (algebraMap R S)
  have he : Localization.localRingHom p q (algebraMap R S) rfl =
      (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
        (Localization.AtPrime q)).toRingEquiv.toRingHom := by
    refine Localization.localRingHom_unique _ _ _ _ fun x ↦ ?_
    simpa using IsScalarTower.algebraMap_apply R S (Localization.AtPrime q) x
  rw [he]
  exact (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Localization.AtPrime q)).bijective

/-- A standard open immersion identifies local rings. -/
public theorem of_isStandardOpenImmersion [Algebra.IsStandardOpenImmersion R S] :
    Algebra.IdentifiesLocalRings R S :=
  have ⟨r, _⟩ := Algebra.IsStandardOpenImmersion.exists_away R S
  of_isLocalization (Submonoid.powers r)

/-- The comparison map of a composite is the composite of the comparison maps. -/
private theorem localRingHom_eq_comp {T : Type*} [CommSemiring T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (r : Ideal T)
    [r.IsPrime] (hpq : p = q.comap (algebraMap R S)) (hqr : q = r.comap (algebraMap S T))
    (h : p = r.comap (algebraMap R T)) :
    Localization.localRingHom p r (algebraMap R T) h =
      (Localization.localRingHom q r (algebraMap S T) hqr).comp
        (Localization.localRingHom p q (algebraMap R S) hpq) := by
  rw [← Localization.localRingHom_comp]
  congr 1
  exact IsScalarTower.algebraMap_eq R S T

/-- A local isomorphism identifies local rings. -/
@[stacks 096I "(2)"]
public theorem of_isLocalIso [Algebra.IsLocalIso R S] : Algebra.IdentifiesLocalRings R S := by
  intro q hq
  suffices H : ∀ (p : Ideal R) [p.IsPrime] (h : p = q.comap (algebraMap R S)),
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) h) from H _ rfl
  intro p _ h
  obtain ⟨g, hgq, hg⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) (S := S) q
  set T := Localization.Away g
  have hd : Disjoint (Submonoid.powers g : Set S) (q : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hgq
  have hq' : (q.map (algebraMap S T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) T q hq hd
  have hcomap : (q.map (algebraMap S T)).comap (algebraMap S T) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) T hq hd
  have hpT : p = (q.map (algebraMap S T)).comap (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T, ← Ideal.comap_comap, hcomap, h]
  have hqT : q = (q.map (algebraMap S T)).comap (algebraMap S T) := hcomap.symm
  have hRT := bijective_localRingHom (of_isStandardOpenImmersion (R := R) (S := T)) p
    (q.map (algebraMap S T)) hpT
  have hST := bijective_localRingHom
    (of_isLocalization (R := S) (S := T) (Submonoid.powers g)) q (q.map (algebraMap S T)) hqT
  rw [localRingHom_eq_comp p q _ h hqT hpT] at hRT
  exact (Function.Bijective.of_comp_iff' hST _).mp hRT

section Tower

variable {T : Type*} [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- If `R → S` and `S → T` identify local rings, then so does `R → T`. -/
@[stacks 096G "(2)"]
public theorem trans (hRS : Algebra.IdentifiesLocalRings R S)
    (hST : Algebra.IdentifiesLocalRings S T) :
    Algebra.IdentifiesLocalRings R T := by
  intro r _
  suffices H : ∀ (p : Ideal R) [p.IsPrime] (h : p = r.comap (algebraMap R T)),
      Function.Bijective (Localization.localRingHom p r (algebraMap R T) h) from H _ rfl
  intro p _ h
  have hpq : p = (r.comap (algebraMap S T)).comap (algebraMap R S) := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, h]
  rw [localRingHom_eq_comp p _ r hpq rfl h]
  exact (bijective_localRingHom hST _ r rfl).comp (bijective_localRingHom hRS p _ hpq)

end Tower

end Algebra.IdentifiesLocalRings

open AlgebraicGeometry in
/-- Identifying local rings is exactly the condition that every stalk map of the induced morphism
of affine schemes is bijective. -/
public theorem Algebra.identifiesLocalRings_iff_stalkwise {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] :
    Algebra.IdentifiesLocalRings R S ↔
      stalkwise (fun f ↦ Function.Bijective f)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [stalkwise_SpecMap_iff RingHom.Bijective.respectsIso]
  exact ⟨fun H q hq ↦ @H q hq, fun H q hq ↦ H q hq⟩

end
