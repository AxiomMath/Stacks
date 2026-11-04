module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.Catenary.Universes
public import StacksFrontier.RingTheory.Excellent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal catenarity is local, and the rings essentially of finite type over a field

## Main results

* `Ring.IsUniversallyCatenary.of_field`: a field is universally catenary.
* `Ring.IsUniversallyCatenary.of_localization_atPrime`: a ring all of whose localizations at
  prime ideals are universally catenary is universally catenary.
* `Ring.IsUniversallyCatenary.of_essFiniteType`: an algebra essentially of finite type over a
  Noetherian universally catenary ring is universally catenary.
* `Ring.IsUniversallyCatenary.of_forall_essFiniteType_field`: a ring each of whose local rings
  is essentially of finite type over a field is universally catenary.
* `Algebra.EssFiniteType.exists_field_essFiniteType_localization`: that condition on the local
  rings ascends along essentially finite type algebras.
-/

@[expose] public section

universe u

namespace Ring.IsUniversallyCatenary

/-- **A field is universally catenary.** -/
theorem of_field (k : Type u) [Field k] : Ring.IsUniversallyCatenary k :=
  ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k).2

/-- **Universal catenarity is local on the spectrum.** A ring all of whose localizations at prime
ideals are universally catenary is universally catenary. -/
@[ega "IV 5.6.3" "(i)", ega "IV 7.8.2" "Direction"]
theorem of_localization_atPrime {R : Type u} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime], Ring.IsUniversallyCatenary (Localization.AtPrime p)) :
    Ring.IsUniversallyCatenary R := by
  intro C _ _ hC
  apply AlgebraicGeometry.ringIsCatenary_of_forall_primeLocalization (R := C)
  intro n hn T _ _ _
  let p : Ideal R := n.comap (algebraMap R C)
  have hp : p.IsPrime := hn.comap _
  let N : Submonoid C := Submonoid.map (algebraMap R C) p.primeCompl
  let C' := Localization N
  let : Algebra (Localization.AtPrime p) C' :=
    (IsLocalization.map C' (algebraMap R C) (Submonoid.le_comap_map p.primeCompl)).toAlgebra
  have : Algebra.FiniteType (Localization.AtPrime p) C' :=
    RingHom.finiteType_localizationPreserves (algebraMap R C) p.primeCompl
      (Localization.AtPrime p) C' (RingHom.finiteType_algebraMap.mpr hC)
  have hle : N ≤ n.primeCompl := Submonoid.map_le_iff_le_comap.mpr fun _ ha => ha
  let : Algebra C' T := IsLocalization.localizationAlgebraOfSubmonoidLe C' T N n.primeCompl hle
  have : IsScalarTower C C' T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le C' T N n.primeCompl hle
  have : IsLocalization (Submonoid.map (algebraMap C C') n.primeCompl) T :=
    IsLocalization.isLocalization_of_submonoid_le C' T N n.primeCompl hle
  exact AlgebraicGeometry.ringIsCatenary_of_isLocalization
    (Submonoid.map (algebraMap C C') n.primeCompl) (hR p C')

/-- **A ring essentially of finite type over a Noetherian universally catenary ring is
universally catenary.** -/
@[ega "IV 10.7.2" "more general", ega "IV 5.6.3"]
theorem of_essFiniteType {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.EssFiniteType A B] (hA : Ring.IsUniversallyCatenary A) :
    Ring.IsUniversallyCatenary B := by
  obtain ⟨B₀, M, hB₀, hM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra A B).mp inferInstance
  have : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing A B₀
  exact Ring.IsUniversallyCatenary.localization M B
    (Ring.IsUniversallyCatenary.of_finiteType (C := B₀) hA)

/-- **A ring that is, locally on its spectrum, essentially of finite type over a field is
universally catenary.** If every localization `R_p` of `R` at a prime is essentially of finite
type over some field, then `R` is universally catenary. -/
theorem of_forall_essFiniteType_field {R : Type u} [CommRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime], ∃ (K : Type u) (_ : Field K)
      (_ : Algebra K (Localization.AtPrime p)), Algebra.EssFiniteType K (Localization.AtPrime p)) :
    Ring.IsUniversallyCatenary R := by
  refine of_localization_atPrime fun p _ => ?_
  obtain ⟨K, _, _, _⟩ := h p
  exact of_essFiniteType (of_field K)

end Ring.IsUniversallyCatenary

/-- **Being locally essentially of finite type over a field ascends along essentially finite type
algebras.** If every localization of `R` at a prime is essentially of finite type over some
field, and `S` is an essentially finite type `R`-algebra, then every localization of `S` at a
prime is essentially of finite type over some field. -/
theorem Algebra.EssFiniteType.exists_field_essFiniteType_localization {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (h : ∀ (p : Ideal R) [p.IsPrime], ∃ (K : Type u) (_ : Field K)
      (_ : Algebra K (Localization.AtPrime p)), Algebra.EssFiniteType K (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra K (Localization.AtPrime q)),
      Algebra.EssFiniteType K (Localization.AtPrime q) := by
  let p : Ideal R := q.comap (algebraMap R S)
  have : p.IsPrime := Ideal.comap_isPrime _ q
  have : q.LiesOver p := ⟨rfl⟩
  obtain ⟨K, _, _, _⟩ := h p
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType R (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp R S (Localization.AtPrime q)
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R _ _
  let : Algebra K (Localization.AtPrime q) :=
    ((algebraMap (Localization.AtPrime p) (Localization.AtPrime q)).comp
      (algebraMap K (Localization.AtPrime p))).toAlgebra
  have : IsScalarTower K (Localization.AtPrime p) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨K, inferInstance, inferInstance,
    Algebra.EssFiniteType.comp K (Localization.AtPrime p) (Localization.AtPrime q)⟩
