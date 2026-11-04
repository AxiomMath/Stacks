module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalProperties.Basic
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal catenarity and local rings

A locally Noetherian scheme is universally catenary if and only if all of its local rings are
universally catenary.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyCatenary_iff_stalk_isUniversallyCatenary`
  characterizes universal catenarity of a locally Noetherian scheme in terms of its local
  rings.

## Implementation notes

The local ring of a scheme `S` at `s` is represented by `S.presheaf.stalk s`. Universal
catenarity of the scheme is `AlgebraicGeometry.Scheme.IsUniversallyCatenary`, while universal
catenarity of each local ring is `Ring.IsUniversallyCatenary`.

Both directions go through the affine-local criterion
`AlgebraicGeometry.Scheme.isUniversallyCatenary_iff_forall_affineOpens` and the fact that the
stalk at a point of an affine open is a localization of the ring of sections at the
corresponding prime. The two ring-theoretic ingredients are that a localization of a
universally catenary ring is universally catenary, and conversely that a ring is universally
catenary as soon as all of its localizations at primes are. The second is phrased with an
auxiliary structure, so that the localization may be presented by any ring satisfying
`IsLocalization.AtPrime` rather than by `Localization.AtPrime` itself.

## References

* [Stacks Project, Tag 02JA](https://stacks.math.columbia.edu/tag/02JA)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IrreducibleClosedsCodim

namespace AlgebraicGeometry.Scheme

universe u

/-- A localization of a universally catenary ring is universally catenary. -/
@[ega "IV 10.7.2" "more general", ega "IV 5.6.3" "more general"]
private theorem ringIsUniversallyCatenary_of_isLocalization {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : Ring.IsUniversallyCatenary R) : Ring.IsUniversallyCatenary S := by
  intro C _ _ _
  let : Algebra R C := ((algebraMap S C).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := Algebra.EssFiniteType.of_isLocalization S M
  have : Algebra.EssFiniteType S C := Algebra.EssFiniteType.of_finiteType S C
  have : Algebra.EssFiniteType R C := Algebra.EssFiniteType.comp R S C
  obtain ⟨B, T, _, _⟩ := (Algebra.essFiniteType_iff_exists_subalgebra R C).mp inferInstance
  exact ringIsCatenary_of_isLocalization T (hR B)

/-- A presentation of the localization of `R` at a prime `p` by a universally catenary ring.

This packages the data needed to witness universal catenarity of `R` locally at `p`: a ring
realizing the localization at `p`, together with its universal catenarity. -/
private structure UniversalCatenarityAtPrime (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] where
  /-- The ring realizing the localization at `p`. -/
  carrier : Type u
  /-- Its commutative ring structure. -/
  commRing : CommRing carrier
  /-- Its `R`-algebra structure. -/
  algebra : Algebra R carrier
  /-- It is the localization of `R` at `p`. -/
  localization : @IsLocalization.AtPrime R _ carrier _ algebra p inferInstance
  /-- It is universally catenary. -/
  universallyCatenary : @Ring.IsUniversallyCatenary carrier commRing

/-- A ring all of whose localizations at primes are universally catenary is universally
catenary. -/
@[ega "IV 5.6.3" "(i)", ega "IV 7.8.2" "Direction"]
private theorem ringIsUniversallyCatenary_of_forall_primeLocalization {R : Type u}
    [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime], UniversalCatenarityAtPrime R p) :
    Ring.IsUniversallyCatenary R := by
  intro C _ _ hC
  apply ringIsCatenary_of_forall_primeLocalization (R := C)
  intro n hn T _ _ _
  let p : Ideal R := n.comap (algebraMap R C)
  let N : Submonoid C := Submonoid.map (algebraMap R C) p.primeCompl
  let C' := Localization N
  obtain ⟨T₀, _, _, _, hT₀UC⟩ := hR p
  let : Algebra T₀ C' :=
    (IsLocalization.map C' (algebraMap R C) (Submonoid.le_comap_map p.primeCompl)).toAlgebra
  have : Algebra.FiniteType T₀ C' :=
    RingHom.finiteType_localizationPreserves (algebraMap R C) p.primeCompl T₀ C'
      (RingHom.finiteType_algebraMap.mpr hC)
  have hle : N ≤ n.primeCompl := fun _ ⟨_, ha, h⟩ => h ▸ ha
  let : Algebra C' T := IsLocalization.localizationAlgebraOfSubmonoidLe C' T N n.primeCompl hle
  have : IsScalarTower C C' T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le C' T N n.primeCompl hle
  have : IsLocalization (Submonoid.map (algebraMap C C') n.primeCompl) T :=
    IsLocalization.isLocalization_of_submonoid_le C' T N n.primeCompl hle
  exact ringIsCatenary_of_isLocalization
    (Submonoid.map (algebraMap C C') n.primeCompl) (hT₀UC C')

/-- A locally Noetherian scheme is universally catenary if and only if each of its local rings
is universally catenary. -/
@[stacks 02JA, ega "IV 5.6.3"]
theorem isUniversallyCatenary_iff_stalk_isUniversallyCatenary
    (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsUniversallyCatenary S ↔
      ∀ s : S, Ring.IsUniversallyCatenary (S.presheaf.stalk s) := by
  refine ⟨fun hS s => ?_, fun hStalk => ?_⟩
  · obtain ⟨_, ⟨U, hU, rfl⟩, hsU, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    let : Algebra Γ(S, U) (S.presheaf.stalk s) :=
      TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨s, hsU⟩
    have : IsLocalization.AtPrime (S.presheaf.stalk s) (hU.primeIdealOf ⟨s, hsU⟩).asIdeal :=
      hU.isLocalization_stalk ⟨s, hsU⟩
    exact ringIsUniversallyCatenary_of_isLocalization
      ((hU.primeIdealOf ⟨s, hsU⟩).asIdeal.primeCompl)
      ((isUniversallyCatenary_iff_forall_affineOpens S).mp hS ⟨U, hU⟩)
  · apply (isUniversallyCatenary_iff_forall_affineOpens S).mpr
    intro U
    apply ringIsUniversallyCatenary_of_forall_primeLocalization
    intro p hp
    let y : PrimeSpectrum Γ(S, U) := ⟨p, hp⟩
    let xU : U.1 := U.2.isoSpec.inv y
    let x : S := xU.1
    let : Algebra Γ(S, U.1) (S.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x, xU.2⟩
    exact ⟨S.presheaf.stalk x, inferInstance, inferInstance, U.2.isLocalization_stalk' y xU.2,
      hStalk x⟩

end AlgebraicGeometry.Scheme
