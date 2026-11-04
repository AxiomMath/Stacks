module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.LocalRingProperty
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.RingTheory.Nagata.Descent
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# Checking a local property of rings on every affine open

A property `P` of commutative rings that is local in the sense of
`CommRing.PropertyIsLocal` can be imposed on a scheme pointwise, by asking that every point
have an affine open neighbourhood whose ring of sections satisfies `P`
(`AlgebraicGeometry.IsLocally`). This file shows that this pointwise condition already implies
the corresponding condition on *every* affine open, and records the resulting list of equivalent
formulations together with stability under passing to an open subscheme.

Specialized to `IsNagataRing` and to `IsUniversallyJapaneseRing`, both of which are local
properties, this is the local characterization of Nagata schemes and of universally Japanese
schemes.

## Main results

* `AlgebraicGeometry.IsLocally.forall_affineOpens`: on a scheme locally satisfying `P` the ring
  of sections over every affine open satisfies `P`.
* `AlgebraicGeometry.isLocally_iff_forall_affineOpens`,
  `AlgebraicGeometry.isLocally_iff_exists_affineOpenCover`,
  `AlgebraicGeometry.isLocally_iff_exists_openCover`: the three equivalent reformulations.
* `AlgebraicGeometry.isLocally_open`: an open subscheme of a scheme locally satisfying `P` also
  locally satisfies `P`.
* `CommRing.isNagataRing_propertyIsLocal`: being a Nagata ring is a local property.
* `CommRing.isUniversallyJapaneseRing_propertyIsLocal`: being a universally Japanese ring is a
  local property.
* `isNagataScheme_tfae`, `isNagataScheme_open`: the local characterizations of Nagata schemes.
* `isUniversallyJapaneseScheme_tfae`, `isUniversallyJapaneseScheme_open`: the local
  characterizations of universally Japanese schemes.

## Implementation notes

The forward implication is the affine communication lemma
`AlgebraicGeometry.of_affine_open_cover`, whose two hypotheses are exactly the two fields of
`CommRing.PropertyIsLocal`: the sections over a basic open of an affine open are a localization
away from a single section, and the property descends from a finite family of basic opens whose
defining sections span the unit ideal. The descent field is phrased with the canonical model
`Localization.Away f` of the localization, so the geometric localization `Γ(X, X.basicOpen f)`
is transported to it along the canonical isomorphism of localizations; the transport itself is
`CommRing.PropertyIsLocal.of_ringEquiv`, which is the localization-away field applied to the
unit `1`.

Open covers are indexed families of opens whose supremum is the whole scheme, which is
`TopologicalSpace.IsOpenCover`; the indexing type may always be taken to be the scheme's own
point set, so it lives in the scheme's universe.

## References

* [Stacks Project, Tag 01OR](https://stacks.math.columbia.edu/tag/01OR)
* [Stacks Project, Tag 033W](https://stacks.math.columbia.edu/tag/033W)
* [Stacks Project, Tag 033X](https://stacks.math.columbia.edu/tag/033X)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace CommRing

variable {P : (R : Type u) → [CommRing R] → Prop}

/-- A local property of commutative rings is invariant under ring isomorphism: an isomorphism
exhibits the target as a localization of the source away from the unit `1`. -/
theorem PropertyIsLocal.of_ringEquiv (hP : PropertyIsLocal P) {R S : Type u}
    [CommRing R] [CommRing S] (e : R ≃+* S) (hR : P R) : P S := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have hbij : Function.Bijective (algebraMap R S) := e.bijective
  let : IsLocalization.Away (1 : R) S :=
    IsLocalization.away_of_isUnit_of_bijective S isUnit_one hbij
  exact hP.localizationAwayPreserves 1 S hR

/-- Being a Nagata ring is a local property of commutative rings: it passes to localizations
(Tag 032U) and descends along a principal open cover (Tag 032V). -/
theorem isNagataRing_propertyIsLocal :
    PropertyIsLocal (fun (R : Type u) [CommRing R] => IsNagataRing R) where
  localizationAwayPreserves {R} _ f S _ _ _ hR :=
    isNagata_of_isLocalization R (Submonoid.powers f) S hR
  ofLocalizationSpan {R} _ ι _ f hf hloc := by
    refine (isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan (Set.range f) hf
      (fun g => Localization.Away g.val)).2 ?_
    rintro ⟨r, i, rfl⟩
    exact hloc i

/-- Being universally Japanese is a local property of commutative rings: it passes to
localizations away from an element, because a localization away from an element is of finite
type and universal Japaneseness only constrains finite-type domains over the ring (Tag 032S),
and it descends along a principal open cover (Tag 032V). -/
@[ega "IV 7.7.2" "special case"]
theorem isUniversallyJapaneseRing_propertyIsLocal :
    PropertyIsLocal (fun (R : Type u) [CommRing R] => IsUniversallyJapaneseRing R) where
  localizationAwayPreserves {R} _ f S _ _ _ hR := by
    have : Algebra.FinitePresentation R S := IsLocalization.Away.finitePresentation f
    have hRS : Algebra.FiniteType R S := inferInstance
    refine { japanese := fun T _ _ _ _ => ?_ }
    let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.FiniteType R T := hRS.trans inferInstance
    exact hR.japanese T
  ofLocalizationSpan {R} _ ι _ f hf hloc := by
    refine (isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan (Set.range f) hf
      (fun g => Localization.Away g.val)).1 ?_
    rintro ⟨r, i, rfl⟩
    exact hloc i

end CommRing

namespace AlgebraicGeometry

variable {P : (R : Type u) → [CommRing R] → Prop} {X : Scheme.{u}}

/-- Every scheme locally satisfying `P` admits an affine open cover on whose rings of sections
`P` holds, indexed by the point set of the scheme. -/
private theorem exists_affineOpenCover_of_isLocally (P : (R : Type u) → [CommRing R] → Prop)
    (X : Scheme.{u}) (hX : IsLocally P X) :
    ∃ (ι : Type u) (U : ι → X.affineOpens),
      IsOpenCover (fun i ↦ (U i : X.Opens)) ∧ ∀ i, P Γ(X, (U i).1) := by
  classical
  choose U hUmem hUP using hX
  exact ⟨X, U, top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hUmem x⟩, hUP⟩

/-- On a scheme locally satisfying a local property `P` of commutative rings, the ring of
sections over *every* affine open satisfies `P`. -/
theorem IsLocally.forall_affineOpens (hP : CommRing.PropertyIsLocal P) (hX : IsLocally P X)
    (V : X.affineOpens) : P Γ(X, V.1) := by
  obtain ⟨ι, U, hcover, hUP⟩ := exists_affineOpenCover_of_isLocally P X hX
  induction V using of_affine_open_cover U hcover.iSup_eq_top with
  | basicOpen W f hW =>
    have := W.2.isLocalization_basicOpen f
    exact hP.localizationAwayPreserves f Γ(X, X.basicOpen f) hW
  | openCover W s hs h =>
    refine hP.ofLocalizationSpan (ι := {x // x ∈ s}) (fun g => g.1) (by simpa using hs) ?_
    intro g
    have := W.2.isLocalization_basicOpen g.1
    exact hP.of_ringEquiv (IsLocalization.algEquiv (Submonoid.powers g.1)
      Γ(X, X.basicOpen g.1) (Localization.Away g.1)).toRingEquiv (h g)
  | hU i => exact hUP i

/-- **Stacks Project, Tag 01OR (part (1) iff part (2)).** A scheme locally satisfies a local ring
property precisely when the ring of sections over every affine open satisfies it. -/
@[stacks 01OR "part (1) iff part (2)"]
theorem isLocally_iff_forall_affineOpens (hP : CommRing.PropertyIsLocal P) (X : Scheme.{u}) :
    IsLocally P X ↔ ∀ U : X.affineOpens, P Γ(X, U.1) := by
  refine ⟨fun hX => hX.forall_affineOpens hP, fun h x => ?_⟩
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  exact ⟨⟨W, hW⟩, hxW, h ⟨W, hW⟩⟩

/-- **Stacks Project, Tag 01OR (part (1) iff part (3)).** A scheme locally satisfies a ring
property precisely when it has an affine open cover on whose rings of sections the property
holds. -/
@[stacks 01OR "part (1) iff part (3)"]
theorem isLocally_iff_exists_affineOpenCover (P : (R : Type u) → [CommRing R] → Prop)
    (X : Scheme.{u}) :
    IsLocally P X ↔
      ∃ (ι : Type u) (U : ι → X.affineOpens),
        IsOpenCover (fun i ↦ (U i : X.Opens)) ∧ ∀ i, P Γ(X, (U i).1) := by
  refine ⟨exists_affineOpenCover_of_isLocally P X, ?_⟩
  rintro ⟨ι, U, hcover, hU⟩ x
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  exact ⟨U i, hxi, hU i⟩

/-- **Stacks Project, Tag 01OR (open subschemes).** Every open subscheme of a scheme locally
satisfying a local ring property also locally satisfies that property. -/
@[stacks 01OR "open subschemes"]
theorem isLocally_open (hP : CommRing.PropertyIsLocal P) (X : Scheme.{u}) (hX : IsLocally P X)
    (U : X.Opens) : IsLocally P U.toScheme := by
  rw [isLocally_iff_forall_affineOpens hP]
  intro V
  exact hP.of_ringEquiv (U.ι.appIso V.1).commRingCatIsoToRingEquiv
    (hX.forall_affineOpens hP ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩)

/-- **Stacks Project, Tag 01OR (part (1) iff part (4)).** A scheme locally satisfies a local ring
property precisely when it has an open cover by open subschemes locally satisfying the
property. -/
@[stacks 01OR "part (1) iff part (4)"]
theorem isLocally_iff_exists_openCover (hP : CommRing.PropertyIsLocal P) (X : Scheme.{u}) :
    IsLocally P X ↔
      ∃ (ι : Type u) (U : ι → X.Opens),
        IsOpenCover U ∧ ∀ i, IsLocally P (U i).toScheme := by
  refine ⟨fun hX => ⟨PUnit, fun _ => ⊤, by simp [IsOpenCover],
    fun _ => isLocally_open hP X hX ⊤⟩, ?_⟩
  rintro ⟨ι, U, hcover, hU⟩ x
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  obtain ⟨V, hxV, hPV⟩ := hU i ⟨x, hxi⟩
  exact ⟨⟨(U i).ι ''ᵁ V.1, V.2.image_of_isOpenImmersion (U i).ι⟩, ⟨⟨x, hxi⟩, hxV, rfl⟩, hPV⟩

end AlgebraicGeometry

/-- Being a Nagata scheme is locally satisfying the Nagata property of rings. -/
theorem isNagataScheme_iff_isLocally (X : Scheme.{u}) :
    IsNagataScheme X ↔ IsLocally (fun (R : Type u) [CommRing R] => IsNagataRing R) X :=
  Iff.rfl

/-- **Stacks Project, Tag 033X.** For a scheme `X`, being Nagata is equivalent to the section
ring of every affine open being Nagata, to this holding on some affine open covering, and to
admitting an open covering by Nagata open subschemes. -/
@[stacks 033X "equivalent conditions"]
theorem isNagataScheme_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsNagataScheme X,
      ∀ U : X.affineOpens, IsNagataRing Γ(X, (U : X.Opens)),
      ∃ (I : Type u) (U : I → X.affineOpens),
        IsOpenCover (fun i ↦ (U i : X.Opens)) ∧
          ∀ i, IsNagataRing Γ(X, (U i : X.Opens)),
      ∃ (I : Type u) (U : I → X.Opens),
        IsOpenCover U ∧ ∀ i, IsNagataScheme (U i).toScheme] := by
  tfae_have 1 ↔ 2 :=
    isLocally_iff_forall_affineOpens CommRing.isNagataRing_propertyIsLocal X
  tfae_have 1 ↔ 3 :=
    isLocally_iff_exists_affineOpenCover (fun (R : Type u) [CommRing R] => IsNagataRing R) X
  tfae_have 1 ↔ 4 :=
    isLocally_iff_exists_openCover CommRing.isNagataRing_propertyIsLocal X
  tfae_finish

/-- **Stacks Project, Tag 033X.** Every open subscheme of a Nagata scheme is Nagata. -/
@[stacks 033X "open subschemes"]
theorem isNagataScheme_open {X : Scheme.{u}} (hX : IsNagataScheme X) (U : X.Opens) :
    IsNagataScheme U.toScheme :=
  isLocally_open CommRing.isNagataRing_propertyIsLocal X hX U

/-- On a Nagata scheme the ring of sections over every affine open is a Nagata ring. -/
theorem IsNagataScheme.isNagataRing_sections {X : Scheme.{u}} (hX : IsNagataScheme X)
    (U : X.affineOpens) : IsNagataRing Γ(X, (U : X.Opens)) :=
  AlgebraicGeometry.IsLocally.forall_affineOpens CommRing.isNagataRing_propertyIsLocal hX U

/-- **Stacks Project, Tag 033W.** For a scheme `X`, being universally Japanese is equivalent to
the section ring of every affine open being universally Japanese, to this holding on some affine
open covering, and to admitting an open covering by universally Japanese open subschemes. -/
@[stacks 033W "equivalent conditions", sga "4 IX 2.14.2"]
theorem isUniversallyJapaneseScheme_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsUniversallyJapaneseScheme X,
      ∀ U : X.affineOpens, IsUniversallyJapaneseRing Γ(X, (U : X.Opens)),
      ∃ (I : Type u) (U : I → X.affineOpens),
        IsOpenCover (fun i ↦ (U i : X.Opens)) ∧
          ∀ i, IsUniversallyJapaneseRing Γ(X, (U i : X.Opens)),
      ∃ (I : Type u) (U : I → X.Opens),
        IsOpenCover U ∧ ∀ i, IsUniversallyJapaneseScheme (U i).toScheme] := by
  tfae_have 1 ↔ 2 :=
    isLocally_iff_forall_affineOpens CommRing.isUniversallyJapaneseRing_propertyIsLocal X
  tfae_have 1 ↔ 3 :=
    isLocally_iff_exists_affineOpenCover
      (fun (R : Type u) [CommRing R] => IsUniversallyJapaneseRing R) X
  tfae_have 1 ↔ 4 :=
    isLocally_iff_exists_openCover CommRing.isUniversallyJapaneseRing_propertyIsLocal X
  tfae_finish

/-- **Stacks Project, Tag 033W.** Every open subscheme of a universally Japanese scheme is
universally Japanese. -/
@[stacks 033W "open subschemes"]
theorem isUniversallyJapaneseScheme_open {X : Scheme.{u}} (hX : IsUniversallyJapaneseScheme X)
    (U : X.Opens) : IsUniversallyJapaneseScheme U.toScheme :=
  isLocally_open CommRing.isUniversallyJapaneseRing_propertyIsLocal X hX U

end
