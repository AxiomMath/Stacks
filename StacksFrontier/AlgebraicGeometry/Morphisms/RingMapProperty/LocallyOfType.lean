module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.Defs

/-!
# Morphisms locally of type `P` for a local property `P`

For a local property `P` of ring maps, a morphism of schemes locally of type `P` satisfies `P`
on every pair of affine opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`; this property of morphisms can
be checked on open coverings of the source and target, is inherited by restrictions to open
subschemes, and is stable under composition when `P` is. Smoothness is the example used later.

## Main results

* `RingHom.StacksPropertyIsLocal.propertyIsLocal`: a local property in the sense of the source
  is local in Mathlib's sense `RingHom.PropertyIsLocal`.
* `AlgebraicGeometry.locallyOfType_eq_affineLocally`: for such a property, being locally of
  type `P` is Mathlib's `affineLocally P`.
* `AlgebraicGeometry.appLE_of_locallyOfType`: [Stacks Project, Tag 01ST].
* `AlgebraicGeometry.locallyOfType_tfae`, `AlgebraicGeometry.locallyOfType_resLE`:
  [Stacks Project, Tag 01SU].
* `AlgebraicGeometry.locallyOfType_comp`: [Stacks Project, Tag 01SV].
* `RingHom.Smooth.stacksPropertyIsLocal`, `AlgebraicGeometry.smooth_tfae`,
  `AlgebraicGeometry.smooth_resLE`: [Stacks Project, Tag 01V6].

## Implementation notes

Condition (1)(b) of locality, applied with the unit element in the source or in the target,
says that `P` is stable under composition with principal localizations on either side; with
conditions (1)(a) and (1)(c) this gives all four axioms of Mathlib's `RingHom.PropertyIsLocal`.
The results above are then instances of Mathlib's `HasRingHomProperty` API, the affine-cover
characterization `HasRingHomProperty.iff_exists_appLE` being literally the definition of
`AlgebraicGeometry.locallyOfType`.

Open coverings are encoded as sets of opens whose supremum is the space covered, so that the
index sets of the source carry no universe constraint.

## References

* [Stacks Project, Tag 01ST](https://stacks.math.columbia.edu/tag/01ST)
* [Stacks Project, Tag 01SU](https://stacks.math.columbia.edu/tag/01SU)
* [Stacks Project, Tag 01SV](https://stacks.math.columbia.edu/tag/01SV)
* [Stacks Project, Tag 01V6](https://stacks.math.columbia.edu/tag/01V6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace RingHom

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- A ring is its own localization away from `1`. -/
private theorem isLocalization_away_one_self (R : Type u) [CommRing R] :
    IsLocalization.Away (1 : R) R :=
  IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id

namespace StacksPropertyIsLocal

variable (hP : StacksPropertyIsLocal P)
include hP

/-- A local property is stable under composition with a principal localization of the
target. -/
theorem stableUnderCompositionWithLocalizationAwayTarget :
    StableUnderCompositionWithLocalizationAwayTarget P := by
  intro R S T _ _ _ _ s _ f hf
  have := isLocalization_away_one_self R
  have := hP.compPrincipalLocalizations (R := R) (A := S) (Rf := R) (Aa := T) (1 : R) s f hf
  rwa [Algebra.algebraMap_self, RingHom.comp_id] at this

/-- A local property is stable under composition with a principal localization of the
source. -/
theorem stableUnderCompositionWithLocalizationAwaySource :
    StableUnderCompositionWithLocalizationAwaySource P := by
  intro R Rr T _ _ _ _ r _ f hf
  have := isLocalization_away_one_self T
  have := hP.compPrincipalLocalizations (R := R) (A := T) (Rf := Rr) (Aa := T) r (1 : T) f hf
  rwa [Algebra.algebraMap_self, RingHom.id_comp] at this

/-- A local property descends along an arbitrary spanning family of the target. -/
theorem ofLocalizationSpanTarget : OfLocalizationSpanTarget P :=
  (RingHom.ofLocalizationSpanTarget_iff_finite @P).mpr hP.ofLocalizationFiniteSpanTarget

/-- A local property can be checked after localizing the source on a spanning family. -/
theorem ofLocalizationSpan : OfLocalizationSpan P := by
  intro R S _ _ f s hs H
  refine hP.ofLocalizationSpanTarget f (f '' s)
    (by rw [← Ideal.map_span, hs, Ideal.map_top]) ?_
  rintro ⟨_, r, hr, rfl⟩
  have := isLocalization_away_one_self (Localization.Away (f r))
  have := hP.compPrincipalLocalizations (R := R) (A := Localization.Away (f r))
    (Rf := Localization.Away r) (Aa := Localization.Away (f r)) r 1
    (Localization.awayMap f r) (H ⟨r, hr⟩)
  rwa [Algebra.algebraMap_self, RingHom.id_comp, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_comp] at this

/-- A local property in the sense of the Stacks Project is local in Mathlib's sense. -/
theorem propertyIsLocal : PropertyIsLocal P where
  localizationAwayPreserves := hP.localizationAwayPreserves
  ofLocalizationSpanTarget := hP.ofLocalizationSpanTarget
  ofLocalizationSpan := hP.ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    hP.stableUnderCompositionWithLocalizationAwayTarget

end StacksPropertyIsLocal

/-- Smoothness of ring maps is a local property. -/
@[stacks 01V6 "smoothness of ring maps is local"]
theorem Smooth.stacksPropertyIsLocal : StacksPropertyIsLocal RingHom.Smooth where
  localizationAwayPreserves := RingHom.Smooth.propertyIsLocal.localizationAwayPreserves
  compPrincipalLocalizations {_ _ Rf Aa} _ _ _ _ f a _ _ _ _ _ hg :=
    ((RingHom.Smooth.holdsForLocalizationAway Rf f).comp hg).comp
      (RingHom.Smooth.holdsForLocalizationAway Aa a)
  ofLocalizationFiniteSpanTarget :=
    (RingHom.ofLocalizationSpanTarget_iff_finite @RingHom.Smooth).mp
      RingHom.Smooth.ofLocalizationSpanTarget

end RingHom

namespace AlgebraicGeometry

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- For a local property `P`, a morphism is locally of type `P` exactly when it satisfies
Mathlib's `affineLocally P`. -/
theorem locallyOfType_eq_affineLocally (hP : RingHom.StacksPropertyIsLocal P) :
    locallyOfType P = affineLocally P := by
  have : HasRingHomProperty (affineLocally P) P := ⟨hP.propertyIsLocal, rfl⟩
  ext X Y f
  exact (HasRingHomProperty.iff_exists_appLE (P := affineLocally P)
    hP.stableUnderCompositionWithLocalizationAwaySource).symm

/-- For a local property `P`, being locally of type `P` is the morphism property associated
with `P` in Mathlib's sense. -/
theorem RingHom.StacksPropertyIsLocal.hasRingHomProperty (hP : RingHom.StacksPropertyIsLocal P) :
    HasRingHomProperty (locallyOfType P) P :=
  ⟨hP.propertyIsLocal, locallyOfType_eq_affineLocally hP⟩

variable {X S : Scheme.{u}}

/-- If `f` is locally of type `P` for a local property `P`, then `P` holds for the ring map
`𝒪_S(V) → 𝒪_X(U)` of any affine opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`. -/
@[stacks 01ST]
theorem appLE_of_locallyOfType (hP : RingHom.StacksPropertyIsLocal P) {f : X ⟶ S}
    (hf : locallyOfType P f) (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    P (f.appLE V U e).hom :=
  have := hP.hasRingHomProperty
  HasRingHomProperty.appLE (locallyOfType P) f hf V U e

/-- If `f` is locally of type `P` for a local property `P`, then so is its restriction
`U → V` to any opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`. -/
@[stacks 01SU "moreover: restriction to open subschemes"]
theorem locallyOfType_resLE (hP : RingHom.StacksPropertyIsLocal P) {f : X ⟶ S}
    (hf : locallyOfType P f) (V : S.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    locallyOfType P (f.resLE V U e) :=
  have := hP.hasRingHomProperty
  IsZariskiLocalAtSource.resLE e hf

/-- For a local property `P`, being locally of type `P` can be checked on all pairs of affine
opens, on open coverings of target and preimages, or on affine such coverings. -/
@[stacks 01SU "equivalence of (1), (2), (3) and (4)"]
theorem locallyOfType_tfae (hP : RingHom.StacksPropertyIsLocal P) (f : X ⟶ S) :
    List.TFAE [
      locallyOfType P f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1), P (f.appLE V U e).hom,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, locallyOfType P (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1, P (f.appLE V U e).hom] := by
  have := hP.hasRingHomProperty
  have : (locallyOfType P).RespectsRight @IsOpenImmersion :=
    have := HasRingHomProperty.respects_isOpenImmersion (P := locallyOfType P)
      hP.stableUnderCompositionWithLocalizationAwaySource
    inferInstance
  tfae_have 1 → 2 := fun hf V U e ↦ appLE_of_locallyOfType hP hf V U e
  tfae_have 2 → 4 := by
    intro h
    refine ⟨Set.univ, by rw [iSup_univ]; exact iSup_affineOpens_eq_top S, fun V _ ↦
      ⟨{U | U.1 ≤ f ⁻¹ᵁ V.1}, le_antisymm (iSup₂_le fun U hU ↦ hU) ?_,
        fun U hU ↦ ⟨hU, h V U hU⟩⟩⟩
    intro x hx
    obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, Opens.mem_iSup.mpr ⟨hUV, hxU⟩⟩
  tfae_have 4 → 1 := by
    rintro ⟨𝒱, h𝒱, H⟩ x
    obtain ⟨V, hV, hxV⟩ : ∃ V ∈ 𝒱, f x ∈ V.1 := by
      have : f x ∈ ⨆ V ∈ 𝒱, V.1 := by rw [h𝒱]; trivial
      obtain ⟨V, hV⟩ := Opens.mem_iSup.mp this
      exact ⟨V, (Opens.mem_iSup.mp hV).1, (Opens.mem_iSup.mp hV).2⟩
    obtain ⟨𝒰, h𝒰, H'⟩ := H V hV
    obtain ⟨U, hU, hxU⟩ : ∃ U ∈ 𝒰, x ∈ U.1 := by
      have : x ∈ ⨆ U ∈ 𝒰, U.1 := by rw [h𝒰]; exact hxV
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp this
      exact ⟨U, (Opens.mem_iSup.mp hU).1, (Opens.mem_iSup.mp hU).2⟩
    obtain ⟨e, he⟩ := H' U hU
    exact ⟨V, U, hxU, e, he⟩
  tfae_have 1 → 3 := by
    intro hf
    refine ⟨{⊤}, sSup_singleton, fun V hV ↦ ?_⟩
    obtain rfl : V = ⊤ := hV
    refine ⟨{⊤}, sSup_singleton, fun U hU ↦ ?_⟩
    obtain rfl : U = ⊤ := hU
    exact ⟨le_top, locallyOfType_resLE hP hf _ _ _⟩
  tfae_have 3 → 1 := by
    rintro ⟨𝒱, h𝒱, H⟩
    refine (IsZariskiLocalAtSource.iff_exists_resLE (P := locallyOfType P)).mpr fun x ↦ ?_
    obtain ⟨V, hV, hxV⟩ : ∃ V ∈ 𝒱, f x ∈ V := by
      have : f x ∈ sSup 𝒱 := by rw [h𝒱]; trivial
      exact Opens.mem_sSup.mp this
    obtain ⟨𝒰, h𝒰, H'⟩ := H V hV
    obtain ⟨U, hU, hxU⟩ : ∃ U ∈ 𝒰, x ∈ U := by
      have : x ∈ sSup 𝒰 := by rw [h𝒰]; exact hxV
      exact Opens.mem_sSup.mp this
    obtain ⟨e, he⟩ := H' U hU
    exact ⟨V, U, hxU, e, he⟩
  tfae_finish

/-- The whole statement: for a local property `P`, the four characterizations of being locally
of type `P` agree, and being locally of type `P` passes to restrictions to open subschemes. -/
@[stacks 01SU]
theorem locallyOfType_tfae_and_resLE (hP : RingHom.StacksPropertyIsLocal P) (f : X ⟶ S) :
    List.TFAE [
      locallyOfType P f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1), P (f.appLE V U e).hom,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, locallyOfType P (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1, P (f.appLE V U e).hom] ∧
    (locallyOfType P f → ∀ (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V),
      locallyOfType P (f.resLE V U e)) :=
  ⟨locallyOfType_tfae hP f, fun hf U V e ↦ locallyOfType_resLE hP hf V U e⟩

/-- For a local property `P` stable under composition, a composition of morphisms locally of
type `P` is locally of type `P`. -/
@[stacks 01SV]
theorem locallyOfType_comp (hP : RingHom.StacksPropertyIsLocal P)
    (hPc : RingHom.StableUnderComposition P) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : locallyOfType P f) (hg : locallyOfType P g) : locallyOfType P (f ≫ g) :=
  have := hP.hasRingHomProperty
  have := HasRingHomProperty.stableUnderComposition (P := locallyOfType P) hPc
  (locallyOfType P).comp_mem f g hf hg

/-- A morphism of schemes is smooth exactly when it is locally of type "smooth ring map". -/
theorem smooth_iff_locallyOfType (f : X ⟶ S) : Smooth f ↔ locallyOfType RingHom.Smooth f :=
  HasRingHomProperty.iff_exists_appLE (P := @Smooth)
    RingHom.Smooth.stacksPropertyIsLocal.stableUnderCompositionWithLocalizationAwaySource

/-- If `f` is smooth then so is its restriction `U → V` to any opens `U ⊆ X`, `V ⊆ S` with
`f(U) ⊆ V`. -/
@[stacks 01V6 "moreover: restriction to open subschemes"]
theorem smooth_resLE {f : X ⟶ S} (hf : Smooth f) (V : S.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) : Smooth (f.resLE V U e) :=
  (smooth_iff_locallyOfType _).mpr (locallyOfType_resLE RingHom.Smooth.stacksPropertyIsLocal
    ((smooth_iff_locallyOfType f).mp hf) V U e)

/-- Smoothness of a morphism of schemes can be checked on all pairs of affine opens, on open
coverings of target and preimages, or on affine such coverings. -/
@[stacks 01V6 "equivalence of (1), (2), (3) and (4)"]
theorem smooth_tfae (f : X ⟶ S) :
    List.TFAE [
      Smooth f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.Smooth,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, Smooth (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          (f.appLE V U e).hom.Smooth] := by
  simp only [smooth_iff_locallyOfType]
  exact locallyOfType_tfae RingHom.Smooth.stacksPropertyIsLocal f

/-- The whole statement: the four characterizations of smoothness agree, and smoothness passes
to restrictions to open subschemes. -/
@[stacks 01V6]
theorem smooth_tfae_and_resLE (f : X ⟶ S) :
    List.TFAE [
      Smooth f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.Smooth,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V, Smooth (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          (f.appLE V U e).hom.Smooth] ∧
    (Smooth f → ∀ (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V), Smooth (f.resLE V U e)) :=
  ⟨smooth_tfae f, fun hf U V e ↦ smooth_resLE hf V U e⟩

end AlgebraicGeometry
