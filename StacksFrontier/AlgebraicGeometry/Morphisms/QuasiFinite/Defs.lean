module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint

/-!
# Quasi-finite morphisms of schemes

A morphism of schemes is quasi-finite at a point when it is of finite type there and its stalk
map is quasi-finite. It is locally quasi-finite when this holds at every point, and quasi-finite
when it is moreover quasi-compact.

## Main definitions

* `AlgebraicGeometry.quasiFiniteAt` expresses that a morphism is quasi-finite at a point.
* `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite` together
  express local quasi-finiteness.
* Adding `AlgebraicGeometry.QuasiCompact` expresses quasi-finiteness.

## Main results

* `AlgebraicGeometry.quasiFiniteAt_iff_exists_affineOpens` identifies `quasiFiniteAt` with
  the affine-neighbourhood formulation in the source.
* `AlgebraicGeometry.forall_quasiFiniteAt_iff` identifies local quasi-finiteness with
  quasi-finiteness at every point.
* `AlgebraicGeometry.quasiFinite_conditions_iff_isDiscrete_fibers` expresses the fiber condition
  in the definition of a quasi-finite morphism.
* `AlgebraicGeometry.quasiFinite_conditions_iff_forall_quasiFiniteAt_and_quasiCompact`: a
  morphism is quasi-finite if and only if it is locally quasi-finite and quasi-compact.
* `AlgebraicGeometry.locallyQuasiFinite_conditions_tfae` and
  `AlgebraicGeometry.locallyQuasiFinite_conditions_resLE` characterize local quasi-finiteness on
  affine opens and on open coverings, and restrict it to open subschemes.

## Implementation notes

Mathlib's ring-theoretic and scheme-theoretic quasi-finiteness predicates omit the finite-type
condition. Thus quasi-finiteness at a point is the conjunction of
`AlgebraicGeometry.finiteTypeAt` and `Scheme.Hom.QuasiFiniteAt`. Similarly, local
quasi-finiteness is represented by the two typeclasses `LocallyOfFiniteType` and
`LocallyQuasiFinite`. A quasi-finite morphism has in addition the `QuasiCompact` typeclass. The
last characterization explicitly uses
`AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton` to identify
`LocallyQuasiFinite`, under the local finite-type condition, with discreteness of every
set-theoretic fiber.

The statement that a morphism is quasi-finite exactly when it is locally quasi-finite and
quasi-compact is stated with quasi-finiteness as finite type plus discreteness of every fiber and
local quasi-finiteness as `quasiFiniteAt` at every point. It follows from the two
characterizations above together with a reassociation of the conjunction.

## References

* [EGA II, Definition 6.2.3]
* [Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [Stacks Project, Tag 01TJ](https://stacks.math.columbia.edu/tag/01TJ)
* [Stacks Project, Tag 01TK](https://stacks.math.columbia.edu/tag/01TK)
-/

@[expose] public section

open CategoryTheory hiding IsDiscrete

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is quasi-finite at `x` if it is of finite type at `x` and its
stalk map at `x` is quasi-finite. -/
@[stacks 01TD "part (1)"]
public abbrev quasiFiniteAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  AlgebraicGeometry.finiteTypeAt f x ∧ f.QuasiFiniteAt x

/-- Quasi-finiteness at a point is equivalently witnessed on compatible affine
neighbourhoods by a finite-type ring map which is quasi-finite at the corresponding
prime. -/
@[stacks 01TD "part (1), affine-neighbourhood characterization"]
public theorem quasiFiniteAt_iff_exists_affineOpens
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    quasiFiniteAt f x ↔
      ∃ (U : S.affineOpens) (V : X.affineOpens) (hxV : x ∈ V.1)
        (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
        (f.appLE U V hVU).hom.FiniteType ∧
          (f.appLE U V hVU).hom.QuasiFiniteAt
            (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  constructor
  · rintro ⟨⟨U, V, hxV, hVU, hft⟩, hqf⟩
    exact ⟨U, V, hxV, hVU, hft, hqf.quasiFiniteAt V.2 U.2 hVU hxV⟩
  · rintro ⟨U, V, hxV, hVU, hft, hqf⟩
    refine ⟨⟨U, V, hxV, hVU, hft⟩, ?_⟩
    let _ := (f.appLE U V hVU).hom.toAlgebra
    let p := (U.2.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
    let q := (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal
    have : q.LiesOver p :=
      ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 V.1 V.2 hVU hxV).1).symm⟩
    let _ := Localization.AtPrime.algebraOfLiesOver p q
    let _ := hqf
    exact (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U.1 U.2 V.1 V.2 hVU hxV)).mpr
      (RingHom.quasiFinite_algebraMap.mpr (Algebra.QuasiFinite.of_restrictScalars
        Γ(S, U.1) (Localization.AtPrime p) (Localization.AtPrime q)))

add_to_stacks 01TD "the local finite-type condition in parts (2) and (3)"
  AlgebraicGeometry.LocallyOfFiniteType

add_to_stacks 01TD "the fiber-isolation condition in parts (2) and (3)"
  AlgebraicGeometry.LocallyQuasiFinite

add_to_stacks 01TD "the quasi-compact condition in part (3)"
  AlgebraicGeometry.QuasiCompact

/-- Finite type at a point, unfolded to its affine-neighbourhood form. -/
private lemma finiteTypeAt_iff_exists_affineOpens
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    AlgebraicGeometry.finiteTypeAt f x ↔
      ∃ (U : S.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
        (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
        (f.appLE U V hVU).hom.FiniteType := by
  simp only [AlgebraicGeometry.finiteTypeAt]

/-- Finite type ring maps are stable under composition with a principal localization of the
source. -/
private lemma finiteType_stableUnderCompositionWithLocalizationAwaySource :
    RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.FiniteType :=
  (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    RingHom.finiteType_holdsForLocalizationAway).left

/-- A morphism is quasi-finite at every point exactly when it is locally of finite type
and locally quasi-finite. -/
@[stacks 01TD "part (2), pointwise characterization"]
public theorem forall_quasiFiniteAt_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    (∀ x, quasiFiniteAt f x) ↔
      (AlgebraicGeometry.LocallyOfFiniteType f ∧
        AlgebraicGeometry.LocallyQuasiFinite f) := by
  constructor
  · intro h
    have hft : LocallyOfFiniteType f :=
      (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
        finiteType_stableUnderCompositionWithLocalizationAwaySource).mpr
        (fun x ↦ (finiteTypeAt_iff_exists_affineOpens f x).mp (h x).1)
    refine ⟨hft, locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr ?_⟩
    intro y
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
    rintro ⟨x, (rfl : f x = y)⟩
    change IsOpen ({⟨x, by simp⟩} : Set (f ⁻¹' {f x}))
    simpa only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
      using (f.fiberHomeo (f x)).isOpen_image.mpr
        (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (h x).2)
  · rintro ⟨hft, hqf⟩ x
    exact ⟨finiteTypeAt_of_locallyOfFiniteType f x, f.quasiFiniteAt x⟩

/-- The conditions defining a quasi-finite morphism can be expressed either by local
quasi-finiteness or by discreteness of every set-theoretic fiber. -/
@[stacks 01TD "part (3), fiber characterization"]
public theorem quasiFinite_conditions_iff_isDiscrete_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ((LocallyOfFiniteType f ∧ QuasiCompact f) ∧ LocallyQuasiFinite f) ↔
      ((LocallyOfFiniteType f ∧ QuasiCompact f) ∧
        ∀ s, IsDiscrete (f ⁻¹' {s})) :=
  and_congr_right fun h ↦
    have := h.1
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton

/-- A morphism is quasi-finite, that is of finite type with every point isolated in its fiber,
exactly when it is locally quasi-finite, that is quasi-finite at every point, and
quasi-compact. -/
@[stacks 01TJ "quasi-finite as in Tag 01TD (3), locally quasi-finite as in Tag 01TD (2)"]
public theorem quasiFinite_conditions_iff_forall_quasiFiniteAt_and_quasiCompact
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ((LocallyOfFiniteType f ∧ QuasiCompact f) ∧ ∀ s, IsDiscrete (f ⁻¹' {s})) ↔
      ((∀ x, quasiFiniteAt f x) ∧ QuasiCompact f) := by
  rw [forall_quasiFiniteAt_iff, ← quasiFinite_conditions_iff_isDiscrete_fibers, and_right_comm]

/-- The ring-map condition `FiniteType ∧ QuasiFinite` defining quasi-finite ring maps is stable
under composition with a principal localization of the source. -/
private lemma finiteType_and_quasiFinite_stableUnderCompositionWithLocalizationAwaySource :
    RingHom.StableUnderCompositionWithLocalizationAwaySource
      (fun f ↦ RingHom.FiniteType f ∧ RingHom.QuasiFinite f) :=
  fun _ S _ _ _ _ _ r _ f hf ↦
    ⟨finiteType_stableUnderCompositionWithLocalizationAwaySource S r f hf.1,
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).left S r f hf.2⟩

/-- Local quasi-finiteness, as a single morphism property. -/
private abbrev locallyQuasiFiniteConditions : MorphismProperty Scheme.{u} :=
  @LocallyOfFiniteType ⊓ @LocallyQuasiFinite

private instance : HasRingHomProperty locallyQuasiFiniteConditions
    (fun f ↦ RingHom.FiniteType f ∧ RingHom.QuasiFinite f) := HasRingHomProperty.inf

/-- **Stacks Project, Tag 01TK.** Local quasi-finiteness can be checked on all pairs of affine
opens, on open coverings of the target and of the preimages, or on affine such coverings; on
affine opens it is the condition that the ring map be quasi-finite, that is of finite type and
quasi-finite at every prime. -/
@[stacks 01TK "equivalence of (1), (2), (3) and (4)"]
public theorem locallyQuasiFinite_conditions_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [
      LocallyOfFiniteType f ∧ LocallyQuasiFinite f,
      ∀ (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1),
        (f.appLE V U e).hom.FiniteType ∧ (f.appLE V U e).hom.QuasiFinite,
      ∃ 𝒱 : Set S.Opens, sSup 𝒱 = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.Opens, sSup 𝒰 = f ⁻¹ᵁ V ∧
        ∀ U ∈ 𝒰, ∃ e : U ≤ f ⁻¹ᵁ V,
          LocallyOfFiniteType (f.resLE V U e) ∧ LocallyQuasiFinite (f.resLE V U e),
      ∃ 𝒱 : Set S.affineOpens, (⨆ V ∈ 𝒱, V.1) = ⊤ ∧ ∀ V ∈ 𝒱, ∃ 𝒰 : Set X.affineOpens,
        (⨆ U ∈ 𝒰, U.1) = f ⁻¹ᵁ V.1 ∧ ∀ U ∈ 𝒰, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          (f.appLE V U e).hom.FiniteType ∧ (f.appLE V U e).hom.QuasiFinite] := by
  have : locallyQuasiFiniteConditions.RespectsRight @IsOpenImmersion :=
    have := HasRingHomProperty.respects_isOpenImmersion (P := locallyQuasiFiniteConditions)
      finiteType_and_quasiFinite_stableUnderCompositionWithLocalizationAwaySource
    inferInstance
  tfae_have 1 → 2 := fun hf V U e ↦
    HasRingHomProperty.appLE locallyQuasiFiniteConditions f hf V U e
  tfae_have 2 → 4 := by
    intro h
    refine ⟨Set.univ, iSup_univ.trans (iSup_affineOpens_eq_top S), fun V _ ↦
      ⟨{U | U.1 ≤ f ⁻¹ᵁ V.1}, le_antisymm (iSup₂_le fun U hU ↦ hU) ?_,
        fun U hU ↦ ⟨hU, h V U hU⟩⟩⟩
    intro x hx
    obtain ⟨U, hU, hxU, hUV⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨U, hU⟩, TopologicalSpace.Opens.mem_iSup.mpr ⟨hUV, hxU⟩⟩
  tfae_have 4 → 1 := by
    rintro ⟨𝒱, h𝒱, H⟩
    refine (HasRingHomProperty.iff_exists_appLE (P := locallyQuasiFiniteConditions)
      finiteType_and_quasiFinite_stableUnderCompositionWithLocalizationAwaySource).mpr
      fun x ↦ ?_
    obtain ⟨V, hV, hxV⟩ : ∃ V ∈ 𝒱, f x ∈ V.1 := by
      have : f x ∈ ⨆ V ∈ 𝒱, V.1 := h𝒱 ▸ trivial
      simpa only [TopologicalSpace.Opens.mem_iSup, exists_prop] using this
    obtain ⟨𝒰, h𝒰, H'⟩ := H V hV
    obtain ⟨U, hU, hxU⟩ : ∃ U ∈ 𝒰, x ∈ U.1 := by
      have : x ∈ ⨆ U ∈ 𝒰, U.1 := h𝒰 ▸ hxV
      simpa only [TopologicalSpace.Opens.mem_iSup, exists_prop] using this
    obtain ⟨e, he⟩ := H' U hU
    exact ⟨V, U, hxU, e, he⟩
  tfae_have 1 → 3 := by
    intro hf
    refine ⟨{⊤}, sSup_singleton, fun V hV ↦ ?_⟩
    obtain rfl : V = ⊤ := hV
    refine ⟨{⊤}, sSup_singleton, fun U hU ↦ ?_⟩
    obtain rfl : U = ⊤ := hU
    exact ⟨le_top, IsZariskiLocalAtSource.resLE (P := locallyQuasiFiniteConditions) _ hf⟩
  tfae_have 3 → 1 := by
    rintro ⟨𝒱, h𝒱, H⟩
    refine (IsZariskiLocalAtSource.iff_exists_resLE (P := locallyQuasiFiniteConditions)).mpr
      fun x ↦ ?_
    obtain ⟨V, hV, hxV⟩ : ∃ V ∈ 𝒱, f x ∈ V := by
      have : f x ∈ sSup 𝒱 := h𝒱 ▸ trivial
      exact TopologicalSpace.Opens.mem_sSup.mp this
    obtain ⟨𝒰, h𝒰, H'⟩ := H V hV
    obtain ⟨U, hU, hxU⟩ : ∃ U ∈ 𝒰, x ∈ U := by
      have : x ∈ sSup 𝒰 := h𝒰 ▸ hxV
      exact TopologicalSpace.Opens.mem_sSup.mp this
    obtain ⟨e, he⟩ := H' U hU
    exact ⟨V, U, hxU, e, he⟩
  tfae_finish

/-- **Stacks Project, Tag 01TK.** If `f` is locally quasi-finite then so is its restriction
`U → V` to any opens `U ⊆ X`, `V ⊆ S` with `f(U) ⊆ V`. -/
@[stacks 01TK "moreover: restriction to open subschemes"]
public theorem locallyQuasiFinite_conditions_resLE {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : LocallyOfFiniteType f ∧ LocallyQuasiFinite f) (V : S.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) :
    LocallyOfFiniteType (f.resLE V U e) ∧ LocallyQuasiFinite (f.resLE V U e) :=
  IsZariskiLocalAtSource.resLE (P := locallyQuasiFiniteConditions) e hf

end AlgebraicGeometry
