module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Properties
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Separatedness, properness and finiteness of a modification from its local pieces

Let `D` be a `FinitePresentationAwayPointsSituation`: a scheme `S` with finitely many pairwise
distinct closed points `s i` whose open complement `U` is quasi-compact. Base change to the
spectra of the local rings `S i = Spec 𝒪_{S, s i}` carries a finitely presented morphism
`f : X ⟶ S` which is an isomorphism over `U` to a family of morphisms `g i : Y i ⟶ S i`; this
is the functor `F` of [Stacks, Tag 0BFU], here the field `BaseChangeFunctor.functor`, and `f`
*corresponds to* `g i` when `g i` is the `i`th component `BC.functor.obj X i` of its image.

This file proves that `f` is separated, proper, or finite exactly when every `g i` is. One
direction is base change stability. The other is covering `S` by `U` together with one open
neighbourhood of each `s i`: over `U` the morphism is an isomorphism, and a neighbourhood of
`s i` on which the property holds is produced by spreading out from `Spec 𝒪_{S, s i}`.

That spreading-out step is the assertion of [Stacks, Tag 0EY3], which is available in the
library as `AlgebraicGeometry.GlueingNearPoint.exists_open_isSeparated`,
`AlgebraicGeometry.GlueingNearPoint.exists_open_isProper` and
`AlgebraicGeometry.GlueingNearPoint.exists_open_isFinite`. Those statements concern a scheme of
finite presentation over an open neighbourhood of the union of the quasi-compact open and the
point; taking that neighbourhood to be the whole of `S` gives the form needed here, so the three
results below are unconditional.

## Main results

* `AlgebraicGeometry.prop_baseChangeLocal` : a property stable under base change passes from
  `f` to each `g i`, unconditionally.
* `AlgebraicGeometry.prop_iff_forall_baseChangeLocal` : for a property that is stable under
  base change, contains the identities, is Zariski local on the target, and spreads out from
  local rings, `f` has the property if and only if every `g i` does. The spreading-out
  assertion is the one hypothesis that is not an instance.
* `AlgebraicGeometry.isSeparated_iff_forall_baseChangeLocal`,
  `AlgebraicGeometry.isProper_iff_forall_baseChangeLocal` and
  `AlgebraicGeometry.isFinite_iff_forall_baseChangeLocal` are the three instances of this for
  separatedness, properness and finiteness, with the spreading-out hypothesis discharged from
  Tag 0EY3.

## Implementation notes

The objects of the global and local categories are objects of full subcategories of
over-categories, so the morphisms in question are the structure morphisms `X.obj.hom` and
`(BC.functor.obj X i).obj.hom`. The data `BaseChangeFunctor.pullbackIso` identifies the latter,
after forgetting the defining properties, with the pullback of `X.obj.hom` along
`S.fromSpecStalk (D.points i)`; `AlgebraicGeometry.baseChangeLocalArrowIso` packages that
identification as an isomorphism of arrows, which is what transfers a morphism property.

The open cover used in the proof is indexed by `Option (Fin D.n)`, with `none` naming the
complement of the distinguished points and `some i` the neighbourhood of `s i`.

The spreading-out results of Tag 0EY3 are stated for a scheme of finite presentation over an
open neighbourhood of the union of the quasi-compact open and the point, packaged as a
`AlgebraicGeometry.GlueingNearPoint.FinitePresentationNeighborhoodModel`. A morphism
`f : X ⟶ S` becomes such a model with neighbourhood `⊤`, viewing `f` as a morphism to
`(⊤ : S.Opens).toScheme` along `AlgebraicGeometry.Scheme.topIso`; base changing that model to
an open `V` then gives back `pullback.snd f V.ι`. The retrocompactness of `U` assumed by Tag
0EY3 follows from quasi-compactness of `U.ι` through
`IsRetrocompact_iff_isSpectralMap_subtypeVal`.

## References

* [Stacks Project, Tag 0BFW](https://stacks.math.columbia.edu/tag/0BFW)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0EY3](https://stacks.math.columbia.edu/tag/0EY3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A finitely presented morphism `f : X ⟶ S` viewed as a scheme of finite presentation over
the open neighbourhood `⊤` of `S`, which is the shape in which [Stacks, Tag 0EY3] is stated. -/
private noncomputable def topNeighborhoodModel {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) (U : S.Opens) (s : S) :
    GlueingNearPoint.FinitePresentationNeighborhoodModel S U s where
  neighborhood := ⟨⊤, le_top, trivial⟩
  source := X
  hom := f ≫ S.topIso.inv
  finitePresentation := by
    have := hf.1
    have := hf.2.1
    have := hf.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A spreading-out statement for schemes of finite presentation over a neighbourhood
(as in [Stacks, Tag 0EY3]), specialised to the neighbourhood `⊤`: a property holding for the base
change of `f : X ⟶ S` to a quasi-compact open `U` and to `Spec 𝒪_{S, s}`, with `s ∉ U`, holds for
its base change to an open neighbourhood of `s` containing `U`. -/
private theorem exists_open_pullback_snd_of_spread (P : MorphismProperty Scheme.{u})
    (hspread : ∀ (S : Scheme.{u}) (U : S.Opens) (s : S), s ∉ U → IsRetrocompact (U : Set S) →
      ∀ M : GlueingNearPoint.FinitePresentationNeighborhoodModel S U s,
      P ((Over.pullback U.ι).obj
          ((GlueingNearPoint.neighborhoodModelToAmbient S U s).obj M)).hom →
      P ((Over.pullback (S.fromSpecStalk s)).obj
          ((GlueingNearPoint.neighborhoodModelToAmbient S U s).obj M)).hom →
      ∃ V : S.Opens, U ≤ V ∧ V ≤ M.neighborhood.V ∧ s ∈ V ∧
        P ((Over.pullback V.ι).obj
          ((GlueingNearPoint.neighborhoodModelToAmbient S U s).obj M)).hom)
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (U : S.Opens)
    (hU : QuasiCompact U.ι) (s : S) (hs : s ∉ U)
    (hopen : P (pullback.snd f U.ι)) (hlocal : P (pullback.snd f (S.fromSpecStalk s))) :
    ∃ V : S.Opens, U ≤ V ∧ s ∈ V ∧ P (pullback.snd f V.ι) := by
  have he : (GlueingNearPoint.neighborhoodModelToAmbient S U s).obj
      (topNeighborhoodModel f hf U s) = Over.mk f := by
    show Over.mk ((f ≫ S.topIso.inv) ≫ (⊤ : S.Opens).ι) = Over.mk f
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  obtain ⟨V, hUV, -, hsV, hPV⟩ := hspread S U s hs
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr (quasiCompact_iff_isSpectralMap.mp hU))
    (topNeighborhoodModel f hf U s) (by rwa [he]) (by rwa [he])
  exact ⟨V, hUV, hsV, by rwa [he] at hPV⟩

/-- A property of morphisms holding after base change to an open subscheme holds for the
corresponding restriction. -/
private theorem prop_morphismRestrict_of_pullback_snd (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (h : P (pullback.snd f U.ι)) : P (f ∣_ U) := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f U] at h
  exact (P.cancel_left_of_respectsIso (pullbackRestrictIsoRestrict f U).hom (f ∣_ U)).1 h

/-- The structure morphism of the object of the `i`th local category corresponding to `X` is,
as an arrow, the base change of the structure morphism of `X` along
`Spec 𝒪_{S, s i} ⟶ S`. -/
noncomputable def baseChangeLocalArrowIso (D : FinitePresentationAwayPointsSituation.{u})
    (BC : BaseChangeFunctor D) (X : D.globalCategory) (i : Fin D.n) :
    Arrow.mk (BC.functor.obj X i).obj.hom ≅
      Arrow.mk (pullback.snd X.obj.hom (D.S.fromSpecStalk (D.points i))) := by
  refine Arrow.isoMk ((Over.forget (D.localScheme i)).mapIso ((BC.pullbackIso i).app X))
    (Iso.refl _) ?_
  have h := Over.w ((BC.pullbackIso i).app X).hom
  simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Over.forget_map]
  exact h

/-- A property of morphisms holds for the object of the `i`th local category corresponding to
`X` exactly when it holds for the base change of `X` along `Spec 𝒪_{S, s i} ⟶ S`. -/
theorem prop_baseChangeLocal_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {D : FinitePresentationAwayPointsSituation.{u}} (BC : BaseChangeFunctor D)
    (X : D.globalCategory) (i : Fin D.n) :
    P (BC.functor.obj X i).obj.hom ↔
      P (pullback.snd X.obj.hom (D.S.fromSpecStalk (D.points i))) :=
  P.arrow_mk_iso_iff (baseChangeLocalArrowIso D BC X i)

/-- A property of morphisms stable under base change passes from `f : X ⟶ S` to each of the
corresponding morphisms `g i : Y i ⟶ Spec 𝒪_{S, s i}`. -/
theorem prop_baseChangeLocal (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {D : FinitePresentationAwayPointsSituation.{u}} (BC : BaseChangeFunctor D)
    (X : D.globalCategory) (hX : P X.obj.hom) (i : Fin D.n) :
    P (BC.functor.obj X i).obj.hom :=
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  (prop_baseChangeLocal_iff P BC X i).2
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) hX)

/-- A property of morphisms which is stable under base change, contains the identities, is
Zariski local on the target and spreads out from local rings holds for a finitely presented
morphism `f : X ⟶ S` which is an isomorphism away from the distinguished closed points if and
only if it holds for each of the corresponding morphisms `g i : Y i ⟶ Spec 𝒪_{S, s i}`. -/
theorem prop_iff_forall_baseChangeLocal (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.ContainsIdentities] [IsZariskiLocalAtTarget P]
    (hP : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z), FinitePresentation g → ∀ W : Z.Opens,
      QuasiCompact W.ι → ∀ t : Z, t ∉ W → P (pullback.snd g W.ι) →
        P (pullback.snd g (Z.fromSpecStalk t)) →
          ∃ V : Z.Opens, W ≤ V ∧ t ∈ V ∧ P (pullback.snd g V.ι))
    {D : FinitePresentationAwayPointsSituation.{u}}
    (BC : BaseChangeFunctor D) (X : D.globalCategory) :
    P X.obj.hom ↔ ∀ i, P (BC.functor.obj X i).obj.hom := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsIso (pullback.snd X.obj.hom D.complement.ι) := X.property.2
  have hU : P (pullback.snd X.obj.hom D.complement.ι) := MorphismProperty.of_isIso P _
  refine ⟨fun hX ↦ prop_baseChangeLocal P BC X hX, fun hg ↦ ?_⟩
  have hpt : ∀ i, D.points i ∉ D.complement := fun i ↦ by
    simp [FinitePresentationAwayPointsSituation.complement, rangeComplementOfClosedPoints]
  choose V _hUV hmem hV using fun i ↦
    hP X.obj.hom X.property.1 D.complement D.complement_quasiCompact (D.points i) (hpt i) hU
      ((prop_baseChangeLocal_iff P BC X i).1 (hg i))
  have hcover : iSup (fun j : Option (Fin D.n) ↦ j.elim D.complement V) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    by_cases hx : x ∈ D.complement
    · exact Opens.mem_iSup.mpr ⟨none, hx⟩
    · obtain ⟨i, rfl⟩ : x ∈ Set.range D.points := by
        simpa [FinitePresentationAwayPointsSituation.complement,
          rangeComplementOfClosedPoints] using hx
      exact Opens.mem_iSup.mpr ⟨some i, hmem i⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P)
    (fun j : Option (Fin D.n) ↦ j.elim D.complement V) hcover]
  rintro (_ | i)
  · exact prop_morphismRestrict_of_pullback_snd P _ _ hU
  · exact prop_morphismRestrict_of_pullback_snd P _ _ (hV i)

/-- **Stacks Project, Tag 0BFW (separatedness).** If `f : X ⟶ S` corresponds to
`g i : Y i ⟶ Spec 𝒪_{S, s i}` under the base-change functor of Tag 0BFU, then `f` is separated
if and only if every `g i` is separated. -/
@[stacks 0BFW "separated"]
theorem isSeparated_iff_forall_baseChangeLocal
    {D : FinitePresentationAwayPointsSituation.{u}} (BC : BaseChangeFunctor D)
    (X : D.globalCategory) :
    IsSeparated X.obj.hom ↔ ∀ i, IsSeparated (BC.functor.obj X i).obj.hom :=
  have : MorphismProperty.ContainsIdentities (@IsSeparated : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  prop_iff_forall_baseChangeLocal _
    (exists_open_pullback_snd_of_spread _ GlueingNearPoint.exists_open_isSeparated) BC X

/-- **Stacks Project, Tag 0BFW (properness).** If `f : X ⟶ S` corresponds to
`g i : Y i ⟶ Spec 𝒪_{S, s i}` under the base-change functor of Tag 0BFU, then `f` is proper if
and only if every `g i` is proper. -/
@[stacks 0BFW "proper"]
theorem isProper_iff_forall_baseChangeLocal
    {D : FinitePresentationAwayPointsSituation.{u}} (BC : BaseChangeFunctor D)
    (X : D.globalCategory) :
    IsProper X.obj.hom ↔ ∀ i, IsProper (BC.functor.obj X i).obj.hom :=
  have : MorphismProperty.ContainsIdentities (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  prop_iff_forall_baseChangeLocal _
    (exists_open_pullback_snd_of_spread _ GlueingNearPoint.exists_open_isProper) BC X

/-- **Stacks Project, Tag 0BFW (finiteness).** If `f : X ⟶ S` corresponds to
`g i : Y i ⟶ Spec 𝒪_{S, s i}` under the base-change functor of Tag 0BFU, then `f` is finite if
and only if every `g i` is finite. -/
@[stacks 0BFW "finite"]
theorem isFinite_iff_forall_baseChangeLocal
    {D : FinitePresentationAwayPointsSituation.{u}} (BC : BaseChangeFunctor D)
    (X : D.globalCategory) :
    IsFinite X.obj.hom ↔ ∀ i, IsFinite (BC.functor.obj X i).obj.hom :=
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  prop_iff_forall_baseChangeLocal _
    (exists_open_pullback_snd_of_spread _ GlueingNearPoint.exists_open_isFinite) BC X

end AlgebraicGeometry
