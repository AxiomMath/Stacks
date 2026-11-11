module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeProjGlue.Algebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative homogeneous spectrum

Tag 01NQ builds `Proj_S(𝒜) ⟶ S`, for a quasi-coherent graded algebra `𝒜` on a scheme `S`, by
glueing the absolute `Proj Γ(U, 𝒜)` over the affine opens `U` of `S`.
`StacksFrontier.AlgebraicGeometry.RelativeProj.Local` built those charts, their structure
morphisms and the transitions, and proved the glueing squares *commute*. This file supplies the
missing half — the squares are **cartesian** — and performs the glueing.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGlue.chartFunctor`: the charts as a functor
  `S.AffineZariskiSite ⥤ Scheme`, with the transition morphisms as its action on arrows.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeGluingData`: that functor together with the
  structure morphisms to the affine opens, as an
  `AlgebraicGeometry.Scheme.Cover.RelativeGluingData` for the directed affine cover of `S`.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj` and
  `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProjToBase`: the glued scheme and its
  structure morphism to `S`.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.chart`: the chart `Proj Γ(U, 𝒜) ⟶ Proj_S(𝒜)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGlue.isOpenImmersion_projMap`: for a graded ring map
  exhibiting `B` as a localization of `A` away from a degree-zero element, Mathlib's
  `AlgebraicGeometry.Proj.map` is an open immersion.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.opensRange_resMap`: its image is the preimage of
  the basic open, i.e. the transition morphism of a basic-open inclusion `D(f) ⊆ U` identifies
  `Proj Γ(D(f), 𝒜)` with the preimage of `D(f)` in `Proj Γ(U, 𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.isPullback_transition`: **the cartesian square of
  Tag 01NO**, hence the equifiberedness that the relative glueing of Tag 01LH asks for.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.isPullback_chart`: each chart is cartesian over its
  affine open, i.e. `Proj Γ(U, 𝒜)` is the preimage of `U` in `Proj_S(𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.chart_relativeProjToBase` and
  `Stacks.AlgebraicGeometry.RelativeProjGlue.transition_comp_chart`: the charts are compatible
  with the structure morphisms and with the transitions.

## Implementation notes

The route from the algebra to the geometry is: on the standard chart `D₊(h)` of `Proj Γ(U, 𝒜)`,
Mathlib's `AlgebraicGeometry.Proj.awayι_comp_map` describes the transition morphism as
`Spec` of the map of degree-zero localizations, and
`Stacks.AlgebraicGeometry.RelativeProjGlue.isLocalization_away_map` says that map is a
localization away from one element. Both legs of that square are open immersions and
`AlgebraicGeometry.Proj.map_preimage_basicOpen` holds by `rfl`, so
`AlgebraicGeometry.IsOpenImmersion.isPullback` makes the square cartesian *without* knowing
anything about the transition morphism yet; being an open immersion is Zariski-local at the
target, so the transition is an open immersion, and its image is computed chart by chart.

Several transparency hazards arise here and are worth recording.

* `(U.basicOpen f).toOpens` and `S.basicOpen f` are equal by `rfl` but not at `implicit`
  transparency, and `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen` is a `def`. A proof of
  `S.basicOpen f ≤ U.toOpens` placed where a proof of `(U.basicOpen f).toOpens ≤ U.toOpens` is
  expected therefore defeats instance search for `IsOpenImmersion (S.homOfLE …)` and every
  `rw` whose pattern mentions `S.homOfLE`. The general statements below are indexed by an
  arbitrary `h : U.toOpens ≤ V.toOpens` for exactly this reason, and the basic-open case is
  reached by substituting `V.basicOpen f = U` rather than by rewriting a proof.
* `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen` being a `def` also means `𝒜.res`
  cannot infer its two site arguments from the type of the inclusion proof; they are given by
  name at every occurrence, and the *same* spelling has to be used in a lemma and at its use
  site or `rw` will not match.
* `CategoryTheory.Limits.pullback.snd` carries a `HasPullback` instance argument, and `rw`
  transports the instance rather than re-synthesizing it, so a freshly built
  `CategoryTheory.IsPullback.of_hasPullback` does not `rw`-match a `pullback.snd` that a previous
  `rw` produced. `CategoryTheory.IsPullback.isoIsPullback` between the two squares, applied with
  `▸` at an explicitly stated type, is what works.
* `CategoryTheory.Limits.HasColimit` of the glued functor is *not* found by instance search here,
  exactly as in `Mathlib/AlgebraicGeometry/Normalization.lean`, which has to name the
  `IsLocallyDirected` instance of a relative glueing datum by hand. The instance
  `isLocallyDirected_chartFunctor` below is that same workaround, and without it `colimit.ι`
  and `colimit.w` cannot be written.
* `AlgebraicGeometry.Scheme.Hom.opensRange` takes `IsOpenImmersion` as an instance argument, so
  statements about the *set* range of a morphism not yet known to be an open immersion are
  phrased with `Set.range … .base`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)

## Not done here

The comparison isomorphisms `θ` on the twisting sheaves `𝒪(n)` of Tags 01NO and 01NP are not
used here, so `Proj_S(𝒜)` carries no twists in this file. Over Situation 01NN they are
`Stacks.ProjTwistComparison.twistMap`, invertible by
`Stacks.RelativeProj.Situation.isIso_twistMap_gradedSectionRestriction`, and Tag 01NP with both of
its assertions is `Stacks.RelativeProj.Situation.projInclusionMap_and_twistMap_trans`. Nothing
is said about quasi-compactness, separatedness or properness of `relativeProjToBase`, nor about
the case of a graded algebra generated in degree one. No stacks attribute for 01NO, 01NP or 01NQ
is attached to anything in this file.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
open HomogeneousLocalization TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.RelativeProjGlue

universe u

section General

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) {s : A} (hs : s ∈ 𝒜 0) [Algebra A B]
  (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away s B]

include hs halg in
/-- `Spec` of the map of degree-zero localizations induced by a graded localization away from a
degree-zero element is an open immersion. -/
public theorem isOpenImmersion_specMap_awayMap {d : ℕ} {h : A} (hh : h ∈ 𝒜 d) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Away.map ψ h))) := by
  let := (Away.map ψ h).toAlgebra
  have := isLocalization_away_map 𝒜 ℬ ψ hs halg hh
  exact IsOpenImmersion.of_isLocalization
    (S := Away ℬ (ψ h)) (fromZeroRingHom 𝒜 (Submonoid.powers h) ⟨s, hs⟩)

include hs halg in
/-- Its image is the basic open of the degree-zero element, viewed in the degree-zero
localization. Phrased with `Set.range` rather than
`AlgebraicGeometry.Scheme.Hom.opensRange`, which would need the open-immersion instance in the
statement. -/
public theorem range_specMap_awayMap {d : ℕ} {h : A} (hh : h ∈ 𝒜 d) :
    Set.range (Spec.map (CommRingCat.ofHom (Away.map ψ h))).base =
      (PrimeSpectrum.basicOpen (fromZeroRingHom 𝒜 (Submonoid.powers h) ⟨s, hs⟩) :
        Set (PrimeSpectrum (Away 𝒜 h))) := by
  let := (Away.map ψ h).toAlgebra
  have := isLocalization_away_map 𝒜 ℬ ψ hs halg hh
  exact PrimeSpectrum.localization_away_comap_range (Away ℬ (ψ h)) _

omit [Algebra A B] in
/-- **The standard chart of Mathlib's `AlgebraicGeometry.Proj.map` is a pullback.** For `f`
homogeneous of positive degree, the square relating `Spec` of the map of degree-zero
localizations to `AlgebraicGeometry.Proj.map ψ` along the two standard open immersions is
cartesian.

No hypothesis on `ψ` beyond Mathlib's own is needed: the two vertical legs are open immersions
and `AlgebraicGeometry.Proj.map_preimage_basicOpen` holds by `rfl`, so the square is cartesian
before anything is known about `AlgebraicGeometry.Proj.map ψ` itself. -/
public theorem isPullback_awayι_map (hψ : irrelevant ℬ ≤ (irrelevant 𝒜).map ψ)
    {d : ℕ} (hd : 0 < d) {h : A} (hh : h ∈ 𝒜 d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map ψ h)))
      (Proj.awayι ℬ (ψ h) (ψ.map_mem hh) hd) (Proj.awayι 𝒜 h hh hd) (Proj.map ψ hψ) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map ψ hψ hd h hh) ?_
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

include hs halg in
/-- **Tag 01NO, the open-immersion half.** For a graded ring map exhibiting `B` as a
localization of `A` away from an element of degree `0`, Mathlib's `AlgebraicGeometry.Proj.map` is
an open immersion.

Proved by descent along the standard affine cover of `Proj 𝒜`: being an open immersion is
Zariski-local at the target, and over each chart the morphism is `Spec` of a localization map. -/
public theorem isOpenImmersion_projMap (hψ : irrelevant ℬ ≤ (irrelevant 𝒜).map ψ) :
    IsOpenImmersion (Proj.map ψ hψ) := by
  refine IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover fun i => ?_
  have hpb := (isPullback_awayι_map 𝒜 ℬ ψ hψ i.1.2 i.2.2).flip
  have hu := IsPullback.of_hasPullback (Proj.map ψ hψ) (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2)
  have h2 : IsOpenImmersion ((IsPullback.isoIsPullback _ _ hu hpb).hom ≫
      Spec.map (CommRingCat.ofHom (Away.map ψ (i.2 : A)))) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion) _ _).mpr
      (isOpenImmersion_specMap_awayMap 𝒜 ℬ ψ hs halg i.2.2)
  have h4 : IsOpenImmersion (pullback.snd (Proj.map ψ hψ)
      (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2)) :=
    (IsPullback.isoIsPullback_hom_snd (Proj ℬ) _ hu hpb) ▸ h2
  exact h4

end General

section Relative

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- The transition morphism of a quasi-coherent graded algebra along a basic open inclusion of
affine opens is an open immersion. -/
@[ega "II 3.1.1" "ρ_{U', special case"]
public instance isOpenImmersion_resMap (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    IsOpenImmersion (𝒜.resMap U f) := by
  rw [𝒜.resMap_eq_map U f]
  let := 𝒜.algebra (U := U.basicOpen f) (V := U) (S.basicOpen_le f)
  have := 𝒜.isLocalization U f
  exact isOpenImmersion_projMap _ _ _ (𝒜.str_mem U f)
    (𝒜.algebraMap_eq (U := U.basicOpen f) (V := U) (S.basicOpen_le f)) _

/-- The degree-zero corestriction of the structure morphism, read as an element of the
degree-zero part together with its membership proof. -/
public theorem strZero_eq (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    𝒜.strZero U f = ⟨𝒜.str U f, 𝒜.str_mem U f⟩ :=
  Subtype.ext (𝒜.coe_strZero_apply U f)

/-- **The chartwise form of the image of a transition morphism.** On the standard chart `D₊(h)`
of `Proj Γ(U, 𝒜)`, the preimage of a basic open `D(f) ⊆ U` under the structure morphism to `S` is
the basic open of `f / 1` in the degree-zero localization.

This is the geometric side of the brick: the element cut out here is exactly the one that
`Stacks.AlgebraicGeometry.RelativeProjGlue.isLocalization_away_map` localizes at. -/
public theorem awayι_preimage_toBase_preimage_basicOpen (U : S.AffineZariskiSite)
    (f : Γ(S, U.toOpens)) {d : ℕ} (hd : 0 < d) {h : 𝒜.ring U} (hh : h ∈ 𝒜.grading U d) :
    Proj.awayι (𝒜.grading U) h hh hd ⁻¹ᵁ (𝒜.toBase U ⁻¹ᵁ S.basicOpen f) =
      PrimeSpectrum.basicOpen
        (fromZeroRingHom (𝒜.grading U) (Submonoid.powers h) (𝒜.strZero U f)) := by
  have key : Proj.awayι (𝒜.grading U) h hh hd ≫ 𝒜.toBase U =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom (𝒜.grading U) (Submonoid.powers h))) ≫
        Spec.map (𝒜.strZero U) ≫ U.2.fromSpec := by
    rw [GradedAlgebra.toBase, Proj.awayι_toSpecZero_assoc]
  rw [← Scheme.Hom.comp_preimage, key]
  simp only [Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_basicOpen,
    SpecMap_preimage_basicOpen]
  exact SpecMap_preimage_basicOpen _ _

/-- The transition morphism along a basic open inclusion, read on the standard chart attached to
a homogeneous element of positive degree. -/
public theorem awayι_comp_resMap (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens))
    {d : ℕ} (hd : 0 < d) {h : 𝒜.ring U} (hh : h ∈ 𝒜.grading U d) :
    Proj.awayι (𝒜.grading (U.basicOpen f))
        (𝒜.res (U := U.basicOpen f) (V := U) (S.basicOpen_le f) h)
        ((𝒜.res (U := U.basicOpen f) (V := U) (S.basicOpen_le f)).map_mem hh) hd ≫
          𝒜.resMap U f =
      Spec.map (CommRingCat.ofHom (Away.map
          (𝒜.res (U := U.basicOpen f) (V := U) (S.basicOpen_le f)) h)) ≫
        Proj.awayι (𝒜.grading U) h hh hd := by
  rw [𝒜.resMap_eq_map U f]
  exact Proj.awayι_comp_map _ _ hd h hh

/-- `Stacks.AlgebraicGeometry.RelativeProjGlue.range_specMap_awayMap` for the restriction map of
a quasi-coherent graded algebra: the chart of the smaller affine open is the locus where the
section cutting it out is invertible. -/
public theorem range_specMap_awayMap_res (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens))
    {d : ℕ} {h : 𝒜.ring U} (hh : h ∈ 𝒜.grading U d) :
    Set.range (Spec.map (CommRingCat.ofHom (Away.map
        (𝒜.res (U := U.basicOpen f) (V := U) (S.basicOpen_le f)) h))).base =
      (PrimeSpectrum.basicOpen (fromZeroRingHom (𝒜.grading U) (Submonoid.powers h)
        (𝒜.strZero U f)) : Set (PrimeSpectrum (Away (𝒜.grading U) h))) := by
  let := 𝒜.algebra (U := U.basicOpen f) (V := U) (S.basicOpen_le f)
  have := 𝒜.isLocalization U f
  rw [strZero_eq 𝒜 U f]
  exact range_specMap_awayMap _ _ _ (𝒜.str_mem U f)
    (𝒜.algebraMap_eq (U := U.basicOpen f) (V := U) (S.basicOpen_le f)) hh

/-- A point of a standard chart of `Proj Γ(U, 𝒜)` lying over the basic open `D(f)` is in the
image of the transition morphism. This is the surjectivity half of
`Stacks.AlgebraicGeometry.RelativeProjGlue.opensRange_resMap`. -/
public theorem mem_range_resMap_of_awayι (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens))
    {d : ℕ} (hd : 0 < d) {h : 𝒜.ring U} (hh : h ∈ 𝒜.grading U d)
    (y : Spec (CommRingCat.of (Away (𝒜.grading U) h)))
    (hy : Proj.awayι (𝒜.grading U) h hh hd y ∈ 𝒜.toBase U ⁻¹ᵁ S.basicOpen f) :
    Proj.awayι (𝒜.grading U) h hh hd y ∈ Set.range (𝒜.resMap U f) := by
  have hmem : y ∈ Proj.awayι (𝒜.grading U) h hh hd ⁻¹ᵁ (𝒜.toBase U ⁻¹ᵁ S.basicOpen f) := hy
  rw [awayι_preimage_toBase_preimage_basicOpen 𝒜 U f hd hh] at hmem
  obtain ⟨z, hz⟩ : y ∈ Set.range (Spec.map (CommRingCat.ofHom (Away.map
      (𝒜.res (U := U.basicOpen f) (V := U) (S.basicOpen_le f)) h))).base := by
    rw [range_specMap_awayMap_res 𝒜 U f hh]
    exact hmem
  refine ⟨Proj.awayι (𝒜.grading (U.basicOpen f))
    (𝒜.res (U := U.basicOpen f) (V := U) (S.basicOpen_le f) h)
    ((𝒜.res (U := U.basicOpen f) (V := U) (S.basicOpen_le f)).map_mem hh) hd z, ?_⟩
  rw [← Scheme.Hom.comp_apply, awayι_comp_resMap 𝒜 U f hd hh, Scheme.Hom.comp_apply, hz]

/-- **The image of a transition morphism.** For a basic open inclusion `D(f) ⊆ U` of affine
opens, the transition morphism identifies `Proj Γ(D(f), 𝒜)` with the preimage of `D(f)` under the
structure morphism of `Proj Γ(U, 𝒜)` to `S`.

One inclusion is formal, since the structure morphism of the smaller chart lands in `D(f)`; the
other is checked chart by chart on the standard affine cover. -/
public theorem opensRange_resMap (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    (𝒜.resMap U f).opensRange = 𝒜.toBase U ⁻¹ᵁ S.basicOpen f := by
  refine TopologicalSpace.Opens.ext (Set.Subset.antisymm ?_ ?_)
  · rintro x ⟨y, rfl⟩
    change 𝒜.toBase U (𝒜.resMap U f y) ∈ S.basicOpen f
    rw [← Scheme.Hom.comp_apply, 𝒜.resMap_toBase U f, ← 𝒜.toOpen_ι, Scheme.Hom.comp_apply]
    exact (𝒜.toOpen (U.basicOpen f) y).2
  · intro x hx
    obtain ⟨i, y, rfl⟩ : ∃ (i : _) (y : _),
        (Proj.affineOpenCover (𝒜.grading U)).openCover.f i y = x :=
      ⟨_, _, ((Proj.affineOpenCover (𝒜.grading U)).openCover.covers x).choose_spec⟩
    exact mem_range_resMap_of_awayι 𝒜 U f i.1.2 i.2.2 y hx

/-- A morphism of the small affine Zariski site is a basic open inclusion. -/
private theorem exists_basicOpen_eq {U V : S.AffineZariskiSite} (hUV : U ≤ V) :
    ∃ f : Γ(S, V.toOpens), V.basicOpen f = U :=
  hUV.imp fun _ hf => Subtype.ext hf

/-- **Tag 01NO: the square of a nested pair of affine opens is cartesian.** For a morphism
`U ⟶ V` of `AlgebraicGeometry.Scheme.AffineZariskiSite`, the square formed by the transition
morphism, the two structure morphisms and the inclusion `U ⊆ V` is a pullback.

This is the equifiberedness that `AlgebraicGeometry.Scheme.Cover.RelativeGluingData` asks for,
and it is what `StacksFrontier.AlgebraicGeometry.RelativeProj.Local` left open. The inclusion
proof is an explicit argument, independent of the proof that `U ≤ V` in the site, because a
proof of `(V.basicOpen f).toOpens ≤ V.toOpens` and a proof of `S.basicOpen f ≤ V.toOpens` are
interchangeable only at default transparency. -/
public theorem isPullback_transition {U V : S.AffineZariskiSite} (hUV : U ≤ V)
    (h : U.toOpens ≤ V.toOpens)
    (hdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤) :
    IsPullback (𝒜.transition h hdom) (𝒜.toOpen U) (𝒜.toOpen V) (S.homOfLE h) := by
  obtain ⟨f, rfl⟩ := exists_basicOpen_eq hUV
  have hi : IsOpenImmersion (S.homOfLE h) := inferInstance
  have hoi : IsOpenImmersion (𝒜.transition h hdom) := isOpenImmersion_resMap 𝒜 V f
  refine (@IsOpenImmersion.isPullback _ _ _ _ (𝒜.toOpen (V.basicOpen f))
    (𝒜.transition h hdom) (S.homOfLE h) (𝒜.toOpen V) hoi hi
    (𝒜.transition_toOpen h hdom) ?_).flip
  rw [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, 𝒜.toOpen_ι]
  exact (opensRange_resMap 𝒜 V f).symm

/-- The morphism of projective spectra induced by a restriction map is everywhere defined for
every morphism of the small affine Zariski site, those being exactly the basic open
inclusions. -/
public theorem mapDomain_res_eq_top_of_le {U V : S.AffineZariskiSite} (hUV : U ≤ V)
    (h : U.toOpens ≤ V.toOpens) :
    mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤ := by
  obtain ⟨f, rfl⟩ := exists_basicOpen_eq hUV
  exact 𝒜.mapDomain_res_eq_top V f

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` holds for every morphism of the small
affine Zariski site. -/
public theorem irrelevant_le_map_res_of_le {U V : S.AffineZariskiSite} (hUV : U ≤ V)
    (h : U.toOpens ≤ V.toOpens) :
    irrelevant (𝒜.grading U) ≤ (irrelevant (𝒜.grading V)).map (𝒜.res h) := by
  obtain ⟨f, rfl⟩ := exists_basicOpen_eq hUV
  exact 𝒜.irrelevant_le_map_res V f

/-- **The charts as a functor.** `U ↦ Proj Γ(U, 𝒜)` on the small affine Zariski site of `S`,
with the transition morphisms of
`StacksFrontier.AlgebraicGeometry.RelativeProj.Local` as its action on arrows. Functoriality is
Tag 01NP. -/
public def chartFunctor : S.AffineZariskiSite ⥤ Scheme.{u} where
  obj U := 𝒜.projOver U
  map {_U _V} φ := 𝒜.transition (Scheme.AffineZariskiSite.toOpens_mono φ.le)
    (mapDomain_res_eq_top_of_le 𝒜 φ.le _)
  map_id U := 𝒜.transition_id U _
  map_comp {_U _V _W} φ χ :=
    (𝒜.transition_comp (Scheme.AffineZariskiSite.toOpens_mono φ.le)
      (Scheme.AffineZariskiSite.toOpens_mono χ.le)
      (irrelevant_le_map_res_of_le 𝒜 φ.le _) (irrelevant_le_map_res_of_le 𝒜 χ.le _)
      _ _ _).symm

/-- **The relative glueing datum of Tag 01NQ.** The chart functor together with the structure
morphisms to the affine opens, whose squares are cartesian by
`Stacks.AlgebraicGeometry.RelativeProjGlue.isPullback_transition`. -/
public def relativeGluingData :
    (Scheme.AffineZariskiSite.directedCover S).RelativeGluingData where
  functor := chartFunctor 𝒜
  natTrans :=
    { app := fun U => 𝒜.toOpen U
      naturality := fun {_U _V} φ => 𝒜.transition_toOpen
        (Scheme.AffineZariskiSite.toOpens_mono φ.le)
        (mapDomain_res_eq_top_of_le 𝒜 φ.le _) }
  equifibered := fun {_U _V} φ => isPullback_transition 𝒜 φ.le
    (Scheme.AffineZariskiSite.toOpens_mono φ.le) (mapDomain_res_eq_top_of_le 𝒜 φ.le _)

/-- **The relative homogeneous spectrum `Proj_S(𝒜)`**, obtained by glueing the charts. -/
public abbrev relativeProj : Scheme.{u} := (relativeGluingData 𝒜).glued

/-- The structure morphism `Proj_S(𝒜) ⟶ S`. -/
public abbrev relativeProjToBase : relativeProj 𝒜 ⟶ S := (relativeGluingData 𝒜).toBase

/-- The glued diagram is locally directed. Named rather than left to instance search, exactly as
`Mathlib/AlgebraicGeometry/Normalization.lean` has to do for its own relative glueing datum:
without this the colimit of `chartFunctor` has no `CategoryTheory.Limits.HasColimit` instance and
`colimit.ι` cannot be written. -/
public instance isLocallyDirected_chartFunctor :
    ((relativeGluingData 𝒜).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The chart of the relative homogeneous spectrum over an affine open `U` of the base, i.e. the
open immersion `Proj Γ(U, 𝒜) ⟶ Proj_S(𝒜)`. -/
public abbrev chart (U : S.AffineZariskiSite) : 𝒜.projOver U ⟶ relativeProj 𝒜 :=
  colimit.ι (relativeGluingData 𝒜).functor U

/-- The chart over an affine open is compatible with the structure morphisms to the base. -/
public theorem chart_relativeProjToBase (U : S.AffineZariskiSite) :
    chart 𝒜 U ≫ relativeProjToBase 𝒜 = 𝒜.toBase U :=
  ((relativeGluingData 𝒜).ι_toBase U).trans (𝒜.toOpen_ι U)

/-- **Tag 01NQ: each chart is the preimage of its affine open.** The square formed by the chart,
the structure morphism of the chart, the inclusion of the affine open and the structure morphism
of the relative homogeneous spectrum is cartesian. -/
public theorem isPullback_chart (U : S.AffineZariskiSite) :
    IsPullback (𝒜.toOpen U) (chart 𝒜 U) U.toOpens.ι (relativeProjToBase 𝒜) :=
  (relativeGluingData 𝒜).isPullback_natTrans_ι_toBase U

/-- The charts are compatible with the transition morphisms. -/
public theorem transition_comp_chart {U V : S.AffineZariskiSite} (φ : U ⟶ V) :
    𝒜.transition (Scheme.AffineZariskiSite.toOpens_mono φ.le)
        (mapDomain_res_eq_top_of_le 𝒜 φ.le _) ≫ chart 𝒜 V = chart 𝒜 U :=
  colimit.w (relativeGluingData 𝒜).functor φ

end Relative

end Stacks.AlgebraicGeometry.RelativeProjGlue

end
