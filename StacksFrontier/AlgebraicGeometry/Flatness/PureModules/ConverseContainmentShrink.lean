module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ConverseChartCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ContainmentConstructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible

/-!
# Shrinking the base so that the chart covers the relative assassin fibrewise

The purity criterion of Tag 05L4, run forward at a chart of Tag 05KW, says that the image of
`X' ⟶ X ×_S S'` contains every point of the relative assassin of the base change lying over a
point of `S'` that specializes to the distinguished point `s'`. This file turns that statement
about a *specialization-closed* family of points into a statement over an honest affine open
neighbourhood of `s'`.

The mechanism is the pair Tag 05KR / Tag 05LW. Tag 05KR
(`Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment`) says that the locus of
points `t` of the base over which the associated points of the fibre lie in a given open
subscheme is locally constructible; Tag 05LW
(`AlgebraicGeometry.mem_nhds_of_isLocallyConstructible_of_specializes_subset`) says that a locally
constructible set containing every generalization of a point contains a neighbourhood of it. The
range statement is exactly the hypothesis of the second applied to the locus of the first, for the
open subscheme `g(X') ⊆ X ×_S S'`. Mathlib's `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`
then shrinks the resulting neighbourhood to an affine open.

Two side conditions are discharged here. The image `g(X')` is open because the induced morphism
`X' ⟶ X ×_S S'` is étale (`AlgebraicGeometry.etale_pullback_lift_of_etale`), hence an open map;
and it is quasi-compact over the base because it is the image of the affine, hence compact, scheme
`X'`, which is what Tag 05KR needs of the open subscheme.

## Main results

* `AlgebraicGeometry.exists_affineOpen_fibrewiseContainment_of_mem_range`: the shrink, from the
  range statement.
* `AlgebraicGeometry.exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong`: the shrink
  composed with Tag 05KW and Tag 05L4, so that the only geometric input is purity along `X_s`.

## References

* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
* [Stacks Project, Tag 05L4](https://stacks.math.columbia.edu/tag/05L4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The image of the chart in the base change, as an open subscheme. It is open because the
induced morphism `X' ⟶ X ×_S S'` is étale, hence an open map. -/
def chartImageOpens {X S X' : Scheme.{u}} (f : X ⟶ S) {s : S} (U : EtaleNeighborhood S s)
    (p : X' ⟶ U.scheme) (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase) :
    (pullback (C := Scheme.{u}) f U.toBase).Opens :=
  letI : Etale (pullback.lift g p hcomm) := etale_pullback_lift_of_etale f U.toBase g p hcomm
  ⟨Set.range (pullback.lift g p hcomm), (pullback.lift g p hcomm).isOpenMap.isOpen_range⟩

/-- Tags 05KR and 05LW applied to the range statement of Tag 05L4: there is an affine open
neighbourhood `W₀` of the distinguished point of the neighbourhood over every point of which the
associated points of the fibre of the base-changed module lie in the image of the chart.

The hypothesis `hrange` is the conclusion of
`AlgebraicGeometry.relativeAssassin_specializing_mem_range_of_isPureAlong`; no purity is assumed
directly here. -/
theorem exists_affineOpen_fibrewiseContainment_of_mem_range
    {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    {s : S} (U : EtaleNeighborhood S s) [IsAffine U.scheme]
    (p : X' ⟶ U.scheme) [IsAffine X'] (g : X' ⟶ X) [Etale g]
    (hcomm : g ≫ f = p ≫ U.toBase)
    (hrange : ∀ x : pullback (C := Scheme.{u}) f U.toBase,
      x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
          ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) →
        pullback.snd f U.toBase x ⤳ U.point →
          x ∈ Set.range (pullback.lift g p hcomm)) :
    ∃ WO : (U.scheme).Opens, IsAffineOpen WO ∧ U.point ∈ WO ∧
      (WO : Set U.scheme) ⊆ Stacks.RelativeAssassin.fibrewiseContainment
        (pullback.snd f U.toBase)
        ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)
        (chartImageOpens f U p g hcomm) := by
  set q := pullback.lift g p hcomm with hq
  set fU := pullback.snd f U.toBase with hfU
  set FU := (Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F with hFU
  set W : (pullback (C := Scheme.{u}) f U.toBase).Opens := chartImageOpens f U p g hcomm with hW
  -- `W` is quasi-compact over the base, being the image of the affine scheme `X'`
  have hWcompact : IsCompact (W : Set (pullback (C := Scheme.{u}) f U.toBase)) :=
    isCompact_range q.continuous
  have hWcs : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hWcompact
  have hWqc : QuasiCompact (W.ι ≫ fU) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  -- Tag 05KR: the fibrewise containment locus is locally constructible
  have hfp : FinitePresentation fU := ⟨inferInstance, inferInstance, inferInstance⟩
  have hFUqc : FU.IsQuasicoherent := isQuasicoherent_pullback_obj _ F
  have hcons : IsLocallyConstructible
      (Stacks.RelativeAssassin.fibrewiseContainment fU FU W) :=
    Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment fU hfp FU W
  -- every generalization of the distinguished point lies in that locus
  have hsub : {t : U.scheme | t ⤳ U.point} ⊆
      Stacks.RelativeAssassin.fibrewiseContainment fU FU W := by
    intro t ht ξ hξ
    have h1 : fU.fiberι t ξ ∈ Stacks.Divisors.relativeAssassin fU FU :=
      (Stacks.Divisors.mem_relativeAssassin fU FU _).mpr ⟨t, ξ, hξ, rfl⟩
    have h2 : fU (fU.fiberι t ξ) = t := (fU.range_fiberι t).le ⟨ξ, rfl⟩
    refine hrange _ h1 ?_
    rw [h2]
    exact ht
  -- Tag 05LW, then shrink to an affine open
  have hnhds := mem_nhds_of_isLocallyConstructible_of_specializes_subset hcons hsub
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.mp hnhds
  obtain ⟨WO, hWOaff, hWOmem, hWOsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⟨V, hVopen⟩ : (U.scheme).Opens)) hVmem
  exact ⟨WO, hWOaff, hWOmem, hWOsub.trans hVsub⟩

/-- The shrink of `AlgebraicGeometry.exists_affineOpen_fibrewiseContainment_of_mem_range`
composed with Tag 05KW and the forward direction of Tag 05L4, so that the only geometric
hypothesis is purity of `ℱ` along `X_s`.

This is the whole geometric input of the converse of Tag 05MD, packaged: an affine elementary
étale neighbourhood `S'` of `s`, an affine chart `X'` étale over `X` and of finite type over `S'`
whose sections are projective over `Γ(S', 𝒪_{S'})`, and an affine open `W₀ ∋ s'` of `S'` over
every point of which the associated points of the fibre of `ℱ ×_S S'` lie in the image of
`X' ⟶ X ×_S S'`. -/
theorem exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hpure : IsPureAlong
      ({ S := S
         X := X
         f := f
         F := F
         isFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
         s := s } : PrePureSituation.{u})) :
    ∃ (U : EtaleNeighborhood S s) (X' : Scheme.{u}) (p : X' ⟶ U.scheme) (g : X' ⟶ X)
      (hcomm : g ≫ f = p ≫ U.toBase) (_ : IsAffine U.scheme) (_ : IsAffine X') (_ : Etale g),
      U.IsElementary ∧ LocallyOfFiniteType p ∧
      (let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
       letI : Module Γ(U.scheme, ⊤) N := Module.compHom N p.appTop.hom
       Module.Projective Γ(U.scheme, ⊤) N) ∧
      ∃ WO : (U.scheme).Opens, IsAffineOpen WO ∧ U.point ∈ WO ∧
        (WO : Set U.scheme) ⊆ Stacks.RelativeAssassin.fibrewiseContainment
          (pullback.snd f U.toBase)
          ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)
          (chartImageOpens f U p g hcomm) := by
  obtain ⟨U, X', p, g, hcomm, hUe, hUa, hX'a, hgE, hLFT, hproj, hrange⟩ :=
    exists_chart_relativeAssassin_specializing_mem_range f F s hflat hpure
  refine ⟨U, X', p, g, hcomm, hUa, hX'a, hgE, hUe, hLFT, hproj, ?_⟩
  exact exists_affineOpen_fibrewiseContainment_of_mem_range f F U p g hcomm hrange

end AlgebraicGeometry

end
