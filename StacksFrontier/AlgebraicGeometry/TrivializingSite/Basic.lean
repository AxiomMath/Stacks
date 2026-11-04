module

public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.AffineBasis
public import StacksFrontier.AlgebraicGeometry.RelativeProjGeneral.Basic

/-!
# The trivializing affine opens of an invertible module, and the charts they index

Let `L` be an invertible module on a scheme `X`. The affine opens `U` of `X` over which `L`
becomes isomorphic to the structure sheaf are closed under shrinking and form a basis of the
topology of `X`; they therefore cut out a full sub-preorder `Site L` of the small affine Zariski
site `X.AffineZariskiSite` whose members still cover `X`.

For a quasi-coherent graded algebra `𝒜` on a base scheme `S`, the relative homogeneous spectrum
`Proj_S(𝒜)` of Tag 01NQ is glued from the charts `Proj Γ(U, 𝒜)` indexed by the *whole* small
affine Zariski site of `S`. This file restricts that chart family to `Site L` and checks that
the restriction is still a locally directed open cover of `Proj_S(𝒜)`. That cover is the index
category over which Tag 02NC glues its chart isomorphisms: it is simultaneously fine enough for
`L` to be trivial on each member and coarse enough to cover `Proj_S(𝒜)`.

## Main definitions

* `Stacks.AlgebraicGeometry.TrivializingSite.IsTrivializing`: an affine open of the small affine
  Zariski site over which the invertible module is isomorphic to the structure sheaf.
* `Stacks.AlgebraicGeometry.TrivializingSite.Site`: the trivializing affine opens, as a
  sub-preorder of the small affine Zariski site.
* `Stacks.AlgebraicGeometry.TrivializingSite.trivCover`: the open cover of the relative
  homogeneous spectrum by the charts over the trivializing affine opens.

## Main results

* `Stacks.AlgebraicGeometry.TrivializingSite.IsTrivializing.mono`: **triviality of an invertible
  module on an affine open passes to smaller affine opens.**
* `Stacks.AlgebraicGeometry.TrivializingSite.exists_isTrivializing_le`: **a trivializing affine
  open can be found inside any affine open of the site, around any of its points.**
* `Stacks.AlgebraicGeometry.TrivializingSite.iSup_toOpens_eq_top`: **the trivializing affine
  opens cover the scheme.**
* `Stacks.AlgebraicGeometry.TrivializingSite.locallyDirected_trivCover`: the restricted chart
  family is a locally directed cover, with the transition morphisms of the chart functor.

## Implementation notes

The triviality predicate is phrased in the localized-site spelling
`L.over U.toOpens ≅ unit (X.ringCatSheaf.over U.toOpens)`, the one in which
`Stacks.SheafOfModules.isoUnitOverOfHom` restricts a trivialization along an arbitrary morphism
of opens; that lemma *is* `IsTrivializing.mono`, and no sectionwise computation appears. The
refinement lemma goes through
`Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible`, which produces an
arbitrary affine open, and then shrinks it to a *basic* open of the ambient member of the site
with `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`, because the arrows of
`AlgebraicGeometry.Scheme.AffineZariskiSite` are exactly the basic open inclusions.

`Site L` is a reducible abbreviation for the subtype rather than an opaque `def`. It therefore
inherits `Subtype.partialOrder`, the coercion to `AlgebraicGeometry.Scheme.AffineZariskiSite`
and the small category the preorder induces — the last being what
`AlgebraicGeometry.Scheme.Cover.LocallyDirected` asks of a cover's index type — with no
instances declared by hand. Opacity was tried first and is not workable here: with `Site` a
`def`, an element written `⟨V, hV⟩` has the subtype as its type while the cover's index field
has `Site L`, and the two are not interchangeable at `implicit` transparency, which breaks every
`rw` inside the directedness proof and the `rfl` of
`Stacks.AlgebraicGeometry.TrivializingSite.trans_trivCover`.

The surjectivity of the restricted chart family is read off the description of the image of a
chart as the inverse image of its affine open,
`Stacks.AlgebraicGeometry.TrivializingSite.opensRange_chart`, which is Mathlib's
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι` for the
glueing datum of Tag 01NQ. The directedness argument is Mathlib's proof for
`AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover` transported one level up: a point of
an intersection of two charts is pushed down to the base, a common basic open of the two affine
opens around that image is produced by
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`, and the refinement lemma shrinks it to a
trivializing one.

The transition maps of the cover are written as `GradedAlgebra.transition` applied to the
inclusion of opens, not as `chartFunctor.map` of the arrow of the site, even though the two are
definitionally equal. Only the first has a type that `(trivCover 𝒜 L).X` matches without
unfolding `Stacks.AlgebraicGeometry.RelativeProjGlue.chartFunctor`, and with the second the
statement of the `directed` field is ill-typed at `implicit` transparency, so no rewrite fires
inside it. Their three properties are then
`Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_comp_of_le_opens`,
`Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_comp_chart_of_le_opens` and
`Stacks.AlgebraicGeometry.RelativeProjGeneral.isOpenImmersion_transition_of_le_opens`, whose
hypotheses are the inclusion of opens itself rather than an arrow of the site, which is what
makes them usable here.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjGlue

namespace Stacks.AlgebraicGeometry.TrivializingSite

universe u

section Trivializing

variable {X : Scheme.{u}} (L : X.Modules)

/-- **An affine open of the small affine Zariski site over which an invertible module is
trivial.** The trivialization is asked for in the localized-site spelling
`L.over U ≅ unit (𝒪_X.over U)`, the one `Stacks.SheafOfModules.isoUnitOverOfHom` restricts. -/
public def IsTrivializing (U : X.AffineZariskiSite) : Prop :=
  Nonempty (L.over U.toOpens ≅ SheafOfModules.unit (X.ringCatSheaf.over U.toOpens))

/-- **Triviality passes to smaller affine opens.** A trivialization restricts along the
inclusion of opens underlying an arrow of the small affine Zariski site. -/
public theorem IsTrivializing.mono {U V : X.AffineZariskiSite} (h : U ≤ V)
    (hV : IsTrivializing L V) : IsTrivializing L U :=
  ⟨Stacks.SheafOfModules.isoUnitOverOfHom L
    (homOfLE (Scheme.AffineZariskiSite.toOpens_mono h)) hV.some⟩

/-- **The trivializing affine opens**, as a sub-preorder of the small affine Zariski site of
`X`. Its arrows are the basic open inclusions between members, so it is a full subcategory of
`AlgebraicGeometry.Scheme.AffineZariskiSite`. -/
public abbrev Site : Type u := { U : X.AffineZariskiSite // IsTrivializing L U }

namespace Site

variable {L}

/-- An inequality of trivializing affine opens is an inequality in the small affine Zariski
site. -/
public theorem val_le_val {U V : Site L} (h : U ≤ V) : U.1 ≤ V.1 := h

/-- An arrow of trivializing affine opens is an arrow of the small affine Zariski site. -/
public abbrev homVal {U V : Site L} (h : U ⟶ V) : U.1 ⟶ V.1 := homOfLE (val_le_val h.le)

end Site

end Trivializing

section Refinement

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **A trivializing affine open can be found inside any member of the site, around any of its
points.** The invertible module is trivial on some affine open neighbourhood inside the given
one; that neighbourhood is then shrunk to a basic open of the given member, which is what an
arrow of `AlgebraicGeometry.Scheme.AffineZariskiSite` is. -/
public theorem exists_isTrivializing_le (U : X.AffineZariskiSite) (x : X) (hx : x ∈ U.toOpens) :
    ∃ V : X.AffineZariskiSite, V ≤ U ∧ x ∈ V.toOpens ∧ IsTrivializing L V := by
  obtain ⟨V₀, _, hxV₀, _, ⟨e⟩⟩ :=
    Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible L hx
  obtain ⟨f, hfV₀, hxf⟩ := U.2.exists_basicOpen_le (V := V₀) ⟨x, hxV₀⟩ hx
  refine ⟨U.basicOpen f, U.basicOpen_le f, hxf, ⟨?_⟩⟩
  exact Stacks.SheafOfModules.isoUnitOverOfHom L (homOfLE hfV₀)
    (Stacks.Modules.overIsoUnitOfRestrictIsoUnit L V₀ e)

/-- **The trivializing affine opens cover the scheme.** Every point lies in an affine open, and
the refinement lemma produces a trivializing affine open inside it around that point. -/
public theorem iSup_toOpens_eq_top : (⨆ V : Site L, V.1.toOpens) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨U, hxU⟩ :=
    Opens.mem_iSup.mp ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  obtain ⟨V, _, hxV, hV⟩ := exists_isTrivializing_le L U x hxU
  exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩

end Refinement

section Cover

variable {S : Scheme.{u}} (𝒜 : RelativeProj.GradedAlgebra S) (L : S.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- Each chart of the relative homogeneous spectrum is an open immersion, being a base change
of the inclusion of its affine open. -/
public instance isOpenImmersion_chart (U : S.AffineZariskiSite) : IsOpenImmersion (chart 𝒜 U) :=
  MorphismProperty.of_isPullback (isPullback_chart 𝒜 U) inferInstance

/-- **The image of a chart of the relative homogeneous spectrum is the inverse image of its
affine open.** This is Mathlib's
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι` for the
glueing datum of Tag 01NQ. -/
public theorem opensRange_chart (U : S.AffineZariskiSite) :
    (chart 𝒜 U).opensRange = relativeProjToBase 𝒜 ⁻¹ᵁ U.toOpens := by
  rw [← Scheme.Opens.opensRange_ι U.toOpens]
  exact ((relativeGluingData 𝒜).toBase_preimage_eq_opensRange_ι U).symm

/-- A point of the relative homogeneous spectrum lying over an affine open is in the image of
the chart over that affine open. -/
public theorem mem_range_chart {U : S.AffineZariskiSite} {z : relativeProj 𝒜}
    (hz : relativeProjToBase 𝒜 z ∈ U.toOpens) : z ∈ Set.range (chart 𝒜 U).base :=
  show z ∈ (chart 𝒜 U).opensRange from (opensRange_chart 𝒜 U).symm ▸ hz

/-- **The cover of the relative homogeneous spectrum by the charts over the trivializing affine
opens.** The charts over the whole small affine Zariski site cover `Proj_S(𝒜)`; the trivializing
ones still do because they already cover the base. -/
public abbrev trivCover : (relativeProj 𝒜).OpenCover where
  I₀ := Site L
  X W := 𝒜.projOver W.1
  f W := chart 𝒜 W.1
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun z => ?_, fun W => inferInstance⟩
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp
      (show relativeProjToBase 𝒜 z ∈ (⨆ V : Site L, V.1.toOpens) from
        (iSup_toOpens_eq_top L).ge trivial)
    exact ⟨W, mem_range_chart 𝒜 hW⟩

/-- The members of the cover are the charts over the trivializing affine opens. -/
public theorem trivCover_f (W : Site L) : (trivCover 𝒜 L).f W = chart 𝒜 W.1 := rfl

/-- The objects of the cover are the charts of the relative homogeneous spectrum. -/
public theorem trivCover_X (W : Site L) : (trivCover 𝒜 L).X W = 𝒜.projOver W.1 := rfl

/-- **The restricted chart family is locally directed**, with the transition morphisms of
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition` as its transition maps, i.e.
with the action of `Stacks.AlgebraicGeometry.RelativeProjGlue.chartFunctor` on arrows.
Directedness is Mathlib's argument for
`AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover` one level up: a point of an
intersection of two charts is pushed to the base, a common basic open of the two affine opens is
found around its image, and that basic open is shrunk to a trivializing one. -/
public instance locallyDirected_trivCover : (trivCover 𝒜 L).LocallyDirected where
  trans {W W'} h := 𝒜.transition (Scheme.AffineZariskiSite.toOpens_mono (Site.val_le_val h.le))
    (mapDomain_res_eq_top_of_le 𝒜 (Site.val_le_val h.le) _)
  trans_id W := 𝒜.transition_id W.1 _
  trans_comp _ _ := (RelativeProjGeneral.transition_comp_of_le_opens 𝒜 _ _ _ _ _).symm
  w _ := RelativeProjGeneral.transition_comp_chart_of_le_opens 𝒜 _ _
  property_trans _ := RelativeProjGeneral.isOpenImmersion_transition_of_le_opens 𝒜 _ _
  directed {W W'} x := by
    obtain ⟨z, hz⟩ : ∃ z : relativeProj 𝒜, (pullback.fst ((trivCover 𝒜 L).f W)
        ((trivCover 𝒜 L).f W') ≫ (trivCover 𝒜 L).f W) x = z := ⟨_, rfl⟩
    have hzW : relativeProjToBase 𝒜 z ∈ W.1.toOpens := by
      have hmem : z ∈ (chart 𝒜 W.1).opensRange :=
        ⟨pullback.fst ((trivCover 𝒜 L).f W) ((trivCover 𝒜 L).f W') x, by
          rw [← hz, Scheme.Hom.comp_apply]⟩
      rwa [opensRange_chart] at hmem
    have hzW' : relativeProjToBase 𝒜 z ∈ W'.1.toOpens := by
      have hmem : z ∈ (chart 𝒜 W'.1).opensRange :=
        ⟨pullback.snd ((trivCover 𝒜 L).f W) ((trivCover 𝒜 L).f W') x, by
          rw [← hz, pullback.condition, Scheme.Hom.comp_apply]⟩
      rwa [opensRange_chart] at hmem
    obtain ⟨f, g, he, hmf⟩ :=
      exists_basicOpen_le_affine_inter W.1.2 W'.1.2 _ ⟨hzW, hzW'⟩
    obtain ⟨V, hVf, hmV, hV⟩ := exists_isTrivializing_le L (W.1.basicOpen f) _ hmf
    have heq : W.1.basicOpen f = W'.1.basicOpen g := Subtype.ext he
    have hVW : V ≤ W.1 := hVf.trans (W.1.basicOpen_le f)
    have hVW' : V ≤ W'.1 := (hVf.trans_eq heq).trans (W'.1.basicOpen_le g)
    obtain ⟨y, hy⟩ := mem_range_chart 𝒜 (U := V) hmV
    refine ⟨⟨V, hV⟩, homOfLE hVW, homOfLE hVW', y, ?_⟩
    apply (pullback.fst ((trivCover 𝒜 L).f W) ((trivCover 𝒜 L).f W') ≫
      (trivCover 𝒜 L).f W).isOpenEmbedding.injective
    rwa [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc,
      RelativeProjGeneral.transition_comp_chart_of_le_opens, hz]

/-- The transition maps of the cover are the transition morphisms of the chart functor. -/
public theorem trans_trivCover {W W' : Site L} (h : W ⟶ W') :
    (trivCover 𝒜 L).trans h = (chartFunctor 𝒜).map (Site.homVal h) := rfl

end Cover

end Stacks.AlgebraicGeometry.TrivializingSite

end
