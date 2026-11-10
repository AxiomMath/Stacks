module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.MapDomain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 07ZG, assertion (1): the open subscheme of the relative Proj of the target

Tag 07ZG attaches to a homomorphism `ψ` of quasi-coherent graded `𝒪_S`-algebras an open
subscheme `U(ψ)` of the relative projective spectrum of the target, characterized by its
restriction to every affine chart of the base: on the chart over an affine open `V` it is the
domain of definition `U(ψ_V)` of the induced homomorphism of the graded rings of sections over
`V`.

This file constructs that open and proves the characterization.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.relativeMapDomain`: **Tag
  07ZG, assertion (1).** The open subscheme `U(ψ)`, as the supremum over the affine opens of the
  base of the chart images of the chart domains.

## Main results

* `RelativeProjMapDomain.SheafGradedAlgebraHom.chart_preimage_relativeMapDomain`: the
  inverse image of `U(ψ)` under the chart over an affine open `V` of the base is exactly
  `U(ψ_V)`. This is the affine-local characterization Tag 07ZG gives, and it is what makes the
  supremum a glueing rather than merely a union.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.relativeMapDomain_unique`:
  an open with that property is `U(ψ)`, because the chart images cover.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.opensRange_projInclusionMap`: the range of the
  transition morphism of Tag 01NO, as the inverse image of the smaller affine open.

## The refinement, which is the whole content

The supremum is over *all* affine opens of the base, and two of them need not be nested, so the
inclusion `chart V ⁻¹ᵁ U(ψ) ≤ U(ψ_V)` is not a formal consequence of the definition. It is proved
at a point, by refining: a point of the chart over `V` that lies in the chart image over `U` lies
over a point of `U ⊓ V`, and the affine opens are a basis, so there is an affine `W ⊆ U ⊓ V`
containing it. Over `W` both chart images factor through the single chart of `W`, whose
transitions to `U` and to `V` pull the chart domains of `U` and of `V` back to the chart domain
of `W` — that is
`RelativeProjMapDomain.SheafGradedAlgebraHom.projInclusionMap_preimage_chartDomain`,
and it is the only input beyond the geometry of the charts.

For a *nested* pair the argument needs no refinement; see
`RelativeProjMapDomain.SheafGradedAlgebraHom.chart_image_chartDomain_mono`.

## Implementation notes

`Scheme.Hom.opensRange` and the image functor `''ᵁ` both take the `IsOpenImmersion` instance as
an argument, so a rewrite that replaces the morphism underneath either of them fails its motive
check — including the rewrite of `RelativeProjData.chart_transition`, whose statement is an
equality of morphisms. Every such step below is therefore done at a point instead, which is also
shorter: the image of a point under the chart of `W` is read through the transition rather than
the chart image being rewritten.

For the same reason the `IsOpenImmersion` instance of the chart is restated for the spelling
`P.chart U.1 U.2`: the instance of
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` is keyed on the two
arguments separately and does not fire when the first is a coercion, which is exactly the
spelling a supremum over the affine opens produces.

The supremum is indexed by `Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen` rather than
by `AlgebraicGeometry.Scheme.affineOpens`, for the reason recorded at that definition: the latter
is a `Set`, so its subtype's second projection does not have type `IsAffineOpen U` on the nose,
and every rewrite under a chart built from it fails.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Scope

Assertion (1) of Tag 07ZG is here, and three declarations of this file carry the tag for it: the
open itself, its affine-local description, and the fact that the description determines it.
Assertion (2), the morphism `r_ψ : U(ψ) ⟶ Proj_S(A)` over `S`, is in
`StacksFrontier/AlgebraicGeometry/Morphism/Glue.lean`.

Assertion (3) of the tag — the maps on twists
`θ_n : r_ψ^*𝒪_X(n) ⟶ 𝒪_{U(ψ)}(n)` — is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap` in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistExists.lean`, with its affine-local
characterisation, assertion (4c), as `relativeTwistMap_chart` there and its uniqueness as
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_unique`. The sheaves it maps between are
the homogeneous pieces of
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, pulled back along `r_ψ`
and along the inclusion of `U(ψ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

section Transitions

variable {S : Scheme.{u}} (B : SheafGradedAlgebra S)

/-- The affine opens of a scheme, as a subtype of `Opens` whose second projection has type
`IsAffineOpen U` on the nose.

`AlgebraicGeometry.Scheme.affineOpens` is a `Set`, so the second projection of its subtype has
type `U ∈ S.affineOpens`, which is only *definitionally* `IsAffineOpen U`. That is enough for
`exact` and not enough for `rw`: the chart's `IsOpenImmersion` argument is computed from that
proof, and a motive mentioning the chart is then not type-correct at implicit transparency, so
every rewrite under it fails, with the error naming `U.property`. -/
public abbrev AffineOpen (S : Scheme.{u}) : Type u := {U : S.Opens // IsAffineOpen U}

/-- The chart of a relative Proj over an affine open of the base is an open immersion, at the
spelling a supremum over `Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen` produces. -/
public instance isOpenImmersion_chart_affineOpen (P : RelativeProjData B) (U : AffineOpen S) :
    IsOpenImmersion (P.chart U.1 U.2) :=
  isOpenImmersion_chart P U.1 U.2

/-- The chart images over the affine opens of the base cover the relative Proj, stated over
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen`. -/
public theorem iSup_toBase_preimage_eq_top' (P : RelativeProjData B) :
    (⨆ U : AffineOpen S, P.toBase ⁻¹ᵁ U.1) = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ V : S.affineOpens, P.toBase ⁻¹ᵁ (V.1 : S.Opens) by
      rw [iSup_toBase_preimage_eq_top]; trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V.1, V.2⟩, hxV⟩

/-- The transition morphism of Tag 01NO is an open immersion: it is the base change of the
inclusion of the affine opens along the structure morphism of the chart. -/
@[ega "II 3.1.1" "Open-immersion clause"]
public instance isOpenImmersion_projInclusionMap (U V : S.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsOpenImmersion (projInclusionMap B U V h hU hV) :=
  MorphismProperty.of_isPullback (projInclusion_isPullback B U V h hU hV).flip inferInstance

/-- The range of the inclusion of one open subscheme of a scheme into a larger one, as an open of
the larger. -/
public theorem opensRange_homOfLE {U V : S.Opens} (h : U ≤ V) :
    (S.homOfLE h).opensRange = V.ι ⁻¹ᵁ U := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx
    have hx1 : (x.1 : S) = y.1 := by rw [← hy]; exact Scheme.homOfLE_apply h y
    change (x.1 : S) ∈ U
    rw [hx1]
    exact y.2
  · refine ⟨⟨x.1, hx⟩, Subtype.ext ?_⟩
    exact Scheme.homOfLE_apply h ⟨x.1, hx⟩

/-- **The range of the transition morphism of Tag 01NO.** A point of the chart over `V` lies in
the image of the chart over a smaller affine open `U` exactly when its image in `V` lies in `U`.
This is the cartesian square of Tag 01NO, read on opens. -/
public theorem opensRange_projInclusionMap (U V : S.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (projInclusionMap B U V h hU hV).opensRange =
      projInclusionToOpen B V hV ⁻¹ᵁ (V.ι ⁻¹ᵁ U) := by
  have key := AlgebraicGeometry.IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (projInclusion_isPullback B U V h hU hV).flip (⊤ : U.toScheme.Opens)
  rw [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange, opensRange_homOfLE] at key
  exact key

/-- The structure morphism of the chart over an affine open `V`, followed by the inclusion of
`V`, is the chart followed by the structure morphism of the relative Proj. -/
public theorem chart_comp_toBase (V : S.Opens) (hV : IsAffineOpen V) :
    (relativeProj B).chart V hV ≫ (relativeProj B).toBase =
      projInclusionToOpen B V hV ≫ V.ι :=
  ((relativeProj B).chart_isPullback V hV).w

/-- The base point of a point of the chart over `V`, read inside `V`. -/
public theorem toBase_chart_apply (V : S.Opens) (hV : IsAffineOpen V)
    (z : AlgebraicGeometry.Proj (B.grading V)) :
    (relativeProj B).toBase ((relativeProj B).chart V hV z) =
      V.ι (projInclusionToOpen B V hV z) := by
  rw [← Scheme.Hom.comp_apply, chart_comp_toBase, Scheme.Hom.comp_apply]

/-- The base point of a point of the chart over `V` lies in `V`. -/
private theorem toBase_chart_mem (V : S.Opens) (hV : IsAffineOpen V)
    (z : AlgebraicGeometry.Proj (B.grading V)) :
    (relativeProj B).toBase ((relativeProj B).chart V hV z) ∈ V := by
  rw [toBase_chart_apply]
  exact (projInclusionToOpen B V hV z).2

/-- The charts of a nested pair of affine opens, read at a point. This is
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_transition` applied to a
point, which is how every step below uses it: the equality of morphisms itself cannot be
rewritten underneath the image functor, whose `IsOpenImmersion` argument depends on it. -/
public theorem chart_transition_apply (W V : S.Opens) (hWV : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (y : AlgebraicGeometry.Proj (B.grading W)) :
    (relativeProj B).chart V hV (projInclusionMap B W V hWV hW hV y) =
      (relativeProj B).chart W hW y := by
  rw [← Scheme.Hom.comp_apply, (relativeProj B).chart_transition W V hWV hW hV]

/-- A point of the chart over `V` whose base point lies in a smaller affine open `W` comes from
the chart over `W`. -/
private theorem exists_projInclusionMap_eq (W V : S.Opens) (hWV : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) (z : AlgebraicGeometry.Proj (B.grading V))
    (hz : (relativeProj B).toBase ((relativeProj B).chart V hV z) ∈ W) :
    ∃ z', projInclusionMap B W V hWV hW hV z' = z := by
  have hmem : z ∈ (projInclusionMap B W V hWV hW hV).opensRange := by
    rw [opensRange_projInclusionMap]
    change V.ι (projInclusionToOpen B V hV z) ∈ W
    rw [← toBase_chart_apply]
    exact hz
  exact hmem

end Transitions

section Glue

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S}

namespace SheafGradedAlgebraHom

variable (ψ : SheafGradedAlgebraHom A B)

/-- **Tag 07ZG, assertion (1).** The open subscheme of the relative projective spectrum of the
target on which `ψ` induces a morphism to the relative projective spectrum of the source: the
union, over the affine opens of the base, of the chart images of the chart domains. -/
@[ega "II 3.5.1" "the open G(φ)", ega "II 3.5.6" "partial"]
public def relativeMapDomain : (relativeProj B).scheme.Opens :=
  ⨆ U : AffineOpen S, (relativeProj B).chart U.1 U.2 ''ᵁ ψ.chartDomain U.1

/-- For a *nested* pair of affine opens the chart image of the chart domain only grows: the
transition carries the chart domain of the smaller open into the chart domain of the larger one,
because the latter pulls back to the former. -/
public theorem chart_image_chartDomain_mono (W V : S.Opens) (hWV : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) :
    (relativeProj B).chart W hW ''ᵁ ψ.chartDomain W ≤
      (relativeProj B).chart V hV ''ᵁ ψ.chartDomain V := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨projInclusionMap B W V hWV hW hV y, ?_, ?_⟩
  · rw [← ψ.projInclusionMap_preimage_chartDomain W V hWV hW hV] at hy
    exact hy
  · exact (chart_transition_apply B W V hWV hW hV y).trans hyx

/-- **Tag 07ZG's affine-local characterization of the open subscheme.** The inverse image of
`U(ψ)` under the chart over an affine open `V` of the base is the domain of definition of the
homomorphism `ψ` induces on the graded rings of sections over `V`. -/
@[ega "II 3.5.1" "G(φ)∩p⁻¹(U)=G(φ_U)"]
public theorem chart_preimage_relativeMapDomain (V : S.Opens) (hV : IsAffineOpen V) :
    (relativeProj B).chart V hV ⁻¹ᵁ ψ.relativeMapDomain = ψ.chartDomain V := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨U, hzU⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    obtain ⟨w, hw, hwz⟩ := hzU
    -- the base point of `z`, which lies in both `U` and `V`
    have hbV := toBase_chart_mem B V hV z
    have hbU : (relativeProj B).toBase ((relativeProj B).chart V hV z) ∈ U.1 := by
      rw [← hwz]
      exact toBase_chart_mem B U.1 U.2 w
    obtain ⟨-, ⟨W, hWmem, rfl⟩, hbW, hWUV⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show (relativeProj B).toBase ((relativeProj B).chart V hV z) ∈
          ((U.1 ⊓ V : S.Opens) : Set S) from ⟨hbU, hbV⟩) (U.1 ⊓ V).2
    have hW : IsAffineOpen W := hWmem
    have hWU : W ≤ U.1 := fun x hx => (hWUV hx).1
    have hWV : W ≤ V := fun x hx => (hWUV hx).2
    -- both `z` and `w` come from the chart over `W`
    obtain ⟨z', hz'⟩ := exists_projInclusionMap_eq B W V hWV hW hV z hbW
    obtain ⟨w', hw'⟩ := exists_projInclusionMap_eq B W U.1 hWU hW U.2 w
      ((congrArg (fun p => (relativeProj B).toBase p) hwz).symm ▸ hbW)
    have e3 : (relativeProj B).chart U.1 U.2 (projInclusionMap B W U.1 hWU hW U.2 w') =
        (relativeProj B).chart V hV (projInclusionMap B W V hWV hW hV z') := by
      rw [hw', hz']
      exact hwz
    have hchart : (relativeProj B).chart W hW w' = (relativeProj B).chart W hW z' :=
      ((chart_transition_apply B W U.1 hWU hW U.2 w').symm.trans e3).trans
        (chart_transition_apply B W V hWV hW hV z')
    have hzw : z' = w' :=
      (((relativeProj B).chart W hW).isOpenEmbedding.injective hchart).symm
    have hz'W : z' ∈ ψ.chartDomain W := by
      rw [← ψ.projInclusionMap_preimage_chartDomain W U.1 hWU hW U.2]
      change projInclusionMap B W U.1 hWU hW U.2 z' ∈ ψ.chartDomain U.1
      rw [hzw, hw']
      exact hw
    rw [← ψ.projInclusionMap_preimage_chartDomain W V hWV hW hV] at hz'W
    have hfin : projInclusionMap B W V hWV hW hV z' ∈ ψ.chartDomain V := hz'W
    rwa [hz'] at hfin
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(⟨V, hV⟩ : AffineOpen S), ⟨z, hz, rfl⟩⟩

/-- **The open subscheme of Tag 07ZG is the only one with its affine-local description.** The
chart images cover the relative projective spectrum, so an open of it is determined by its
inverse images under the charts. -/
@[ega "II 3.5.1" "uniqueness of G(φ)"]
public theorem relativeMapDomain_unique (W : (relativeProj B).scheme.Opens)
    (hW : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      (relativeProj B).chart V hV ⁻¹ᵁ W = ψ.chartDomain V) :
    W = ψ.relativeMapDomain := by
  have key : ∀ V : AffineOpen S,
      (relativeProj B).chart V.1 V.2 ⁻¹ᵁ W =
        (relativeProj B).chart V.1 V.2 ⁻¹ᵁ ψ.relativeMapDomain :=
    fun V => (hW V.1 V.2).trans (ψ.chart_preimage_relativeMapDomain V.1 V.2).symm
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ V : AffineOpen S, (relativeProj B).toBase ⁻¹ᵁ V.1 by
      rw [iSup_toBase_preimage_eq_top' B (relativeProj B)]; trivial)
  rw [← chart_image_top (relativeProj B) V.1 V.2] at hxV
  obtain ⟨y, -, hyx⟩ := hxV
  subst hyx
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have h1 : y ∈ (relativeProj B).chart V.1 V.2 ⁻¹ᵁ W := hx
    rw [key V] at h1
    exact h1
  · have h1 : y ∈ (relativeProj B).chart V.1 V.2 ⁻¹ᵁ ψ.relativeMapDomain := hx
    rw [← key V] at h1
    exact h1

end SheafGradedAlgebraHom

end Glue

end Stacks.AlgebraicGeometry.RelativeProjMapDomain

end
