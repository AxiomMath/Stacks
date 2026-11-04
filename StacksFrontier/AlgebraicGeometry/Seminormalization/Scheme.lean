module

public import StacksFrontier.AlgebraicGeometry.Properties.LocalRingProperty
public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Seminormalization.LocalProperty

/-!
# Seminormal schemes

A scheme `X` *locally satisfies* a property `P` of commutative rings when every point of `X`
has an affine open neighbourhood whose ring of sections satisfies `P`
([Stacks, Tag 01OQ](https://stacks.math.columbia.edu/tag/01OQ)).  A scheme is *seminormal*
when it locally satisfies seminormality of rings
([Stacks, Tag 0EUN](https://stacks.math.columbia.edu/tag/0EUN)).

The main result is the seminormal half of
[Stacks, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP): for a seminormal scheme the
ring of sections over *every* affine open is seminormal, not only over the affine opens
produced by the definition.  This is the affine-local transfer needed before any statement
about seminormality can be checked on a chosen affine chart.

The proof is the affine communication lemma `AlgebraicGeometry.of_affine_open_cover`, whose two
hypotheses are exactly the two halves of
[Stacks, Tag 0EUM](https://stacks.math.columbia.edu/tag/0EUM) proved in
`StacksFrontier.AlgebraicGeometry.Seminormalization.LocalProperty`: seminormality passes to a
basic open because the sections there are a localization away from a single section, and
descends from a finite family of basic opens whose sections span the unit ideal.

## Main definitions

* `Stacks.AlgebraicGeometry.Seminormal.IsLocallyRingProperty`: `X` locally satisfies a property
  of commutative rings.
* `Stacks.AlgebraicGeometry.Seminormal.IsSeminormal`: `X` is seminormal.
* `Stacks.AlgebraicGeometry.Seminormal.IsAbsolutelyWeaklyNormal`: `X` is absolutely weakly
  normal.

## Main results

* `Stacks.AlgebraicGeometry.Seminormal.IsSeminormal.isSeminormalRing_sections`: on a seminormal
  scheme the sections over every affine open form a seminormal ring.
* `Stacks.AlgebraicGeometry.Seminormal.isSeminormal_iff_forall_affineOpens`: `X` is seminormal
  if and only if the sections over every affine open form a seminormal ring.
* `Stacks.AlgebraicGeometry.Seminormal.IsSeminormal.isReduced`: a seminormal scheme is reduced
  in the sense that its sections over every affine open are reduced.
* `Stacks.AlgebraicGeometry.Seminormal.IsSeminormal.restrict`: every open subscheme of a
  seminormal scheme is seminormal.

## Implementation notes

`AlgebraicGeometry.IsLocally` takes the ring property as a predicate on types carrying a
`CommRing` instance, and ranges over `X.affineOpens`, so affineness of the neighbourhood is
part of the data rather than a side condition.  It is an `abbrev` so that the pointwise
existential form is available without unfolding.  The scheme and the rings live in the same
universe `u`, as they must: `Γ(X, U)` for `X : Scheme.{u}` is a `Type u`.

Only the seminormal half of Tag 0EUP is proved.  The absolutely weakly normal half needs the
corresponding half of Tag 0EUM, which is not available (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Seminormalization.LocalProperty`); `IsAbsolutelyWeaklyNormal`
is defined here only so that the two predicates of Tag 0EUN are stated together.

## References

* [Stacks Project, Tag 01OQ](https://stacks.math.columbia.edu/tag/01OQ)
* [Stacks Project, Tag 0EUN](https://stacks.math.columbia.edu/tag/0EUN)
* [Stacks Project, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Seminormal

open Stacks.RingTheory.Seminormal

/-- A scheme is *seminormal* if every point has an affine open neighbourhood whose ring of
sections is seminormal. -/
abbrev IsSeminormal (X : Scheme.{u}) : Prop :=
  AlgebraicGeometry.IsLocally (fun (R : Type u) [CommRing R] => IsSeminormalRing R) X

/-- A scheme is *absolutely weakly normal* if every point has an affine open neighbourhood
whose ring of sections is absolutely weakly normal. -/
abbrev IsAbsolutelyWeaklyNormal (X : Scheme.{u}) : Prop :=
  AlgebraicGeometry.IsLocally (fun (R : Type u) [CommRing R] => IsAbsolutelyWeaklyNormalRing R) X

variable {X : Scheme.{u}}

/-- Seminormality of the sections over an affine open passes to a basic open of it: the
sections there are a localization away from a single section. -/
theorem isSeminormalRing_sections_affineBasicOpen (U : X.affineOpens) (f : Γ(X, U.1))
    (hU : IsSeminormalRing Γ(X, U.1)) : IsSeminormalRing Γ(X, X.basicOpen f) := by
  have := U.2.isLocalization_basicOpen f
  exact hU.localizationAway f

/-- Seminormality of the sections over an affine open descends from a family of basic opens
whose defining sections span the unit ideal. -/
theorem isSeminormalRing_sections_of_span_eq_top (U : X.affineOpens) {s : Set Γ(X, U.1)}
    (hs : Ideal.span s = ⊤)
    (h : ∀ f : s, IsSeminormalRing Γ(X, X.basicOpen (f : Γ(X, U.1)))) :
    IsSeminormalRing Γ(X, U.1) := by
  refine isSeminormalRing_of_span_eq_top hs fun f => ?_
  have := U.2.isLocalization_basicOpen (f : Γ(X, U.1))
  exact IsSeminormalRing.ofIsLocalization (Submonoid.powers (f : Γ(X, U.1))) (h f)

/-- On a seminormal scheme the ring of sections over *every* affine open is seminormal.  This
is the seminormal half of [Stacks, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP). -/
theorem IsSeminormal.isSeminormalRing_sections (hX : IsSeminormal X) (V : X.affineOpens) :
    IsSeminormalRing Γ(X, V.1) := by
  choose U hUmem hUsn using hX
  have hsup : (⨆ x : X, (U x : X.Opens)) = ⊤ :=
    top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hUmem x⟩
  induction V using of_affine_open_cover U hsup with
  | basicOpen W f hW => exact isSeminormalRing_sections_affineBasicOpen W f hW
  | openCover W s hs h =>
    exact isSeminormalRing_sections_of_span_eq_top W (s := (s : Set Γ(X, W.1))) hs
      fun f => h ⟨f.1, by simp⟩
  | hU x => exact hUsn x

/-- A scheme is seminormal exactly when the ring of sections over every affine open is
seminormal. -/
theorem isSeminormal_iff_forall_affineOpens :
    IsSeminormal X ↔ ∀ V : X.affineOpens, IsSeminormalRing Γ(X, V.1) := by
  refine ⟨fun hX => hX.isSeminormalRing_sections, fun h x => ?_⟩
  obtain ⟨W, hW, hxW, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  exact ⟨⟨W, hW⟩, hxW, h ⟨W, hW⟩⟩

/-- A seminormal scheme is reduced: its sections over every affine open form a reduced ring.
This is the scheme half of [Stacks, Tag 0EUQ](https://stacks.math.columbia.edu/tag/0EUQ). -/
theorem IsSeminormal.isReduced (hX : IsSeminormal X) (V : X.affineOpens) :
    IsReduced Γ(X, V.1) :=
  (hX.isSeminormalRing_sections V).isReduced

/-- Every open subscheme of a seminormal scheme is seminormal.  This is the last assertion of
[Stacks, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP) for seminormality. -/
theorem IsSeminormal.restrict (hX : IsSeminormal X) (U : X.Opens) :
    IsSeminormal U.toScheme := by
  rw [isSeminormal_iff_forall_affineOpens]
  intro V
  exact (hX.isSeminormalRing_sections
      ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩).of_ringEquiv
    (U.ι.appIso V.1).commRingCatIsoToRingEquiv

end Stacks.AlgebraicGeometry.Seminormal

end
