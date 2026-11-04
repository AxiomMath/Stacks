module

public import StacksFrontier.AlgebraicGeometry.Gluing.Punctured
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Constructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Spec 𝒪_{S, s} ∩ U` as a limit, for `U` a retrocompact open

Let `S` be a scheme, `s` a point of it and `U ⊆ S` an open.  That
`Spec 𝒪_{S, s}` is the inverse limit of the affine open neighbourhoods `W` of `s`, and that the
preimage of `U` in it is the inverse limit of the opens `W ∩ U`, is
`AlgebraicGeometry.isLimitSpecStalkCone` and `AlgebraicGeometry.isLimitOpensSpecStalkCone`.
Those hold for every open `U` and every point `s`, with no finiteness hypothesis at all.

What the consumers of that limit need in addition is that the system `W ∩ U` consists of
*quasi-compact and quasi-separated* schemes, since that is what descent along an inverse limit
with affine transition maps asks of the system
([Stacks, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX),
[Stacks, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)).  Quasi-separatedness is free: each
`W ∩ U` is an open subscheme of an affine scheme.  Quasi-compactness is not, and the hypothesis
that buys it is that `U` is *retrocompact* in `S` — the hypothesis under which
[Stacks, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91) is stated, and, in the equivalent
form "`U → S` is quasi-compact", the hypothesis under which
[Stacks, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90) is stated.  This file supplies that
step and the two hypothesis families it yields.

## The two wordings of the hypothesis

Stacks calls `U ⊆ S` retrocompact when its intersection with every quasi-compact open is
quasi-compact ([Stacks, Tag 005A](https://stacks.math.columbia.edu/tag/005A), which is Mathlib's
`IsRetrocompact`), and in the proofs of both 0E90 and 0E91 uses it through the sentence "`U → S`
is quasi-compact".  For an *open* subset the two are the same condition, and
`AlgebraicGeometry.isRetrocompact_iff_quasiCompact_ι` says so, so a consumer may carry whichever
wording its source uses.

## Main results

* `AlgebraicGeometry.isRetrocompact_iff_quasiCompact_ι`: an open of a scheme is retrocompact
  exactly when its inclusion morphism is quasi-compact.
* `AlgebraicGeometry.isCompact_inter_of_isRetrocompact`: a retrocompact open meets a quasi-compact
  open in a quasi-compact set — the retrocompactness counterpart of
  `AlgebraicGeometry.isCompact_inter_of_quasiCompact_ι`, and the one step at which the hypothesis
  on `U` is used.
* `AlgebraicGeometry.compactSpace_opensSpecStalkDiagram_obj_of_isRetrocompact` and
  `AlgebraicGeometry.quasiSeparatedSpace_opensSpecStalkDiagram_obj`: the `CompactSpace` and
  `QuasiSeparatedSpace` families for the system `W ∩ U`, `W` running over the affine open
  neighbourhoods of `s` inside a fixed one.
* `AlgebraicGeometry.opensCone_specStalkCone_pt`: the apex of that limit cone is the preimage of
  `U` along `S.fromSpecStalk s`, i.e. it is `V = Spec 𝒪_{S, s} ∩ U`.

## Implementation notes

The two families are stated as results rather than instances for the same reason as their
counterparts in `StacksFrontier.AlgebraicGeometry.Gluing.Punctured`: the subject is
`AlgebraicGeometry.opensDiagram`, which is a `def`, so instance search does not see through it to
the intersection and the family has to be supplied as a `haveI`.  No hypothesis is placed on `s`:
neither half needs `s` to be a closed point, nor `s ∉ U`, so threading either would only narrow
the statements for the consumers.

## References

* [Stacks Project, Tag 005A](https://stacks.math.columbia.edu/tag/005A)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **An open of a scheme is retrocompact exactly when its inclusion morphism is quasi-compact.**

These are the two wordings in which the hypothesis on `U` appears in
[Stacks, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90) and
[Stacks, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91): the statements say "retrocompact
open", the proofs say "`U → S` is quasi-compact". -/
theorem isRetrocompact_iff_quasiCompact_ι (U : S.Opens) :
    IsRetrocompact (U : Set S) ↔ QuasiCompact U.ι := by
  rw [quasiCompact_iff_isSpectralMap]
  exact IsRetrocompact_iff_isSpectralMap_subtypeVal

/-- An open with quasi-compact inclusion morphism is retrocompact.

This is the direction the consumers need, since both 0E90 and 0E91 arrive carrying the
quasi-compactness of `U → S`.  The opposite direction is already available as
`Stacks.StrictTransform.quasiCompact_ι_of_isRetrocompact`, and is not restated here. -/
theorem isRetrocompact_of_quasiCompact_ι (U : S.Opens) [QuasiCompact U.ι] :
    IsRetrocompact (U : Set S) :=
  (isRetrocompact_iff_quasiCompact_ι U).mpr ‹_›

/-- **A retrocompact open meets a quasi-compact open in a quasi-compact set**, read as a subset of
the second open.

This is the retrocompactness counterpart of `AlgebraicGeometry.isCompact_inter_of_quasiCompact_ι`,
and it is the single step at which the hypothesis on `U` of
[Stacks, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91) is used. -/
@[ega "IV 1.8.1" "necessity"]
theorem isCompact_inter_of_isRetrocompact (U W : S.Opens) (hU : IsRetrocompact (U : Set S))
    (hW : IsCompact (W : Set S)) :
    IsCompact ((W.ι ⁻¹ᵁ U : Set (W : Scheme.{u}))) := by
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  show IsCompact (W.ι '' (W.ι ⁻¹' (U : Set S)))
  rw [Set.image_preimage_eq_inter_range, W.range_ι]
  exact hU hW W.2

variable (S) in
/-- **The `CompactSpace` family for the system `W ∩ U`.**  Every object of the system is the
intersection of the retrocompact open `U` with an affine, hence quasi-compact, open neighbourhood
of `s`, so it is quasi-compact.

This is the hypothesis that descent along an inverse limit with affine transition maps asks of the
system, and the only place the retrocompactness of `U` is used. -/
theorem compactSpace_opensSpecStalkDiagram_obj_of_isRetrocompact {s : S} (U : S.Opens)
    (hU : IsRetrocompact (U : Set S)) (W₀ : AffineOpenNhds S s) (j : Over W₀) :
    CompactSpace ((opensDiagram (affineOpenNhdsDiagram S s) W₀
      (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)).obj j) :=
  compactSpace_opensDiagram_obj_of_isCompact _ _ _
    (isCompact_inter_of_isRetrocompact U W₀.obj.1 hU W₀.property.isCompact) j

variable (S) in
/-- **The `QuasiSeparatedSpace` family for the system `W ∩ U`.**  Every object of the system is an
open subscheme of an affine scheme, so no hypothesis on `U` is needed here. -/
theorem quasiSeparatedSpace_opensSpecStalkDiagram_obj {s : S} (U : S.Opens)
    (W₀ : AffineOpenNhds S s) (j : Over W₀) :
    QuasiSeparatedSpace ((opensDiagram (affineOpenNhdsDiagram S s) W₀
      (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)).obj j) :=
  quasiSeparatedSpace_opensDiagram_obj _ _ _ j

variable (S) in
/-- **The apex of the limit cone for the system `W ∩ U` is `V = Spec 𝒪_{S, s} ∩ U`**, namely the
preimage of `U` along the canonical morphism `Spec 𝒪_{S, s} ⟶ S`.

`AlgebraicGeometry.isLimitOpensSpecStalkCone` exhibits that cone as a limit; this says what its
apex is, so that a consumer stating its conclusion about `V` need not unfold the cone. -/
theorem opensCone_specStalkCone_pt {s : S} (W₀ : AffineOpenNhds S s) (U : S.Opens) :
    (opensCone (affineOpenNhdsDiagram S s) (specStalkCone S s) W₀
        (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ U)).pt =
      (S.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
  congrArg Scheme.Opens.toScheme (specStalkCone_π_preimage S s W₀ U)

end AlgebraicGeometry

end
