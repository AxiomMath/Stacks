module

public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Transfer
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.QuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A curve is affine or H-projective, from a compactification and the inner claim

[Stacks, Tag 0A27] says that a curve over a field is either an affine scheme or H-projective
over that field. Its proof chooses a compactification `j : X ⟶ X̄` with `X̄` an H-projective
curve whose complement consists of finitely many closed points ([Stacks, Tag 0BXW]); if the
complement is empty then `X ≅ X̄` is H-projective, and otherwise it is enough, by
[Stacks, Tag 09N9], that `X̄ ∖ {x₁}` is affine for one point `x₁` of the complement — which is
the *inner claim* of the tag, proved there by a cohomological argument.

This file assembles the tag from those two inputs, neither of which is available in this
repository: the compactification and the inner claim are hypotheses of
`AlgebraicGeometry.isAffine_or_exists_isClosedImmersion_of_compactification`, and no
`@[stacks]` attribute is attached to anything here. What *is* proved unconditionally is the step
the source performs with [Stacks, Tag 09N9]: a quasi-compact open of a locally Noetherian scheme
of dimension at most one which is contained in an affine open is itself affine, hence a
quasi-compact open subscheme of such a scheme with that property is an affine scheme.

## Main results

* `AlgebraicGeometry.krullDimLE_one_stalk_of_topologicalKrullDim_le_one`: the local rings of a
  scheme of dimension at most one have Krull dimension at most one.
* `AlgebraicGeometry.isAffineOpen_of_le_isAffineOpen_of_isCompact`: a quasi-compact open
  contained in an affine open of a locally Noetherian scheme of dimension at most one is affine.
* `AlgebraicGeometry.isAffine_of_isOpenImmersion_le_isAffineOpen`: the same, for the source of an
  open immersion whose image lies in an affine open.
* `AlgebraicGeometry.isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton`: the form in
  which [Stacks, Tag 0A27] uses it — the complement of a point of `X̄` being affine makes `X`
  affine, for any open immersion missing that point.
* `AlgebraicGeometry.isAffine_or_exists_isClosedImmersion_of_compactification`: the conclusion of
  [Stacks, Tag 0A27] for a curve equipped with a compactification, granted the inner claim at the
  points of the complement.

## Implementation notes

**H-projectivity is spelled out as the existential**, exactly as in
`StacksDraft.AlgebraicGeometry.F3b.HProjectiveProper.Basic` and
`StacksDraft.AlgebraicGeometry.F3b.HProjectiveProper.Transfer`: there is no named predicate for
"admits a closed immersion into relative projective space over the base" in this repository, so
both the hypothesis on `X̄` and the conclusion on `X` are written
`∃ n i, IsClosedImmersion i ∧ i ≫ (ℙⁿ_S ↘ S) = f`. The `r = 0` branch is then literally
`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_of_iso`, with no bridging lemma.

**The inner claim is taken in the form "the complement of a point of the complement is an affine
open".** Writing it as `∃ U : X̄.Opens, (U : Set X̄) = {x}ᶜ ∧ IsAffineOpen U` folds in the
closedness of `{x}` — part (3) of [Stacks, Tag 0BXW] — rather than carrying it as a separate
hypothesis, and is what
`Stacks.ProjectiveSpaceSections.isAffineOpen_compl_singleton_of_isClosedImmersion` produces once
its generating pair is available.

**Only quasi-compactness of `X` is used, not the full curve hypothesis on it.** The binder
`[IsCurve k f]` is kept because it is the hypothesis of [Stacks, Tag 0A27]; the curve hypothesis
on `X̄` is used in earnest, for local Noetherianness and for the dimension bound. That `X̄` is
again a curve is not part of the conclusion of [Stacks, Tag 0BXW] but is established in its
proof, so it appears here as a hypothesis.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 09N9](https://stacks.math.columbia.edu/tag/09N9)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The local rings of a scheme of dimension at most one have Krull dimension at most one.**
The dimension of a scheme is the supremum of the Krull dimensions of its local rings
([Stacks, Tag 04MU], `AlgebraicGeometry.topologicalKrullDim_eq_iSup_krullDimOfRing_stalk`), so
each of them is bounded by it. -/
public theorem krullDimLE_one_stalk_of_topologicalKrullDim_le_one (X : Scheme.{u})
    (hX : topologicalKrullDim X ≤ 1) (x : X) : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
  Ring.krullDimLE_iff.mpr <| le_trans
    (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x)
    (by rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]; exact hX)

/-- **A quasi-compact open contained in an affine open of a locally Noetherian scheme of
dimension at most one is affine.** Inside the affine open `W` the open `U` is the quasi-compact
open `W.ι ⁻¹ᵁ U`, so [Stacks, Tag 09N9]
(`AlgebraicGeometry.isAffineOpen_of_isCompact_of_krullDimLE_one`) applies there; its two
hypotheses on the local rings of `W` come from local Noetherianness of `X` and from
`krullDimLE_one_stalk_of_topologicalKrullDim_le_one` for the open subscheme, whose dimension is
bounded by that of `X`. Affineness then transports back along the open immersion `W.ι`. -/
@[ega "IV 21.12.9" "more general"]
public theorem isAffineOpen_of_le_isAffineOpen_of_isCompact {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1) {W U : X.Opens}
    (hW : IsAffineOpen W) (hUW : U ≤ W) (hU : IsCompact (U : Set X)) : IsAffineOpen U := by
  have : IsAffine W.toScheme := hW
  have himage : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUW]
  have hcpt : IsCompact ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme) := by
    refine (W.isOpenEmbedding.isEmbedding.isCompact_iff (f := (W.ι.base : W.toScheme → X))).mpr ?_
    have : (W.ι.base : W.toScheme → X) '' ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme)
        = (U : Set X) := congrArg (fun V : X.Opens => (V : Set X)) himage
    rw [this]
    exact hU
  have hpre : IsAffineOpen (W.ι ⁻¹ᵁ U) :=
    isAffineOpen_of_isCompact_of_krullDimLE_one (fun _ => inferInstance)
      (fun y => krullDimLE_one_stalk_of_topologicalKrullDim_le_one W.toScheme
        ((topologicalKrullDim_subspace_le X (W : Set X)).trans hdim) y) _ hcpt
  exact himage ▸ hpre.image_of_isOpenImmersion W.ι

/-- **The source of an open immersion whose image lies in an affine open of a locally Noetherian
scheme of dimension at most one is affine**, provided it is quasi-compact. This is
`isAffineOpen_of_le_isAffineOpen_of_isCompact` at the open `j.opensRange`, which is compact as
the image of a compact space, together with the identification of `X` with that open. -/
public theorem isAffine_of_isOpenImmersion_le_isAffineOpen {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (hdim : topologicalKrullDim Y ≤ 1) (j : X ⟶ Y) [IsOpenImmersion j]
    [CompactSpace X] {W : Y.Opens} (hW : IsAffineOpen W) (hle : j.opensRange ≤ W) :
    IsAffine X := by
  have hrange : IsCompact ((j.opensRange : Y.Opens) : Set Y) := by
    simpa using isCompact_range (f := (j.base : X → Y)) (by fun_prop)
  have haff : IsAffineOpen j.opensRange :=
    isAffineOpen_of_le_isAffineOpen_of_isCompact hdim hW hle hrange
  have : IsAffine (j.opensRange).toScheme := haff
  exact IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq j (j.opensRange).ι (by simp)).hom

/-- **The step [Stacks, Tag 0A27] takes with [Stacks, Tag 09N9].** Let `Y` be a curve over `k`,
let `j : X ⟶ Y` be an open immersion with `X` quasi-compact, and let `x` be a point of `Y`
outside the image of `j`. If `Y ∖ {x}` is an affine open, then `X` is an affine scheme.

In the source `Y = X̄` is the compactification, `x = x₁` is one of the finitely many points of
the complement, and the affineness of `Y ∖ {x}` is the inner claim of the tag. -/
public theorem isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton (k : Type u) [Field k]
    {X Y : Scheme.{u}} {g : Y ⟶ Spec (.of k)} [IsCurve k g] (j : X ⟶ Y) [IsOpenImmersion j]
    [CompactSpace X] {x : Y} (hx : x ∉ Set.range j.base) {U : Y.Opens}
    (hU : (U : Set Y) = ({x} : Set Y)ᶜ) (hUaff : IsAffineOpen U) : IsAffine X := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  refine isAffine_of_isOpenImmersion_le_isAffineOpen
    (IsCurve.topologicalKrullDim_eq_one g).le j hUaff ?_
  intro y hy
  have hy' : y ∈ Set.range (⇑j : X → Y) := hy
  have hmem : y ∈ (U : Set Y) := by
    rw [hU]
    exact fun hxy => hx (hxy ▸ hy')
  exact hmem

/-- **[Stacks, Tag 0A27] for a curve equipped with a compactification, granted the inner claim.**
Let `X` be a curve over `k`, let `j : X ⟶ Y` be an open immersion into a curve `Y` over `k` which
is H-projective over `k`, and assume that for every point `x` of `Y` outside the image of `j` the
complement `Y ∖ {x}` is an affine open. Then `X` is affine or H-projective over `k`.

This is the structure of the source's proof. If the complement of the image is empty then `j` is
an isomorphism, and H-projectivity transports to `X` by
`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_of_iso`. Otherwise a point `x` of
the complement is chosen and `X` is affine by
`isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton`.

The two hypotheses that are not available in this repository are exactly the two inputs of the
source: the existence of the compactification `j` with its properties is [Stacks, Tag 0BXW], and
the affineness of `Y ∖ {x}` is the inner claim of [Stacks, Tag 0A27]. No attribute is attached:
with those as hypotheses this is not the tag. -/
public theorem isAffine_or_exists_isClosedImmersion_of_compactification (k : Type u) [Field k]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)} [IsCurve k f] [IsCurve k g]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ g = f)
    (hY : ∃ (n : ℕ) (i : Y ⟶ projectiveSpaceOver n (Spec (.of k))),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = g)
    (hinner : ∀ y : Y, y ∉ Set.range j.base →
      ∃ U : Y.Opens, (U : Set Y) = ({y} : Set Y)ᶜ ∧ IsAffineOpen U) :
    IsAffine X ∨ ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n (Spec (.of k))),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  by_cases hsurj : ∀ y : Y, y ∈ Set.range j.base
  · right
    have hepi : Epi j.base := by
      rw [TopCat.epi_iff_surjective]
      exact fun y => hsurj y
    have : IsIso j := (isIso_iff_isOpenImmersion_and_epi_base j).mpr ⟨inferInstance, hepi⟩
    exact exists_isClosedImmersion_projectiveSpaceOver_of_iso (asIso j) hj hY
  · left
    obtain ⟨y, hy⟩ := not_forall.mp hsurj
    obtain ⟨U, hU, hUaff⟩ := hinner y hy
    exact isAffine_of_isOpenImmersion_of_isAffineOpen_compl_singleton k (g := g) j hy hU hUaff

end AlgebraicGeometry

end
