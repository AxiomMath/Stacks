module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Factorization

/-!
# An open over which an immersion is closed lies in the coborder neighbourhood

[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) computes the conormal sheaf of an
immersion `i : Z ⟶ X` over an affine open `V ≤ X`, and the hypothesis it supplies there is a
*presentation of the fibre*: an isomorphism `pullback i V.ι ≅ Spec (Γ(X, V) ⧸ I)` compatible with
`AlgebraicGeometry.IsAffineOpen.isoSpec`. That hypothesis says nothing on its face about
`i.coborderRange`, the open through which `i` factors as a closed immersion and out of which the
conormal sheaf is built; so the affine computation appears to be about an open unrelated to the
construction.

It is not. This file proves that the presentation hypothesis *forces* `V ≤ i.coborderRange`. So
the canonical closed factorization `i.liftCoborder : Z ⟶ i.coborderRange` is already defined over
the whole of `V`, and the affine computation can be carried out inside it.

## Main results

* `Stacks.Conormal.AffineCotangent.closure_inter_subset_range`: for a morphism whose restriction
  over an open `V` is a closed immersion, the closure of the range meets `V` only inside the
  range.
* `Stacks.Conormal.AffineCotangent.le_coborderRange_of_isClosedImmersion_restrict`: **the
  result.** If `i ∣_ V` is a closed immersion then `V ≤ i.coborderRange`. No hypothesis on `V`
  beyond openness, and `i` is an arbitrary immersion.
* `Stacks.Conormal.AffineCotangent.isClosedImmersion_morphismRestrict_of_isoSpecQuotient` and
  `Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient`: the same conclusion from
  the hypothesis [Stacks, Tag 01R3] actually supplies, the presentation of the fibre.
* `Stacks.Conormal.AffineCotangent.image_range_morphismRestrict`: the bookkeeping identity
  `V.ι '' range (i ∣_ V) = range i ∩ V`, which is what makes the topology above come out.

## Route

Purely topological, on top of `Stacks.Conormal.subset_coborder_of_closure_inter_subset`.

Write `S` for the range of `i ∣_ V` inside `V`. It is closed, because a closed immersion is a
closed embedding. Its image under `V.ι` is `range i ∩ V`
(`image_range_morphismRestrict`, from `AlgebraicGeometry.morphismRestrict_ι`). Now let
`x ∈ closure (range i) ∩ V`. Since `V` is open, `IsOpen.inter_closure` puts `x` in
`closure (V ∩ range i)`, that is in `closure (V.ι '' S)`. Writing `x = V.ι a`, the open embedding
`V.ι` is inducing, so `Topology.IsInducing.closure_eq_preimage_closure_image` turns that
membership into `a ∈ closure S`, and `S` is closed, so `a ∈ S`. Hence
`x = V.ι a ∈ V.ι '' S ⊆ range i`.

That is exactly the hypothesis of `subset_coborder_of_closure_inter_subset`, whose conclusion
`V ⊆ coborder (range i)` is `V ≤ i.coborderRange` because
`AlgebraicGeometry.Scheme.Hom.coborderRange` is the coborder of the range carried into `X.Opens`.

For the presentation form, `Spec.map (Ideal.Quotient.mk I)` is a closed immersion by
`AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`, and the two isomorphisms in the
hypothesis are cancelled off by
`CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`; the comparison
`AlgebraicGeometry.pullbackRestrictIsoRestrict` then moves the conclusion from
`CategoryTheory.Limits.pullback.snd i V.ι` to `i ∣_ V`, which is its definition.

## Why this is the missing step

`StacksDraft.AlgebraicGeometry.F3.Conormal.Locality` records, in its "What is not done", that the
passage from the affine model to [Stacks, Tag 01R3]'s part (2) needs a transport along an
isomorphism of schemes. That transport is constructed as
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare` in
`StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic`, with its unit characterization
in `StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic`. What this file removes is a
*different* obstruction, which has to be removed first: that the affine open `V` of the
statement and the open `i.coborderRange` of the construction had no recorded relation at all, so
`Stacks.Conormal.Locality.conormalSheafRestrictIso` — whose second open argument ranges over
opens of the factorization's target — cannot be pointed at `V` without it. With
`V ≤ i.coborderRange` it can, via `i.coborderRange.ι ⁻¹ᵁ V`.

## Vocabulary

No new vocabulary is introduced. The statements are about Mathlib's
`AlgebraicGeometry.morphismRestrict` and `AlgebraicGeometry.Scheme.Hom.coborderRange` only, and
the one project input is `Stacks.Conormal.subset_coborder_of_closure_inter_subset`
(`StacksDraft.AlgebraicGeometry.F3.Conormal.Factorization`).

This file states no clause of any tagged statement. It is an input to the
part (2) clauses of [Stacks, Tag 01R3], and no `stacks` attribute is attached.

## Universe situation

A single universe `u` (`Scheme.{u}`), used only because `Scheme` is universe-polymorphic; nothing
here constrains it. The topological lemmas are universe-polymorphic in the ambient type.

## Transparency gotchas

A `Scheme.Hom` coerces to a function directly, *not* through `.base`: the goal after
`Set.range_comp` displays as `⇑V.ι ∘ ⇑(i ∣_ V)` and `AlgebraicGeometry.Scheme.Hom.comp_base`,
whose statement is about `(f ≫ g).base`, does not rewrite it. `image_range_morphismRestrict`
therefore transports `AlgebraicGeometry.morphismRestrict_ι` pointwise with the `congr(...)` term
elaborator and `funext`, rather than by `rw`.

`IsClosedImmersion (i ∣_ V)` is taken as an *instance* argument in
`le_coborderRange_of_isClosedImmersion_restrict` and as a hypothesis-derived `have` in the
presentation form, because instance search does not see through
`AlgebraicGeometry.pullbackRestrictIsoRestrict`.

## What is not done

* **No clause of [Stacks, Tag 01R3] is discharged and no tag is attached.** This is an input to
  its part (2), not any part of it.
* **No converse.** `V ≤ i.coborderRange` does not imply that `i ∣_ V` is a closed immersion onto
  a *quotient presentation*, and nothing here recovers the ideal `I` from `V`.
* **Nothing about sheaves.** The conormal sheaf does not appear; the content is a containment of
  opens.
* **No transport along an isomorphism of schemes** is built here. That obstruction, recorded in
  `StacksDraft.AlgebraicGeometry.F3.Conormal.Locality`, is untouched *by this file* but is no
  longer open: see
  `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Conormal.AffineCotangent

/-- The image under `V.ι` of the range of `i ∣_ V` is the range of `i` met with `V`.

`AlgebraicGeometry.morphismRestrict_ι` says `i ∣_ V ≫ V.ι = (i ⁻¹ᵁ V).ι ≫ i`, so the two
composite functions agree; the range of the right-hand one is the image under `i` of the
preimage of `V`, which is `range i ∩ V`. -/
theorem image_range_morphismRestrict {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens) :
    V.ι.base '' Set.range (i ∣_ V).base = Set.range i.base ∩ (V : Set X) := by
  rw [← Set.range_comp]
  have h : ⇑V.ι ∘ ⇑(i ∣_ V) = ⇑i ∘ ⇑(i ⁻¹ᵁ V).ι :=
    funext fun z => congr($(morphismRestrict_ι i V) z)
  rw [h, Set.range_comp, Scheme.Opens.range_ι]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, rfl⟩, hz⟩
  · rintro ⟨⟨z, rfl⟩, hx⟩
    exact ⟨z, hx, rfl⟩

/-- If `i ∣_ V` is a closed immersion then the closure of the range of `i` meets `V` only inside
the range of `i`.

`V` is open, so a point of `V` in the closure of `range i` is in the closure of `range i ∩ V`,
which is the image of the closed set `range (i ∣_ V)` under the inducing map `V.ι`. -/
theorem closure_inter_subset_range {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens)
    [IsClosedImmersion (i ∣_ V)] :
    closure (Set.range i.base) ∩ (V : Set X) ⊆ Set.range i.base := by
  have hcl : IsClosed (Set.range (i ∣_ V).base) :=
    (i ∣_ V).isClosedEmbedding.isClosed_range
  have hind : Topology.IsInducing V.ι.base := V.ι.isOpenEmbedding.isInducing
  rintro x ⟨hxc, hxV⟩
  -- `x` lies in the closure of `range i ∩ V`, because `V` is open.
  have hx1 : x ∈ closure (Set.range i.base ∩ (V : Set X)) := by
    refine Set.inter_comm _ _ ▸ ?_
    exact V.2.inter_closure ⟨hxV, hxc⟩
  rw [← image_range_morphismRestrict i V] at hx1
  -- Name `x` inside `V` and pull the membership back along the inducing `V.ι`.
  obtain ⟨a, rfl⟩ : x ∈ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hxV
  have ha : a ∈ closure (Set.range (i ∣_ V).base) := by
    rw [hind.closure_eq_preimage_closure_image]
    exact hx1
  rw [hcl.closure_eq] at ha
  exact (image_range_morphismRestrict i V ▸ Set.mem_image_of_mem _ ha).1

/-- **An open over which an immersion is a closed immersion lies in the coborder neighbourhood.**
If `i ∣_ V` is a closed immersion then `V ≤ i.coborderRange`, so the canonical closed
factorization `i.liftCoborder` is defined over the whole of `V`.

This is `Stacks.Conormal.subset_coborder_of_closure_inter_subset` applied to
`closure_inter_subset_range`. It is the companion of
`Stacks.Conormal.le_coborderRange_of_comp_eq`, which needs a factorization of the *whole* of `i`
through `V`; here only the part of `i` lying over `V` is constrained, which is all the affine
hypothesis of [Stacks, Tag 01R3] gives. -/
theorem le_coborderRange_of_isClosedImmersion_restrict {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) [IsClosedImmersion (i ∣_ V)] :
    V ≤ i.coborderRange :=
  subset_coborder_of_closure_inter_subset (closure_inter_subset_range i V)

/-- The restriction `i ∣_ V` is a closed immersion as soon as the fibre of `i` over `V` is
presented as the spectrum of a quotient of `Γ(X, V)`, compatibly with
`AlgebraicGeometry.IsAffineOpen.isoSpec`.

This is the hypothesis [Stacks, Tag 01R3]'s part (2) supplies. The right-hand side of `he` is a
closed immersion — `Spec.map (Ideal.Quotient.mk I)` is one by
`AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`, and `e.hom` is an isomorphism — and
the isomorphism `hV.isoSpec.hom` is cancelled from the right of the left-hand side. The passage
from `CategoryTheory.Limits.pullback.snd i V.ι` to `i ∣_ V` is the definition of the latter. -/
theorem isClosedImmersion_morphismRestrict_of_isoSpecQuotient {Z X : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    IsClosedImmersion (i ∣_ V) := by
  have hq : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hcomp : IsClosedImmersion (pullback.snd i V.ι ≫ hV.isoSpec.hom) := by
    rw [he]; infer_instance
  have hsnd : IsClosedImmersion (pullback.snd i V.ι) :=
    (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
      (pullback.snd i V.ι) hV.isoSpec.hom).mp hcomp
  rw [show i ∣_ V = (pullbackRestrictIsoRestrict i V).inv ≫ pullback.snd i V.ι from rfl]
  infer_instance

/-- **The containment in the form [Stacks, Tag 01R3] needs it.** The presentation of the fibre of
an immersion over an affine open `V` forces `V ≤ i.coborderRange`. -/
theorem le_coborderRange_of_isoSpecQuotient {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    V ≤ i.coborderRange :=
  have := isClosedImmersion_morphismRestrict_of_isoSpecQuotient i V hV I e he
  le_coborderRange_of_isClosedImmersion_restrict i V

end Stacks.Conormal.AffineCotangent

end
