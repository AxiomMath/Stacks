module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer

/-!
# Stacks 0AKX: the implication (2) ⟹ (1) without a formal algebraic space, and the transfer
results applied to it

Let `S` be a scheme contained in a big fppf site `B`. This file collects the additions to
`StacksFrontier/AlgebraicGeometry/FormalSpace/TypeTransfer.lean` made while working on Stacks 0AKX,
kept apart from that file.

## Main results

* `AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_of_hasAffineEtaleAtlasWithProperty`:
  the implication (2) ⟹ (1) of Stacks 0AKX alone, which assumes no formal algebraic space.
* `hasAffineEtaleChartProperty_iff_atlas_isCountablyIndexed` and its four companions: the
  equivalence of Stacks 0AKX at each of the five properties of the source's list, with the
  hypothesis `htransfer` replaced by the hypotheses of the transfer result for that property.
  None of them is registered: Stacks 0AKX with no hypotheses is
  `hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AKX, the implication (2) ⟹ (1)**, for a property `P` of affine formal algebraic
spaces as in
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`:
*every* fppf sheaf admitting an atlas as in Definition 0AIM all of whose members satisfy `P`
has the chart property `P`, with no assumption that the sheaf be a formal algebraic space.

The hypothesis `hX : IsFormalAlgebraicSpace B S hS X` of the equivalence is what produces the
atlas of condition (2) out of condition (1); the converse implication consumes only the atlas
that condition (2) itself supplies, so the assumption is not needed here. This is the source's
own division of labour: its proof of (2) ⟹ (1) names the family `{Xᵢ ⟶ X}` of condition (2)
and never Definition 0AIM for `X`. Dropping the assumption matters because a consumer which
quantifies over every sheaf carrying such an atlas — `HasAffineEtaleAtlasWithProperty` does
not include the set-theoretic condition of Stacks 0AIS, so it does not give
`IsFormalAlgebraicSpace` — cannot be served by the equivalence above.

The two hypotheses of the equivalence which belong to the implication (2) ⟹ (1) are both
kept: `href` is the refinement of the atlas against the chart and `htransfer` is the transfer
of `P` along the resulting surjective flat morphism of finite type. -/
theorem hasAffineEtaleChartProperty_of_hasAffineEtaleAtlasWithProperty
    (P : FppfSheaf B S hS → Prop)
    (href : HasAffineEtaleRefinementWithProperty B S hS P)
    (htransfer : ∀ {W Z : FppfSheaf B S hS} (w : W ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS W → IsAffineFormalAlgebraicSpace B S hS Z →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom →
      IsSurjective B S hS w → IsRepresentableFlat B S hS w →
      IsLocallyOfFiniteType B S hS w → (P W ↔ P Z)) :
    ∀ T : FppfSheaf B S hS, HasAffineEtaleAtlasWithProperty B S hS T P →
      HasAffineEtaleChartProperty B S hS T P := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro T h
  obtain ⟨J, Zj, gj, hZjaff, hZjet, hZjsurj, hZjP⟩ := h
  intro Y g hY hg
  obtain ⟨W, w, hWaff, hWP, hwrep, hwsurj, hwflat, hwft⟩ :=
    href J Zj gj hZjaff hZjet hZjsurj hZjP Y g hY hg
  exact (htransfer w hWaff hY hwrep hwsurj hwflat hwft).1 hWP

/-! ### Stacks 0AKX at the five properties of the source's list

Each of the five results below is
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`
at one property, with its hypothesis `htransfer` discharged by the transfer result for that
property and replaced by that result's own hypotheses. The refinement step `href` remains a
hypothesis throughout.
-/

/-- **Stacks 0AKX at the countably indexed property.** Let `X` be a formal algebraic space over
`S`. Then every affine formal algebraic space representable étale over `X` is countably indexed
if and only if `X` admits an atlas as in Definition 0AIM all of whose members are countably
indexed.

The hypothesis `htransfer` of
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`
is discharged by `AlgebraicGeometry.FormalSpace.isCountablyIndexed_iff_of_surjective_flat`,
which is Stacks 0AKS and takes no hypothesis beyond the source's. Its finiteness of type is
unused, Stacks 0AKS asking for none.

For this one property
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentableEtale` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedChartLocality.lean` goes further and
discharges `href` as well, at two further inputs this library does not carry; it states the
implication (2) ⟹ (1) alone. -/
theorem hasAffineEtaleChartProperty_iff_atlas_isCountablyIndexed (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (href : HasAffineEtaleRefinementWithProperty B S hS (IsCountablyIndexed B S hS)) :
    HasAffineEtaleChartProperty B S hS X (IsCountablyIndexed B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsCountablyIndexed B S hS) :=
  hasAffineEtaleChartProperty_iff_of_refinement_of_transfer B S hS X
    (IsCountablyIndexed B S hS) hX href
    (fun w hW hW' hw hwsurj hwflat _ ↦
      isCountablyIndexed_iff_of_surjective_flat B S hS w hW hW' hw hwsurj hwflat)

/-- **Stacks 0AKX at the countably indexed and classical property.** Let `X` be a formal
algebraic space over `S`. Then every affine formal algebraic space representable étale over `X`
is countably indexed and classical if and only if `X` admits an atlas as in Definition 0AIM all
of whose members are.

The hypothesis `htransfer` of
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`
is discharged by
`AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_iff_of_surjective_flat`, which is
Stacks 0GXR and takes no hypothesis beyond the source's. Its finiteness of type is unused,
Stacks 0GXR asking for none. -/
theorem hasAffineEtaleChartProperty_iff_atlas_isCountablyIndexedAndClassical
    (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (href : HasAffineEtaleRefinementWithProperty B S hS
      (fun Z ↦ IsCountablyIndexed B S hS Z ∧ IsClassical B S hS Z)) :
    HasAffineEtaleChartProperty B S hS X
        (fun Z ↦ IsCountablyIndexed B S hS Z ∧ IsClassical B S hS Z) ↔
      HasAffineEtaleAtlasWithProperty B S hS X
        (fun Z ↦ IsCountablyIndexed B S hS Z ∧ IsClassical B S hS Z) :=
  hasAffineEtaleChartProperty_iff_of_refinement_of_transfer B S hS X
    (fun Z ↦ IsCountablyIndexed B S hS Z ∧ IsClassical B S hS Z) hX href
    (fun w hW hW' hw hwsurj hwflat _ ↦
      isCountablyIndexedAndClassical_iff_of_surjective_flat B S hS w hW hW' hw hwsurj hwflat)

/-- **Stacks 0AKX at the weakly adic property.** Let `X` be a formal algebraic space over `S`.
Then every affine formal algebraic space representable étale over `X` is weakly adic if and
only if `X` admits an atlas as in Definition 0AIM all of whose members are weakly adic.

The hypothesis `htransfer` of
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`
is discharged by `AlgebraicGeometry.FormalSpace.isWeaklyAdic_iff_of_surjective_flat`, which is
Stacks 0GXS and takes no hypothesis beyond the source's. Its finiteness of type is unused,
Stacks 0GXS asking for none. -/
theorem hasAffineEtaleChartProperty_iff_atlas_isWeaklyAdic (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (href : HasAffineEtaleRefinementWithProperty B S hS (IsWeaklyAdic B S hS)) :
    HasAffineEtaleChartProperty B S hS X (IsWeaklyAdic B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsWeaklyAdic B S hS) :=
  hasAffineEtaleChartProperty_iff_of_refinement_of_transfer B S hS X
    (IsWeaklyAdic B S hS) hX href
    (fun w hW hW' hw hwsurj hwflat _ ↦
      isWeaklyAdic_iff_of_surjective_flat B S hS w hW hW' hw hwsurj hwflat)

/-- **Stacks 0AKX at the adic\* property.** Let `X` be a formal algebraic space over `S`. Then
every affine formal algebraic space representable étale over `X` is adic\* if and only if `X`
admits an atlas as in Definition 0AIM all of whose members are adic\*.

The hypothesis `htransfer` of
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`
is discharged by `AlgebraicGeometry.FormalSpace.isAdicStar_iff_of_surjective_flat`, which is
Stacks 0AKT and takes no hypothesis beyond the source's. Its finiteness of type is unused,
Stacks 0AKT asking for none. -/
theorem hasAffineEtaleChartProperty_iff_atlas_isAdicStar (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (href : HasAffineEtaleRefinementWithProperty B S hS (IsAdicStar B S hS)) :
    HasAffineEtaleChartProperty B S hS X (IsAdicStar B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsAdicStar B S hS) :=
  hasAffineEtaleChartProperty_iff_of_refinement_of_transfer B S hS X
    (IsAdicStar B S hS) hX href
    (fun w hW hW' hw hwsurj hwflat _ ↦
      isAdicStar_iff_of_surjective_flat B S hS w hW hW' hw hwsurj hwflat)

/-- **Stacks 0AKX at the Noetherian property.** Let `X` be a formal algebraic space over `S`.
Then every affine formal algebraic space representable étale over `X` is Noetherian if and only
if `X` admits an atlas as in Definition 0AIM all of whose members are Noetherian.

The hypothesis `htransfer` of
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`
is discharged by `AlgebraicGeometry.FormalSpace.isNoetherian_iff_of_surjective_flat`, which is
Stacks 0AKW and takes no hypothesis beyond the source's. This is the one of the five that
does consume the finiteness of type `htransfer` offers, Stacks 0AKW asking for it. -/
theorem hasAffineEtaleChartProperty_iff_atlas_isNoetherian (X : FppfSheaf B S hS)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (href : HasAffineEtaleRefinementWithProperty B S hS (IsNoetherian B S hS)) :
    HasAffineEtaleChartProperty B S hS X (IsNoetherian B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsNoetherian B S hS) :=
  hasAffineEtaleChartProperty_iff_of_refinement_of_transfer B S hS X
    (IsNoetherian B S hS) hX href
    (fun w hW hW' hw hwsurj hwflat hwft ↦
      isNoetherian_iff_of_surjective_flat B S hS w hW hW' hw hwsurj hwflat hwft)

end AlgebraicGeometry.FormalSpace

end
