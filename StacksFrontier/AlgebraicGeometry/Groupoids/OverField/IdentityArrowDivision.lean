module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.DivisionEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.FieldObjectDivision
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.IdentityArrowSubgroupoid

/-!
# Dividing a groupoid on a field by the piece through the identity

Let `(U, R, s, t, c)` be a groupoid scheme whose object scheme is the spectrum of a field `k`,
whose source and target maps are locally of finite type, whose pre-relation `j = (t, s)` is
unramified, separated and locally quasi-finite, and whose arrow scheme is zero-dimensional.  Then
the open and closed piece `P ⊆ R` through the identity can be divided out, and the quotient
`Ū = U/P` is the spectrum of a field.

This is the step of the proof of **Stacks 06N0** which produces the field `k₀` of invariants.
Every hypothesis of the division of **Stacks 04S4** is met by the piece through the identity:

* affineness of the object scheme and finite local freeness of `s|_P` and `t|_P` reduce, over a
  field, to finiteness of `s|_P` and `t|_P`, which is
  `Stacks.Groupoids.GroupoidScheme.isFinite_openArrowSource_identityArrowOpens` and its
  companion;
* that the inclusion of arrow schemes is a monomorphism is that it is an open immersion;
* that the pre-relation of `P` is a monomorphism is
  `Stacks.Groupoids.GroupoidScheme.mono_prodLift_of_unramified`, which plays the role of the
  computation `A ⊗_{k ⊗ k} k = k` of the source: universal injectivity of `j|_P` comes from the
  identity section, and **Stacks 05VH** turns it together with unramifiedness into a
  monomorphism;
* separatedness, local finite type and local quasi-finiteness of the ambient pre-relation are
  hypotheses; in the setting of Stacks 06N0 they are the DM hypothesis read through
  **Stacks 050H**, parts (3), (1) and (5), and unramifiedness of the ambient pre-relation is
  part (4) of the same tag.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_division_identityArrowOpens_of_isoSpecField`: the
  division by the piece through the identity, with the quotient's global functions a field.
* `AlgebraicGeometry.GroupoidScheme.exists_division_identityArrowOpens_etale_of_isoSpecField`:
  the same division when the source map is in addition flat and locally of finite presentation,
  with the identity of the quotient groupoid an open immersion and its source and target maps
  étale.

## Implementation notes

The field-ness of the quotient is stated for the global functions of the quotient scheme, as
`AlgebraicGeometry.GroupoidScheme.exists_division_isField_quotient_of_isoSpecField` states it:
the quotient is produced as an affine scheme rather than as the spectrum of a named field, and
`AlgebraicGeometry.Scheme.isoSpec` recovers the spectrum presentation.

Zero-dimensionality of the arrow scheme is `AlgebraicGeometry.IsLocallyArtinian`; the two
hypotheses on the object scheme that the construction of the piece needs — that it has one point
and that it is zero-dimensional — are derived from the isomorphism onto the spectrum of the
field.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 05VH](https://stacks.math.columbia.edu/tag/05VH)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Groupoids.GroupoidScheme

namespace GroupoidScheme

/-- **Stacks 04S4 applied to the open and closed piece through the identity.**  A groupoid scheme
whose object scheme is the spectrum of a field, whose arrow scheme is zero-dimensional and whose
pre-relation is unramified, separated, locally of finite type and locally quasi-finite can be
divided by the piece of its arrow scheme through the identity, and the quotient is the spectrum
of a field. -/
@[stacks 06N0 "the division of the groupoid of a flat field-valued presentation by the open and \
closed piece of its arrow scheme through the identity, with the quotient the spectrum of a \
field: the step of the proof which produces the field k_0 of invariants"]
theorem exists_division_identityArrowOpens_of_isoSpecField {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (k : Type u) [Field k]
    (iso : G.objects.left ≅ Spec (.of k))
    [IsLocallyArtinian G.arrows.left]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [Unramified (prod.lift G.target G.source).left]
    [IsSeparated (prod.lift G.target G.source).left]
    [LocallyOfFiniteType (prod.lift G.target G.source).left]
    [LocallyQuasiFinite (prod.lift G.target G.source).left]
    (u : G.objects.left) :
    ∃ (P : OpenFiniteSubgroupoid G)
      (D : Division G P.subgroupoid P.inclusion P.objects_eq),
      Set.range P.inclusion.mapArrows.left.base = {G.identity.left.base u} ∧
        IsField Γ(D.quotient.left, ⊤) := by
  have : Subsingleton G.objects.left :=
    ⟨fun a b => iso.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  have : Nonempty G.objects.left := ⟨u⟩
  have : IsLocallyArtinian G.objects.left := IsLocallyArtinian.of_isImmersion iso.hom
  have hmono : Mono (prod.lift (identityOpenFiniteSubgroupoid G u).subgroupoid.target
      (identityOpenFiniteSubgroupoid G u).subgroupoid.source) :=
    mono_prodLift_of_unramified (identityArrowOpens G u) (mem_identityArrowOpens G u)
  have hmonoι : Mono (identityOpenFiniteSubgroupoid G u).inclusion.mapArrows :=
    mono_openOverι G.arrows (identityArrowOpens G u)
  have hsrc : IsFinite (identityOpenFiniteSubgroupoid G u).subgroupoid.source.left :=
    isFinite_openArrowSource_identityArrowOpens G u
  have htgt : IsFinite (identityOpenFiniteSubgroupoid G u).subgroupoid.target.left :=
    isFinite_openArrowTarget_identityArrowOpens G u
  obtain ⟨D, hD⟩ := exists_division_isField_quotient_of_isoSpecField G
    (identityOpenFiniteSubgroupoid G u).subgroupoid
    (identityOpenFiniteSubgroupoid G u).inclusion
    (identityOpenFiniteSubgroupoid G u).objects_eq
    (identityOpenFiniteSubgroupoid G u).mapObjects_eq k iso
  exact ⟨identityOpenFiniteSubgroupoid G u, D,
    range_identityOpenFiniteSubgroupoid_inclusion G u, hD⟩

/-- **The division by the piece through the identity has étale quotient groupoid.**  If, on top of
the hypotheses of
`AlgebraicGeometry.GroupoidScheme.exists_division_identityArrowOpens_of_isoSpecField`, the source
map of the groupoid is flat and locally of finite presentation, then the identity of the quotient
groupoid `(Ū, R̄)` is an open immersion and its source and target maps are étale.

The identity is an open immersion because the piece `P` through the identity is exactly the part
of `R` lying over `ē`, which is
`AlgebraicGeometry.GroupoidScheme.Division.descend_isPullback_identity`; étaleness is then
**Stacks 047W** at unramifiedness, after flatness and local finite presentation descend from `s`
to `s̄`.  This is the "after the division" step of the proof of **Stacks 06N0**, at the level of
groupoid schemes. -/
theorem exists_division_identityArrowOpens_etale_of_isoSpecField {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (k : Type u) [Field k]
    (iso : G.objects.left ≅ Spec (.of k))
    [IsLocallyArtinian G.arrows.left]
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Unramified (prod.lift G.target G.source).left]
    [IsSeparated (prod.lift G.target G.source).left]
    [LocallyOfFiniteType (prod.lift G.target G.source).left]
    [LocallyQuasiFinite (prod.lift G.target G.source).left]
    (u : G.objects.left) :
    ∃ (P : OpenFiniteSubgroupoid G)
      (D : Division G P.subgroupoid P.inclusion P.objects_eq),
      Set.range P.inclusion.mapArrows.left.base = {G.identity.left.base u} ∧
        IsField Γ(D.quotient.left, ⊤) ∧ IsOpenImmersion D.descended.identity.left ∧
          Etale D.descended.source.left ∧ Etale D.descended.target.left := by
  obtain ⟨P, D, hrange, hfield⟩ :=
    exists_division_identityArrowOpens_of_isoSpecField G k iso u
  let := P.arrows_open
  exact ⟨P, D, hrange, hfield, D.isOpenImmersion_descended_identity,
    D.etale_descended_source, D.etale_descended_target⟩

end GroupoidScheme

end AlgebraicGeometry

end
