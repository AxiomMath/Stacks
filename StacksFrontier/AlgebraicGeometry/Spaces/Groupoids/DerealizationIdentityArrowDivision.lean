module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.IdentityArrowDivision
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSpacesDerealizationProperties

/-!
# Dividing the de-realization of a groupoid in algebraic spaces on a field

`AlgebraicGeometry.GroupoidScheme.exists_division_identityArrowOpens_of_isoSpecField` divides a
groupoid *scheme* whose object scheme is the spectrum of a field by the open and closed piece of
its arrow scheme through the identity, and reads the quotient as the spectrum of a field.  It
consumes seven instances on the structure morphisms of schemes.  This file applies it to the
de-realization of a groupoid in algebraic spaces, with those seven instances supplied by the
transfers of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSpacesDerealizationProperties` from the
structure morphisms of presheaves, which is the shape in which they are available.

Five hypotheses on the groupoid in algebraic spaces suffice for the seven instances.  Local
quasi-finiteness of a morphism of algebraic spaces is **Stacks 03XJ**, part (1), which asks local
finite type of the charts as well, so the single hypothesis on the pre-relation covers both of
the division's instances for it; and zero-dimensionality of the arrow scheme is taken as it
stands, `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyArtinian_derealization_arrows`
being one route to it.

The étale strengthening asks two further properties of the source — flatness and local finite
presentation — and they transfer the same way, both being étale local on the source and the
target by **Stacks 04R3**.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.flat_derealization_source` and
  `…locallyOfFinitePresentation_derealization_source`: the two further transfers the étale
  strengthening consumes.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_division_identityArrowOpens_derealization`:
  **the division of the de-realization by the piece through the identity, with the quotient the
  spectrum of a field.**
* `…exists_division_identityArrowOpens_etale_derealization`: the same division when the source
  of the groupoid is in addition flat and locally of finite presentation, with the identity of the
  quotient groupoid an open immersion and its source and target maps étale.

## References

* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable]

/-! ### Flatness and local finite presentation of the source -/

/-- **The source map of the de-realization is flat as soon as the source of the groupoid is.** -/
theorem flat_derealization_source (h : Space.IsFlat C S hS G.source.hom) :
    Flat (derealization G).source.left :=
  holdsOnEveryEtaleChart_derealization_source G Flat.isEtaleLocalOnSourceAndTarget h

/-- **The source map of the de-realization is locally of finite presentation as soon as the
source of the groupoid is.** -/
theorem locallyOfFinitePresentation_derealization_source
    (h : Space.IsLocallyOfFinitePresentation C S hS G.source.hom) :
    LocallyOfFinitePresentation (derealization G).source.left :=
  holdsOnEveryEtaleChart_derealization_source G
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget h

/-! ### The division -/

/-- **Stacks 04S4 applied to the de-realization of a groupoid in algebraic spaces whose object
scheme is the spectrum of a field.**  A groupoid in algebraic spaces whose object and arrow
spaces are representable, whose de-realized object scheme is the spectrum of a field, whose
de-realized arrow scheme is zero-dimensional, whose source and target are locally of finite
type and whose pre-relation `j = (t, s)` is unramified, separated and locally quasi-finite can
be divided by the piece of its de-realized arrow scheme through the identity, and the quotient
is the spectrum of a field.

The hypotheses are the properties of the morphisms of *presheaves* that the groupoid carries,
which is where **Stacks 06FF** and the parts of **Stacks 050H** land them; the instances
`AlgebraicGeometry.GroupoidScheme.exists_division_identityArrowOpens_of_isoSpecField` consumes
are the transfers of those along the de-realization.  Local finite type of the pre-relation is
not a separate hypothesis: local quasi-finiteness of a morphism of algebraic spaces is
**Stacks 03XJ**, part (1), which includes it. -/
theorem exists_division_identityArrowOpens_derealization (k : Type u) [Field k]
    (iso : (derealization G).objects.left ≅ Spec (.of k))
    (hart : IsLocallyArtinian (derealization G).arrows.left)
    (hsrc : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (htgt : Space.IsLocallyOfFiniteType C S hS G.target.hom)
    (hunr : Space.IsUnramified C S hS (prod.lift G.target.hom G.source.hom))
    (hsep : Space.IsSeparated C S hS (prod.lift G.target.hom G.source.hom))
    (hqf : Space.IsLocallyQuasiFinite C S hS (prod.lift G.target.hom G.source.hom))
    (u : (derealization G).objects.left) :
    ∃ (P : Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid (derealization G))
      (D : GroupoidScheme.Division (derealization G) P.subgroupoid P.inclusion P.objects_eq),
      Set.range P.inclusion.mapArrows.left.base =
          {(derealization G).identity.left.base u} ∧
        IsField Γ(D.quotient.left, ⊤) := by
  have := hart
  have := locallyOfFiniteType_derealization_source G hsrc
  have := locallyOfFiniteType_derealization_target G htgt
  have := unramified_prodLift_derealization G hunr
  have := isSeparated_prodLift_derealization G hsep
  have := (holdsOnEveryEtaleChart_prodLift_derealization G
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hqf).1
  have := locallyQuasiFinite_prodLift_derealization G hqf
  exact GroupoidScheme.exists_division_identityArrowOpens_of_isoSpecField
    (derealization G) k iso u

/-- **The division of the de-realization by the piece through the identity has étale quotient
groupoid.**  If, on top of the hypotheses of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_division_identityArrowOpens_derealization`,
the source of the groupoid is flat and locally of finite presentation, then the identity of the
quotient groupoid `(Ū, R̄)` is an open immersion and its source and target maps are étale. -/
theorem exists_division_identityArrowOpens_etale_derealization (k : Type u) [Field k]
    (iso : (derealization G).objects.left ≅ Spec (.of k))
    (hart : IsLocallyArtinian (derealization G).arrows.left)
    (hsrc : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (htgt : Space.IsLocallyOfFiniteType C S hS G.target.hom)
    (hflat : Space.IsFlat C S hS G.source.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (hunr : Space.IsUnramified C S hS (prod.lift G.target.hom G.source.hom))
    (hsep : Space.IsSeparated C S hS (prod.lift G.target.hom G.source.hom))
    (hqf : Space.IsLocallyQuasiFinite C S hS (prod.lift G.target.hom G.source.hom))
    (u : (derealization G).objects.left) :
    ∃ (P : Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid (derealization G))
      (D : GroupoidScheme.Division (derealization G) P.subgroupoid P.inclusion P.objects_eq),
      Set.range P.inclusion.mapArrows.left.base =
          {(derealization G).identity.left.base u} ∧
        IsField Γ(D.quotient.left, ⊤) ∧ IsOpenImmersion D.descended.identity.left ∧
          Etale D.descended.source.left ∧ Etale D.descended.target.left := by
  have := hart
  have := locallyOfFiniteType_derealization_source G hsrc
  have := locallyOfFiniteType_derealization_target G htgt
  have := flat_derealization_source G hflat
  have := locallyOfFinitePresentation_derealization_source G hlfp
  have := unramified_prodLift_derealization G hunr
  have := isSeparated_prodLift_derealization G hsep
  have := (holdsOnEveryEtaleChart_prodLift_derealization G
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hqf).1
  have := locallyQuasiFinite_prodLift_derealization G hqf
  exact GroupoidScheme.exists_division_identityArrowOpens_etale_of_isoSpecField
    (derealization G) k iso u

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
