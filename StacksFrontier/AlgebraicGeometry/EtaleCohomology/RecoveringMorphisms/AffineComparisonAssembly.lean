module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ExistenceFromAffineComparison

/-!
# The per-chart comparison of Stacks 04I6, as a datum indexed by the affine subsite

`AlgebraicGeometry.comparisonSheafHom` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/ComparisonNatural.lean` is the
comparison `g⁻¹h_V ⟶ h_{X ×_Y V}` of step (3) of the proof of [Stacks Project, Tag 04I6] at an
*affine* étale chart `V` of an affine `Y`, natural in `V`
(`AlgebraicGeometry.comparisonSheafHom_naturality_chart`).  It is indexed by the objects `V` of
the small étale site carrying an affineness instance, which is the convenient form in which to
construct it; `AlgebraicGeometry.AffineRepresentableComparison`, the input of the transport in
`RecoveringMorphisms/ExistenceFromAffineComparison.lean`, is indexed by the objects of the small
affine étale site, which is the form a *functor* on the subsite has to take.

This file is that re-indexing, together with the bridge from iso-ness at each affine chart to the
comparison datum.  Both of the two things it leaves open are now closed elsewhere: that each
`AlgebraicGeometry.affineComparisonSheafHom` is an isomorphism is
`AlgebraicGeometry.isIso_affineComparisonSheafHom` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineComparisonIsIso.lean`,
and the agreement of the two structure maps — the `hcomm` hypothesis of
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_affineRepresentableComparison` — is
`AlgebraicGeometry.forgetFSharp_comp_pushforwardIsoOfAffineRepresentableComparison` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`, which is
also where [Stacks Project, Tag 04I6] itself is proved.  Nothing here carries a `@[stacks 04I6]`
tag.

## Implementation notes

The types of the components are written out rather than left to unfold, and the naturality is
stated at `(SmallAffineEtale.inclusion …).map k` rather than at `k`.  Both are needed: a morphism
of a full subcategory is only *definitionally* a morphism of the ambient category, and leaving the
elaborator to see that through the tower `Sheaf (SmallEtale.topology …) (Type u)` exhausts the
heartbeat budget.  The affineness instance is supplied from
`ObjectProperty.FullSubcategory.property` in both of the two spellings that come up, for the same
reason.

## Main definitions

* `AlgebraicGeometry.affineComparisonSheafHom` — the comparison at an object of the small
  affine étale site.
* `AlgebraicGeometry.affineComparisonNatTrans` — the resulting natural transformation
  `(V₀ ↦ g⁻¹h_{V₀}) ⟶ (V₀ ↦ h_{X ×_Y V₀})` on the affine subsite.
* `AlgebraicGeometry.affineRepresentableComparisonOfIsIso` — the comparison *datum*
  `AlgebraicGeometry.AffineRepresentableComparison`, given iso-ness at each affine chart.

## Main results

* `AlgebraicGeometry.affineComparisonSheafHom_naturality` — naturality in the affine chart, at
  the indexing of the subsite.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (f : X ⟶ Y)
  (hf : (B.inclusion.map f).appTop =
    g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property))
  [IsAffine Y.obj]

include hf in
/-- **The comparison of step (3) of Stacks 04I6, read at an object of the small affine
étale site.**  This is `AlgebraicGeometry.comparisonSheafHom` at the underlying chart, the
affineness it asks for being the defining property of the object. -/
def affineComparisonSheafHom (V₀ : SmallAffineEtale B Y.obj Y.property) :
    g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V₀.obj) ⟶
      (SmallEtale.topology B X.obj X.property).yoneda.obj
        ((smallEtaleBaseChange B f).obj V₀.obj) :=
  haveI := V₀.property
  comparisonSheafHom B g f hf V₀.obj

include hf in
/-- `AlgebraicGeometry.affineComparisonSheafHom` is `AlgebraicGeometry.comparisonSheafHom`, for
any affineness instance on the underlying chart. -/
theorem affineComparisonSheafHom_eq (V₀ : SmallAffineEtale B Y.obj Y.property)
    [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V₀.obj)] :
    affineComparisonSheafHom B g f hf V₀ = comparisonSheafHom B g f hf V₀.obj :=
  rfl

include hf in
/-- **The comparison is natural in the object of the small affine étale site**, which is
`AlgebraicGeometry.comparisonSheafHom_naturality_chart` re-indexed. -/
theorem affineComparisonSheafHom_naturality {V₀ V₀' : SmallAffineEtale B Y.obj Y.property}
    (k : V₀ ⟶ V₀') :
    g.toToposHom.inverseImage.map
          ((SmallEtale.topology B Y.obj Y.property).yoneda.map
            ((SmallAffineEtale.inclusion B Y.obj Y.property).map k)) ≫
        affineComparisonSheafHom B g f hf V₀' =
      affineComparisonSheafHom B g f hf V₀ ≫
        (SmallEtale.topology B X.obj X.property).yoneda.map
          ((smallEtaleBaseChange B f).map
            ((SmallAffineEtale.inclusion B Y.obj Y.property).map k)) :=
  have := V₀.property
  have := V₀'.property
  have : IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj
      ((SmallAffineEtale.inclusion B Y.obj Y.property).obj V₀)) := V₀.property
  have : IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj
      ((SmallAffineEtale.inclusion B Y.obj Y.property).obj V₀')) := V₀'.property
  comparisonSheafHom_naturality_chart B g f hf V₀.obj
    ((SmallAffineEtale.inclusion B Y.obj Y.property).map k)

include hf in
/-- **The comparison, as a natural transformation of functors on the small affine étale
site.**  Its source and target are the two functors of
`AlgebraicGeometry.AffineRepresentableComparison`. -/
def affineComparisonNatTrans :
    SmallAffineEtale.inclusion B Y.obj Y.property ⋙
        (SmallEtale.topology B Y.obj Y.property).yoneda ⋙ g.toToposHom.inverseImage ⟶
      SmallAffineEtale.inclusion B Y.obj Y.property ⋙
        smallEtaleBaseChange B f ⋙ (SmallEtale.topology B X.obj X.property).yoneda where
  app V₀ := affineComparisonSheafHom B g f hf V₀
  naturality _ _ k := affineComparisonSheafHom_naturality B g f hf k

include hf in
/-- **The comparison datum of Stacks 04I6 at the affine charts, from iso-ness chart by chart.**
Given that the comparison is an isomorphism at every affine étale chart of `Y` — the stalk
computation of step (3) of the source's proof — the natural transformation above is a natural
isomorphism, which is exactly the hypothesis of
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_affineRepresentableComparison`.

So, modulo that iso-ness and the agreement of the two structure maps, the existence half of
[Stacks Project, Tag 04I6] is assembled: no further infrastructure intervenes between here and
the `∃!`. -/
def affineRepresentableComparisonOfIsIso
    (hiso : ∀ V₀ : SmallAffineEtale B Y.obj Y.property,
      IsIso (affineComparisonSheafHom B g f hf V₀)) :
    AffineRepresentableComparison B g f :=
  NatIso.ofComponents (fun V₀ => haveI := hiso V₀; asIso (affineComparisonSheafHom B g f hf V₀))
    (fun k => affineComparisonSheafHom_naturality B g f hf k)

end AlgebraicGeometry

end
