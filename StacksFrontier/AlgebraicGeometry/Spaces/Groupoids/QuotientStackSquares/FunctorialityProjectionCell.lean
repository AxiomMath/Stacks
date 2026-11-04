module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection

/-!
# The projection of Stacks 044R against the induced 1-morphism of Stacks 046Q

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, written `f : U ⟶ U'` on object
spaces. Stacks 046Q gives the induced 1-morphism `[φ] : [U/R] ⟶ [U'/R']` and Stacks 044R the
projections `π : 𝒮_U ⟶ [U/R]` and `π' : 𝒮_{U'} ⟶ [U'/R']`. This file builds the vertical
2-isomorphism

    π ≫ [φ] ≅ 𝒮_f ≫ π'

filling the square of Stacks 04ZN, where `𝒮_f : 𝒮_U ⟶ 𝒮_{U'}` is the 1-morphism of Stacks 0458
attached to `f`.

Stacks 046Q is recorded against the stackification map out of the pointwise presentation,
`AlgebraicGeometry.Stack.quotientStackMap_commutes`, and the projection of Stacks 044R is that
same stackification map precomposed with the inclusion of the object points,
`AlgebraicGeometry.Stack.pointwiseObjectInclusion`. So the 2-isomorphism wanted is the
restriction of the one of Stacks 046Q along that inclusion, and what has to be checked is that
the inclusion of the object points *strictly* intertwines the map on object spaces with the map
of pointwise presentations. That is
`AlgebraicGeometry.Stack.pointwiseObjectInclusion_comp_quotientPointwiseMap`, and it is an
equality of functors rather than merely a 2-isomorphism because both sides send a morphism of
the object-space fibration to a morphism of the pointwise presentation whose fibre component is
an `eqToHom`: on one side because the fibres of the object-space fibration are discrete, on the
other because the strong naturality constraint of the pointwise map of Stacks 046Q is an
`eqToIso` (`AlgebraicGeometry.Stack.quotientPointwiseMapData`).

`AlgebraicGeometry.Stack.quotientStackProjection_comp_quotientStackMap` records the weaker
statement that the two composites agree after a further 1-morphism into a category fibred in
sets, which is all that the 2-commutativity of the Stacks 0DTG square needs; the 2-isomorphism
built here is what a 2-fibre-product statement about the square needs instead.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackProjectionCell`: the 2-isomorphism filling the square.

## Main results

* `AlgebraicGeometry.Stack.pointwiseObjectInclusion_comp_quotientPointwiseMap`: the inclusion of
  the object points strictly intertwines the two maps of presentations.
* `AlgebraicGeometry.Stack.quotientStackProjectionCell_isHomLift`: every component of the
  2-isomorphism lies over an identity of the site, so it is a 2-morphism of the 2-category of
  categories over the site.

## Implementation notes

The 2-isomorphism is stated with the composite through the pointwise presentation as its target,
not with `𝒮_f ≫ π'`, even though
`AlgebraicGeometry.Stack.pointwiseObjectInclusion_comp_quotientPointwiseMap_comp` says the two are
equal. Transporting it along that equality — composing with the corresponding `eqToIso` — produces
a 2-isomorphism whose components no longer reduce within the heartbeat budget: identifying the
middle object of the composite forces the elaborator through the stackification that defines
`AlgebraicGeometry.Stack.quotientStackMap`. The identification with `𝒮_f ≫ π'` is instead made one
component at a time, in `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted`.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/- The pointwise presentation is a `CoGrothendieck` construction reached through
`AlgebraicGeometry.Stack.presheafOfGroupoids` and `CategoryTheory.Functor.toPseudofunctor'`, and
the object-space fibration through the subtype of categories fibred in groupoids; neither chain is
type-correct at the `implicit` transparency level that `rw` and `simp only` re-check against, so
naming them is what lets the fibre component of a morphism of either be rewritten. -/
section Transparency

attribute [local implicit_reducible] Bicategory.InducedBicategory
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  BasedCategory.ofFunctor Grpd.forgetToCat Grpd.of CategoryTheory.instCategoryObj
  Pseudofunctor.CoGrothendieck.category Pseudofunctor.CoGrothendieck.categoryStruct

/-- **The 1-morphism of object-space stacks induced by a morphism of groupoids**: the 1-morphism
of Stacks 0458 attached to the map on object spaces. -/
noncomputable abbrev objectSpaceMap (φ : Hom G G') :
    (fibredCategory C S hS G.objects.obj).val ⥤ᵇ (fibredCategory C S hS G'.objects.obj).val :=
  (associatedMap C S hS φ.toGroupoidHom.mapObjects).1.hom

/-- **The inclusion of the object points strictly intertwines the map on object spaces with the
map of pointwise presentations.**

Both composites send a point `(T, x)` of the object space to the point `(T, f_T(x))` of the
pointwise presentation of `(U', R', s', t', c')`, and send a morphism to the morphism over the
same morphism of the site whose fibre component is an `eqToHom`: on the left because the strong
naturality constraint of `AlgebraicGeometry.Stack.quotientPointwiseMapData` is an `eqToIso`, on
the right because the fibres of the object-space fibration are discrete. Two `eqToHom`s with the
same source and target are equal. -/
theorem pointwiseObjectInclusion_comp_quotientPointwiseMap (φ : Hom G G') :
    pointwiseObjectInclusion G ⋙ (quotientPointwiseMap φ).toFunctor =
      (objectSpaceMap φ).toFunctor ⋙ pointwiseObjectInclusion G' := by
  refine CategoryTheory.Functor.hext (fun x => rfl) ?_
  intro x y f
  refine heq_of_eq ?_
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  obtain ⟨h, hh⟩ := (quotientPointwiseMapData φ).property.2 (f.base.op.toLoc)
  simp only [Functor.comp_map, quotientPointwiseMap, Pseudofunctor.CoGrothendieck.map,
    pointwiseObjectInclusion, hh, eqToIso.hom, Cat.eqToHom_app, eqToHom_map, eqToHom_trans]
  exact (eqToHom_trans _ _).symm

end Transparency

/-- The equality of functors underlying the 2-isomorphism: the inclusion of the object points
followed by the pointwise map of Stacks 046Q and the stackification of `(U', R', s', t', c')` is
the map on object spaces followed by the projection of Stacks 044R. -/
theorem pointwiseObjectInclusion_comp_quotientPointwiseMap_comp (φ : Hom G G') :
    pointwiseObjectInclusion G ⋙
        (quotientPointwiseMap φ).toFunctor ⋙ pointwiseToQuotientStack G' =
      (objectSpaceMap φ).toFunctor ⋙ (quotientStackProjection G').toFunctor :=
  congrArg (fun K => K ⋙ pointwiseToQuotientStack G')
    (pointwiseObjectInclusion_comp_quotientPointwiseMap φ)

/-- The 2-isomorphism of Stacks 046Q restricted along the inclusion of the object points: the
projection of Stacks 044R followed by the induced 1-morphism of Stacks 046Q is 2-isomorphic to
the inclusion of the object points followed by the pointwise map of Stacks 046Q and the
stackification of `(U', R', s', t', c')`.

`AlgebraicGeometry.Stack.pointwiseObjectInclusion_comp_quotientPointwiseMap_comp` identifies the
target with `𝒮_f ≫ π'`, which is the shape in which the square of Stacks 04ZN wants it; it is
kept separate so that the components of this 2-isomorphism stay the components of the one of
Stacks 046Q, with no transport. -/
noncomputable def quotientStackProjectionCell (φ : Hom G G') :
    (quotientStackProjection G).toFunctor ⋙ (quotientStackMap φ).toFunctor ≅
      pointwiseObjectInclusion G ⋙
        (quotientPointwiseMap φ).toFunctor ⋙ pointwiseToQuotientStack G' :=
  (CategoryTheory.Functor.isoWhiskerLeft (pointwiseObjectInclusion G)
    ((BasedNatTrans.forgetful (presheafOfGroupoids
          (evaluationGroupoidFunctor G.toGroupoidInFunctors)) (quotientStack G')).mapIso
      (quotientStackMap_commutes φ))).symm

/-- **Every component of the 2-isomorphism lies over an identity of the site**, so it is a
2-morphism of the 2-category of categories over the big fppf site: it is a component of the
2-isomorphism of Stacks 046Q, which is vertical. -/
theorem quotientStackProjectionCell_isHomLift (φ : Hom G G')
    (x : (fibredCategory C S hS G.objects.obj).val.obj) :
    (quotientStack G').p.IsHomLift
      (𝟙 ((fibredCategory C S hS G.objects.obj).val.p.obj x))
      ((quotientStackProjectionCell φ).hom.app x) :=
  (quotientStackMap_commutes φ).inv.isHomLift' ((pointwiseObjectInclusion G).obj x)

end AlgebraicGeometry.Stack

end
