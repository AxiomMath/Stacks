module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackDiagram

/-!
# The base-change square of quotient stacks 2-commutes (Stacks 0DTG)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `φ : U ⟶ X` be an `R`-invariant morphism of algebraic spaces
over `B`, and let `g : X' ⟶ X` be a morphism of algebraic spaces over `B`. Let
`(U', R', s', t', c')` be the base change of Stacks 048G. Stacks 0DTG displays the square

    [U'/R'] ---> [U/R]
      |            |
      v            v
     𝒮_{X'} ---> 𝒮_X

of stacks in groupoids over the big fppf site and asserts that it is a 2-fibre product. The four
arrows are built in
`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/BaseChangeQuotientStackDiagram.lean`. This file
proves that the square **2-commutes**, in the strong form of an equality of 1-morphisms, and
packages it as an object of the category of 2-commutative diagrams of Stacks 003O. The
2-fibre-product assertion itself is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/BaseChangeQuotientStackComparisonFibreFull.lean`.

The step that was missing for this is a compatibility between the two canonical constructions
attached to a quotient stack: the projection `π : 𝒮_U ⟶ [U/R]` of Stacks 044R and the induced
1-morphism `[f] : [U/R] ⟶ [U'/R']` of Stacks 046Q. Stacks 046Q is recorded against the
*stackification map* out of the pointwise presentation
(`AlgebraicGeometry.Stack.quotientStackMap_commutes`), and restricting that 2-isomorphism along
the inclusion of the object points is what turns it into a statement about `π`.

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare`: **Stacks 0DTG**, the displayed square,
  as a 2-commutative diagram of stacks in groupoids over the big fppf site.

## Main results

* `AlgebraicGeometry.Stack.quotientStackProjection_comp_quotientStackMap`: the projection of
  Stacks 044R composed with the induced 1-morphism of Stacks 046Q is the morphism of object
  spaces composed with the projection, as 1-morphisms into the category fibred in sets of a
  presheaf.
* `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare_commutes` and
  `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare_lifted_commutes`: the square commutes on
  the nose, at the original hom universe and after enlarging it.

## Implementation notes

The displayed compatibility of the projection with the induced 1-morphism cannot hold as an
equality of 1-morphisms `𝒮_{U'} ⟶ [U/R]`: `AlgebraicGeometry.Stack.quotientStackMap` is produced
by the universal property of the stackification, so a composite with it is pinned down only up to
the 2-isomorphism `AlgebraicGeometry.Stack.quotientStackMap_commutes`. What *is* an equality is
the composite with any further 1-morphism into the category fibred in **sets** of a presheaf,
because a 2-morphism over the site between two 1-morphisms into such a category is an identity
(Stacks 02Y2). That is the shape of
`AlgebraicGeometry.Stack.quotientStackProjection_comp_quotientStackMap`, and it is the shape the
2-commutativity of the Stacks 0DTG square needs, since the bottom right corner of that square is
the algebraic space `X`.

Only the action on objects therefore has to be computed, and
`AlgebraicGeometry.Stack.obj_eq_of_quotientStackMap_commutes` is that computation: the component
of `quotientStackMap_commutes` at a point of the presentation is vertical, so its image under a
1-morphism into a category fibred in sets has equal source and target.

The 2-commutativity itself is then an equality of two 1-morphisms `[U'/R'] ⟶ 𝒮_X`, and those are
determined by their restriction along the projection `𝒮_{U'} ⟶ [U'/R']` — which is Stacks 0DUH,
`AlgebraicGeometry.Stack.restriction_injective`. Both restrictions are the 1-morphism attached to
an invariant morphism `U' ⟶ X` by Stacks 0458, and the two morphisms agree because they are the
two ways round the cartesian square `U' = X' ×_X U` of the base change.

The enlarged form is the unenlarged one composed with
`AlgebraicGeometry.Stack.liftedFibredCategoryUp`: the vertical arrows of the square are
`AlgebraicGeometry.Stack.liftedQuotientStackToBase`, which is the structure arrow of Stacks 044R
followed by that enlargement, and the bottom arrow is
`AlgebraicGeometry.Stack.liftedAssociatedMap`, whose middle factor cancels the enlargement on the
other side on the nose.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 02Y2](https://stacks.math.columbia.edu/tag/02Y2)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The two routes from the presentation of `[U/R]` to a presheaf through `[U'/R']` agree on
objects.** The 2-isomorphism of Stacks 046Q
(`AlgebraicGeometry.Stack.quotientStackMap_commutes`) has vertical components, so a 1-morphism
from `[U'/R']` into the category fibred in sets of a presheaf carries each component to a
vertical morphism, and a vertical morphism of a category fibred in sets has equal source and
target (Stacks 02Y2). -/
theorem obj_eq_of_quotientStackMap_commutes
    {G' G : GroupoidInAlgebraicSpaces C S hS B} (h : GroupoidInAlgebraicSpaces.Hom G' G)
    {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (L : quotientStack G ⥤ᵇ (fibredCategory C S hS Y).val)
    (z : (presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).obj) :
    L.obj ((pointwiseToQuotientStack G).obj ((quotientPointwiseMap h).obj z)) =
      L.obj ((quotientStackMap h).obj ((pointwiseToQuotientStack G').obj z)) := by
  have : (fibredCategory C S hS Y).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection Y).IsFiberedInSets
  have h₁ : (fibredCategory C S hS Y).val.p.IsHomLift
      (𝟙 ((presheafOfGroupoids
        (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).p.obj z))
      (L.toFunctor.map ((quotientStackMap_commutes h).hom.toNatTrans.app z)) :=
    Functor.isHomLift_map_of_comp_eq L.w _ _
  have h₂ : (fibredCategory C S hS Y).val.p.IsHomLift
      (𝟙 ((presheafOfGroupoids
        (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).p.obj z))
      (𝟙 (L.obj ((quotientStackMap h).obj ((pointwiseToQuotientStack G').obj z)))) :=
    IsHomLift.id (BasedFunctor.w_obj
      (BasedFunctor.comp (BasedFunctor.comp (pointwiseToQuotientStackBased G')
        (quotientStackMap h)) L) z)
  exact (@Functor.IsFiberedInSets.eq_of_isHomLift _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂).choose

/-- **The projection of Stacks 044R is compatible with the induced 1-morphism of Stacks 046Q.**
Let `h : (U', R') ⟶ (U, R)` be a morphism of groupoids in algebraic spaces over `B` and let
`L : [U/R] ⟶ 𝒮_Y` be a 1-morphism into the category fibred in sets of a presheaf of sets `Y` on
the big fppf site. Then restricting `[h] ≫ L` along the projection `π' : 𝒮_{U'} ⟶ [U'/R']` is the
same as restricting `L` along `π : 𝒮_U ⟶ [U/R]` after the 1-morphism of Stacks 0458 attached to
the map `U' ⟶ U` of object spaces.

The 1-morphism `L` is not removable: `[h]` is obtained from the universal property of the
stackification, so `π' ≫ [h]` is pinned down only up to the 2-isomorphism of Stacks 046Q, and it
is composing with a 1-morphism into a category fibred in sets that makes that 2-isomorphism an
identity (Stacks 02Y2). -/
theorem quotientStackProjection_comp_quotientStackMap
    {G' G : GroupoidInAlgebraicSpaces C S hS B} (h : GroupoidInAlgebraicSpaces.Hom G' G)
    {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (L : quotientStack G ⥤ᵇ (fibredCategory C S hS Y).val) :
    BasedFunctor.comp (quotientStackProjection G')
        (BasedFunctor.comp (quotientStackMap h) L) =
      BasedFunctor.comp (associatedMap C S hS h.toGroupoidHom.mapObjects).1.hom
        (BasedFunctor.comp (quotientStackProjection G) L) := by
  have : (fibredCategory C S hS Y).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection Y).IsFiberedInSets
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq
    (fibredCategory C S hS G'.objects.obj).val.p (fibredCategory C S hS Y).val.p _ _
    (BasedFunctor.w _) (BasedFunctor.w _) (fun x => ?_)
  refine (congrArg (fun w => L.obj ((quotientStackMap h).obj w))
    (quotientStackProjection_obj G' x)).trans ?_
  refine ((obj_eq_of_quotientStackMap_commutes h L
    (⟨x.base, Discrete.as x.fiber⟩ :
      (presheafOfGroupoids
        (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).obj)).symm).trans ?_
  refine (congrArg L.obj (quotientStackProjection_obj G
    (⟨x.base, Discrete.mk (h.toGroupoidHom.mapObjects.app (op x.base)
      (Discrete.as x.fiber))⟩ :
      (fibredCategory C S hS G.objects.obj).val.obj)).symm).trans ?_
  exact congrArg (fun w => L.obj ((quotientStackProjection G).obj w))
    (associatedMap_obj C S hS h.toGroupoidHom.mapObjects x).symm

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **The Stacks 0DTG square commutes on the nose.** The arrow `[U'/R'] ⟶ [U/R]` of Stacks 046Q
followed by the structure arrow `[U/R] ⟶ X` of Stacks 044R equals the structure arrow
`[U'/R'] ⟶ X'` followed by `g`.

Both sides are 1-morphisms into the category fibred in sets of `X`, so by Stacks 0DUH
(`AlgebraicGeometry.Stack.restriction_injective`) they agree as soon as their restrictions along
the projection `𝒮_{U'} ⟶ [U'/R']` agree. Those restrictions are the 1-morphisms of Stacks 0458
attached to the two composites `U' ⟶ X` around the cartesian square of the base change, and
those composites agree because the square is cartesian. -/
theorem baseChangeQuotientStackSquare_commutes :
    BasedFunctor.comp
        (invariantBaseChangeQuotientStackMap (G := G) (XtoB := XtoB) (X'toB := X'toB)
          (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))
        (quotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)) =
      BasedFunctor.comp
        (quotientStackToBase (invariantBaseChangeGroupoid G XtoB g φ hφB hφ))
        (associatedMap C S hS g.hom).1.hom := by
  refine restriction_injective (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) _ _ ?_
  have hpb :
      (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).projection.mapObjects ≫
          (invariantTargetGroupoid G XtoB φ hφB hφ).objectsToBase.hom =
        (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objectsToBase.hom ≫ g.hom :=
    congrArg (fun k : (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objects ⟶ X => k.hom)
      (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).objects_isPullback.w
  have hstep := quotientStackProjection_comp_quotientStackMap
    (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB) (X'toB := X'toB)
      (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))
    (quotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ))
  have hcomp : ∀ {F G H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (associatedMap C S hS (a ≫ b)).1.hom =
        BasedFunctor.comp (associatedMap C S hS a).1.hom (associatedMap C S hS b).1.hom :=
    fun a b => congrArg (fun k => k.hom) (associatedMap_comp C S hS a b)
  refine hstep.trans ?_
  refine (congrArg (BasedFunctor.comp _)
    (quotientStackProjection_comp_toBase (invariantTargetGroupoid G XtoB φ hφB hφ))).trans ?_
  refine (hcomp _ _).symm.trans ?_
  refine (congrArg (fun a => (associatedMap C S hS a).1.hom) hpb).trans ?_
  refine (hcomp _ _).trans ?_
  exact congrArg (fun k => BasedFunctor.comp k _)
    (quotientStackProjection_comp_toBase
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).symm

/-- **The Stacks 0DTG square commutes in the morphism universe of the ambient bicategory.** The
enlargement `AlgebraicGeometry.Stack.liftedFibredCategoryUp` of the bottom right corner is
common to both sides of `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare_commutes`, and
the enlargement of the bottom left corner cancels against the first factor of
`AlgebraicGeometry.Stack.liftedAssociatedMap` on the nose. -/
theorem baseChangeQuotientStackSquare_lifted_commutes :
    BasedFunctor.comp
        (invariantBaseChangeQuotientStackMap (G := G) (XtoB := XtoB) (X'toB := X'toB)
          (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))
        (liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)) =
      BasedFunctor.comp
        (liftedQuotientStackToBase (invariantBaseChangeGroupoid G XtoB g φ hφB hφ))
        (liftedAssociatedMap g) :=
  congrArg (fun k => BasedFunctor.comp k (liftedFibredCategoryUp X))
    (baseChangeQuotientStackSquare_commutes G XtoB X'toB g hg φ hφB hφ)

/-- **Stacks 0DTG, the displayed square.** For a groupoid in algebraic spaces `(U, R, s, t, c)`
over an algebraic space `B` over a scheme `S` of a big fppf site, an `R`-invariant morphism
`φ : U ⟶ X` of algebraic spaces over `B` and a morphism `g : X' ⟶ X` of algebraic spaces over
`B`, the square

    [U'/R'] ---> [U/R]
      |            |
      v            v
     𝒮_{X'} ---> 𝒮_X

of stacks in groupoids over the big fppf site 2-commutes, where `(U', R', s', t', c')` is the
base change of Stacks 048G. It is a 2-commutative diagram over the cospan in the sense of
Stacks 003O, with its filling 2-isomorphism an identity.

The further assertion of Stacks 0DTG, that this square is a 2-fibre product, is
`AlgebraicGeometry.Stack.baseChangeQuotientStackSquare_isTwoFibreProduct`; hence the qualifier on
the tag here. -/
@[stacks 0DTG "the displayed square and its 2-commutativity"]
noncomputable def baseChangeQuotientStackSquare :
    let J := BigFppfOver.topology C S hS
    let Q : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ),
        isStackInGroupoids_quotientStack _⟩
    let SX : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory X, isStackInGroupoids_liftedFibredCategory X⟩
    let SX' : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory X', isStackInGroupoids_liftedFibredCategory X'⟩
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom
        (liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)) : Q ⟶ SX)
      (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap g) : SX' ⟶ SX) :=
  { pt := ⟨quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ),
      isStackInGroupoids_quotientStack _⟩
    fst := Bicategory.InducedBicategory.mkHom
      (invariantBaseChangeQuotientStackMap (G := G) (XtoB := XtoB) (X'toB := X'toB)
        (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))
    snd := Bicategory.InducedBicategory.mkHom
      (liftedQuotientStackToBase (invariantBaseChangeGroupoid G XtoB g φ hφB hφ))
    iso := Bicategory.InducedBicategory.isoMk
      (eqToIso (baseChangeQuotientStackSquare_lifted_commutes G XtoB X'toB g hg φ hφB hφ)) }

end BaseChange

end AlgebraicGeometry.Stack

end
