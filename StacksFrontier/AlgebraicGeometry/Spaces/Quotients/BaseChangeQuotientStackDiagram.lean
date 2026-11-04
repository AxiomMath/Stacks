module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack

/-!
# The diagram of quotient stacks attached to an invariant base change

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `φ : U ⟶ X` be an `R`-invariant morphism of algebraic spaces
over `B`, and let `g : X' ⟶ X` be a morphism of algebraic spaces over `B`. Reading `G` as a
groupoid over `X` (Stacks 048G, `AlgebraicGeometry.GroupoidInAlgebraicSpaces.overInvariantTarget`)
and pulling it back along `g` (Stacks 0DTA, `AlgebraicGeometry.Space.baseChange`) produces the
base change `(U', R', s', t', c')` of Stacks 048G. Stacks 0DTG displays the square

    [U'/R'] ---> [U/R]
      |            |
      v            v
     𝒮_{X'} ---> 𝒮_X

of stacks in groupoids over the big fppf site and asserts that it is a 2-fibre product. This file
builds the three arrows of that square, which the source refers to Groupoids in Spaces, Section
044O for; the 2-fibre-product assertion of Stacks 0DTG is **not** proved here, and no declaration
below carries that tag.

The two vertical arrows are the structure arrow of Stacks 044R for a groupoid over its own base,
pushed into the morphism universe of the ambient bicategory. The horizontal arrow is the induced
1-morphism of Stacks 046Q for the morphism of groupoids `(U', R') ⟶ (U, R)` given by the two
pullback projections; that morphism lives over `B`, which is why a groupoid over `X` has first to
be read as a groupoid over `B`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.overBase`: a groupoid over `X`, read as a groupoid
  over a base `B` that `X` lies over.
* `AlgebraicGeometry.Stack.liftedQuotientStackToBase`: the structure arrow `[U/R] ⟶ 𝒮_B` of
  Stacks 044R, with its target in the enlarged morphism universe.
* `AlgebraicGeometry.Stack.invariantTargetGroupoid` and
  `AlgebraicGeometry.Stack.invariantBaseChangeGroupoid`: the groupoid over `X` and its base change
  `(U', R', s', t', c')` to `X'`.
* `AlgebraicGeometry.Stack.invariantBaseChangeGroupoidHom`: the morphism of groupoids over `B`
  from the base change to the original groupoid.
* `AlgebraicGeometry.Stack.invariantBaseChangeQuotientStackMapOverBase` and
  `AlgebraicGeometry.Stack.invariantBaseChangeQuotientStackMap`: the horizontal arrow
  `[U'/R'] ⟶ [U/R]` of the Stacks 0DTG diagram, stated first over the common base `B` and then at
  the two original bases.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.overBase_toGroupoidInFunctors` and
  `AlgebraicGeometry.Stack.quotientStack_overBase`: changing the base a groupoid is read over
  alters neither its underlying groupoid in presheaves nor its quotient stack. This is what lets
  the arrow of Stacks 046Q, which needs a common base, be read as an arrow between the quotient
  stacks of two groupoids over different bases.

## Implementation notes

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overBase` changes only the two structure morphisms to
the base; every other field, and in particular the composition on the chosen fibre product of
Stacks 02X2 and the pointwise groupoid law, is carried across unchanged. The quotient stack of
Stacks 044Q is built from the underlying groupoid in presheaves alone, so it is unchanged on the
nose, which is `AlgebraicGeometry.Stack.quotientStack_overBase`.

The two compatibilities a morphism of groupoids over `B` has to satisfy are read off the two
cartesian squares recorded by `AlgebraicGeometry.Space.BaseChange`, rather than off its explicit
pullback projections: the equations wanted are exactly the commutativity of those squares,
postcomposed with the structure morphism `X ⟶ B`.

## References

* [Stacks Project, Tag 044O](https://stacks.math.columbia.edu/tag/044O)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 0DTA](https://stacks.math.columbia.edu/tag/0DTA)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {B : AlgebraicSpaces C S hS}

namespace GroupoidInAlgebraicSpaces

/-- **A groupoid over `X`, read as a groupoid over a base `B` that `X` lies over.** The object and
arrow spaces, the source, the target and the composition are unchanged; the two structure
morphisms to the base are composed with `X ⟶ B`. -/
noncomputable def overBase {X : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (XtoB : X ⟶ B) :
    GroupoidInAlgebraicSpaces C S hS B where
  objects := H.objects
  arrows := H.arrows
  objectsToBase := H.objectsToBase ≫ XtoB
  arrowsToBase := H.arrowsToBase ≫ XtoB
  source := H.source
  target := H.target
  source_over := by rw [← Category.assoc, H.source_over]
  target_over := by rw [← Category.assoc, H.target_over]
  comp := H.comp
  comp_over := by rw [← Category.assoc, H.comp_over, Category.assoc]
  pointwiseGroupoid := H.pointwiseGroupoid

/-- Reading a groupoid over a larger base leaves its underlying groupoid in presheaves
unchanged. -/
theorem overBase_toGroupoidInFunctors {X : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (XtoB : X ⟶ B) :
    (overBase H XtoB).toGroupoidInFunctors = H.toGroupoidInFunctors := rfl

end GroupoidInAlgebraicSpaces

namespace Stack

/-- **The quotient stack does not see which base a groupoid is read over.** The quotient stack of
Stacks 044Q is the stackification of the pointwise groupoid fibration of the underlying groupoid in
presheaves, and that is unchanged by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overBase`. -/
theorem quotientStack_overBase {X : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (XtoB : X ⟶ B) :
    quotientStack (GroupoidInAlgebraicSpaces.overBase H XtoB) = quotientStack H := rfl

/-- **The structure arrow `[U/R] ⟶ 𝒮_B` of Stacks 044R, in the enlarged morphism universe.** It is
`AlgebraicGeometry.Stack.quotientStackToBase` followed by the canonical 1-morphism into the
universe-enlarged fibred category of the base, which is the form in which the two vertical arrows
of the Stacks 0DTG diagram inhabit the bicategory of stacks in groupoids. -/
noncomputable def liftedQuotientStackToBase (H : GroupoidInAlgebraicSpaces C S hS B) :
    quotientStack H ⥤ᵇ liftedFibredCategory B :=
  BasedFunctor.comp (quotientStackToBase H) (liftedFibredCategoryUp B)

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **`(U, R, s, t, c)` read as a groupoid over the invariant target `X`** (Stacks 048G). -/
noncomputable abbrev invariantTargetGroupoid : GroupoidInAlgebraicSpaces C S hS X :=
  (GroupoidInAlgebraicSpaces.overInvariantTarget G XtoB φ hφB hφ).val

/-- **The base change `(U', R', s', t', c')` of Stacks 048G**: the groupoid over `X` of
`AlgebraicGeometry.Stack.invariantTargetGroupoid`, pulled back along `g : X' ⟶ X` by the base
change of Stacks 0DTA. -/
noncomputable abbrev invariantBaseChangeGroupoid : GroupoidInAlgebraicSpaces C S hS X' :=
  (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).groupoid

/-- **The morphism of groupoids over `B` from the base change to the original groupoid.** Its maps
on objects and on arrows are the two pullback projections `U' ⟶ U` and `R' ⟶ R`; that they are
morphisms over `B` is the commutativity of the two cartesian squares of the base change,
postcomposed with the structure morphism `X ⟶ B`. -/
noncomputable def invariantBaseChangeGroupoidHom :
    GroupoidInAlgebraicSpaces.Hom
      (GroupoidInAlgebraicSpaces.overBase
        (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) X'toB)
      (GroupoidInAlgebraicSpaces.overBase
        (invariantTargetGroupoid G XtoB φ hφB hφ) XtoB) where
  toGroupoidHom := (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).projection
  mapObjects_over := by
    have hw' :
        (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).projection.mapObjects ≫
            (invariantTargetGroupoid G XtoB φ hφB hφ).objectsToBase.hom =
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objectsToBase.hom ≫ g.hom :=
      congrArg (fun k : (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objects ⟶ X => k.hom)
        (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).objects_isPullback.w
    change (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).projection.mapObjects ≫
        (invariantTargetGroupoid G XtoB φ hφB hφ).objectsToBase.hom ≫ XtoB.hom =
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).objectsToBase.hom ≫ X'toB.hom
    rw [← hg]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ XtoB.hom) hw').trans (Category.assoc _ _ _))
  mapArrows_over := by
    have hw' :
        (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).projection.mapArrows ≫
            (invariantTargetGroupoid G XtoB φ hφB hφ).arrowsToBase.hom =
          (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).arrowsToBase.hom ≫ g.hom :=
      congrArg (fun k : (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).arrows ⟶ X => k.hom)
        (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).arrows_isPullback.w
    change (Space.baseChange (invariantTargetGroupoid G XtoB φ hφB hφ) g).projection.mapArrows ≫
        (invariantTargetGroupoid G XtoB φ hφB hφ).arrowsToBase.hom ≫ XtoB.hom =
      (invariantBaseChangeGroupoid G XtoB g φ hφB hφ).arrowsToBase.hom ≫ X'toB.hom
    rw [← hg]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ XtoB.hom) hw').trans (Category.assoc _ _ _))

/-- **The induced 1-morphism of Stacks 046Q for
`AlgebraicGeometry.Stack.invariantBaseChangeGroupoidHom`**, stated between the quotient stacks of
the two groupoids as read over `B`.

`AlgebraicGeometry.Stack.invariantBaseChangeQuotientStackMap` is the same 1-morphism with its type
written at the two original bases. Naming this intermediate step is what keeps that reading cheap:
asking for it in one declaration makes the elaborator unfold the base change inside the quotient
stack while the two spellings are still being compared, and the comparison does not terminate. -/
noncomputable def invariantBaseChangeQuotientStackMapOverBase :
    quotientStack (GroupoidInAlgebraicSpaces.overBase
        (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) X'toB) ⥤ᵇ
      quotientStack (GroupoidInAlgebraicSpaces.overBase
        (invariantTargetGroupoid G XtoB φ hφB hφ) XtoB) :=
  quotientStackMap (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB) (X'toB := X'toB)
    (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))

/-- **The horizontal arrow `[U'/R'] ⟶ [U/R]` of the Stacks 0DTG diagram.** It is the induced
1-morphism of Stacks 046Q for
`AlgebraicGeometry.Stack.invariantBaseChangeGroupoidHom`, read through
`AlgebraicGeometry.Stack.quotientStack_overBase`. -/
noncomputable def invariantBaseChangeQuotientStackMap :
    quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ) ⥤ᵇ
      quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ) :=
  invariantBaseChangeQuotientStackMapOverBase (G := G) (XtoB := XtoB) (X'toB := X'toB)
    (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)

end Stack

end AlgebraicGeometry

end
