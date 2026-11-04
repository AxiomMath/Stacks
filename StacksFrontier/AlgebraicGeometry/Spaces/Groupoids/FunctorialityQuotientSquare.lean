module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliaryGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The square of Section 78.21 and its comparison with the 2-fibre product

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over
a scheme `S` of a big fppf site, written `f : U ⟶ U'` on objects, and let
`(U'', R'', s'', t'', c'')` be the auxiliary groupoid of Section 78.21, built in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityAuxiliaryGroupoid.lean`. Stacks 04Y4
compares its quotient stack with the 2-fibre product

```
S_{U'} ×_{π, [U'/R'], [f]} [U/R]
```

of the canonical projection of Stacks 044R with the induced 1-morphism of Stacks 046Q. This file
builds the two legs of the square out of `[U''/R'']`, the 2-fibre product itself, and the
comparison 1-morphism over the site determined by a 2-cell filling the square.

## Main definitions

* `AlgebraicGeometry.Stack.auxQuotientToTargetObjects`: the leg `[U''/R''] ⟶ S_{U'}`, the descent
  of the morphism `U'' ⟶ U'` of Section 78.21 to the quotient stack.
* `AlgebraicGeometry.Stack.auxQuotientToSource`: the leg `[U''/R''] ⟶ [U/R]`, the 1-morphism of
  Stacks 046Q induced by the morphism `g` of Section 78.21.
* `AlgebraicGeometry.Stack.auxTwoFibreProduct`: the 2-fibre product
  `S_{U'} ×_{[U'/R']} [U/R]` as a category over the site.
* `AlgebraicGeometry.Stack.auxComparison`: the comparison 1-morphism
  `[U''/R''] ⟶ S_{U'} ×_{[U'/R']} [U/R]` determined by a vertical 2-cell filling the square.
* `AlgebraicGeometry.Stack.auxPointwiseFst` and `AlgebraicGeometry.Stack.auxPointwiseSnd`: the two
  legs read on the pointwise groupoid presentations, which is where the 2-cell is concrete.
* `AlgebraicGeometry.Stack.auxPointwiseCellHom`: the component of that 2-cell at a point of `U''`,
  the arrow `r'` of the evaluated groupoid of `G'`.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_auxTwoFibreProduct`: the 2-fibre product is fibred
  in groupoids, by Stacks 0041.
* `AlgebraicGeometry.Stack.auxComparison_comp`: the comparison 1-morphism is strictly over the
  site, so it is a 1-morphism of the 2-category of categories over the site.
* `AlgebraicGeometry.Stack.auxPointwiseFst_obj_fiber` and
  `AlgebraicGeometry.Stack.auxPointwiseSnd_obj_fiber`: the two pointwise legs send a point
  `(u, r')` of `U''` over a test object to the points `s'(r')` and `f(u)` of `U'`, which are the
  source and the target of the arrow `r'` of the evaluated groupoid of `G'`. This is the
  identification the proof of Stacks 04Y4 turns on.

## Implementation notes

The leg `[U''/R''] ⟶ S_{U'}` is the descent of an invariant morphism,
`AlgebraicGeometry.Stack.quotientStackOfInvariant`, applied to the morphism `U'' ⟶ U'` of
Section 78.21 and to `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxToTargetObjects_invariant`;
that invariance is exactly `s'(r') = s'(c'(f(r), r'))`, the source of a composite being the source
of the arrow applied first.

The 2-fibre product is the one of Stacks 0040, `CategoryTheory.TwoFibreProductOver`, whose four
hom universes are independent. The projection `S_{U'} ⟶ [U'/R']` has its morphisms in the site's
own universe, while the two quotient stacks have theirs one universe above, so the square is
stated with `AlgebraicGeometry.Stack.fibredCategory` itself and no universe enlargement of the
space side is needed.

The comparison 1-morphism is `CategoryTheory.TwoFibreProductOver.lift`, so its two projections are
the two legs on the nose and the compatibility with the 2-cell `ψ` of the 2-fibre product is
`CategoryTheory.TwoFibreProductOver.lift_whiskerRight_psi`. It takes the 2-cell filling the square
as an argument, and so is the mediating 1-morphism of *every* filler. The canonical filler is
`AlgebraicGeometry.Stack.auxQuotientStackSquare` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityQuotientStackCell.lean`, built from
the arrow `r'` of the evaluated groupoid of `G'` running from `s'(r')` to `f(u)`;
`AlgebraicGeometry.Stack.auxPointwiseCellHom` below is that arrow read as a morphism of the
pointwise groupoid fibration, the identification of its two ends being the two object computations
above. The square assembled from that filler, and the comparison 1-morphism it determines, are
`AlgebraicGeometry.Stack.auxQuotientSquare` and
`AlgebraicGeometry.Stack.auxQuotientComparison` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityQuotientStackComparison.lean`, where
the object-space side of the cospan is the universe-enlarged fibred category of `U'`, as in the
square of Stacks 04ZN, so that the three categories of the cospan share a hom universe.
Stacks 04Y4 itself — that the square identifies `[U''/R'']` with the 2-fibre product — is
`AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityQuotientStackTwoFibreProduct.lean`.

Opening the naturality square of that 2-cell needs the two components of a composite of arrows of
a pointwise groupoid fibration, which `AlgebraicGeometry.Stack.pointwiseComp_base` and
`AlgebraicGeometry.Stack.pointwiseComp_fiber` supply; the corresponding lemmas of
`CategoryTheory.Pseudofunctor.CoGrothendieck` are stated for the `CategoryStruct` instance and do
not rewrite here, as those two docstrings record.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### The two legs of the square -/

/-- **The leg `[U''/R''] ⟶ S_{U'}` of the square of Section 78.21**: the descent to the quotient
stack of the morphism `U'' ⟶ U'` sending `(u, r')` to `s'(r')`, which is invariant under the
auxiliary groupoid. -/
noncomputable def auxQuotientToTargetObjects (φ : Hom G G') :
    quotientStack (auxGroupoid φ) ⥤ᵇ (fibredCategory C S hS G'.objects.obj).val :=
  quotientStackOfInvariant (auxGroupoid φ) (auxToTargetObjects φ)
    (auxToTargetObjects_invariant φ)

/-- **The leg `[U''/R''] ⟶ [U/R]` of the square of Section 78.21**: the 1-morphism of Stacks 046Q
induced by the morphism `g : (U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)` of two first
projections. -/
noncomputable def auxQuotientToSource (φ : Hom G G') :
    quotientStack (auxGroupoid φ) ⥤ᵇ quotientStack G :=
  quotientStackMap (auxHom φ)

/-! ### The 2-fibre product -/

/-- **The 2-fibre product `S_{U'} ×_{π, [U'/R'], [f]} [U/R]`** of Stacks 04Y4, as a category over
the big fppf site: the 2-fibre product of Stacks 0040 of the canonical projection of Stacks 044R
and the induced 1-morphism of Stacks 046Q. -/
noncomputable abbrev auxTwoFibreProductObj (φ : Hom G G') : Type (u + 1) :=
  TwoFibreProductOver (fibredCategory C S hS G'.objects.obj).val.p (quotientStack G).p
    (quotientStack G').p (quotientStackProjection G').toFunctor (quotientStackMap φ).toFunctor

/-- The structure functor of the 2-fibre product of Stacks 04Y4. -/
noncomputable abbrev auxTwoFibreProduct (φ : Hom G G') :
    auxTwoFibreProductObj φ ⥤ BigFppfOver C S hS :=
  TwoFibreProductOver.structureFunctor _ _ _ _ _

/-- **The 2-fibre product of Stacks 04Y4 is fibred in groupoids**, by Stacks 0041: the fibred
category of an algebraic space and the two quotient stacks are, and the projection and the induced
1-morphism are strictly over the site. -/
theorem isFiberedInGroupoids_auxTwoFibreProduct (φ : Hom G G') :
    (auxTwoFibreProduct φ).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (fibredCategory C S hS G'.objects.obj).property
    (isFiberedInGroupoids_quotientStack G) (isFiberedInGroupoids_quotientStack G')
    (quotientStackProjection G').w (quotientStackMap φ).w

/-! ### The comparison 1-morphism -/

/-- **The comparison 1-morphism `[U''/R''] ⟶ S_{U'} ×_{[U'/R']} [U/R]` of Stacks 04Y4**,
determined by a vertical 2-cell `t` filling the square of Section 78.21: it sends an object `x` of
`[U''/R'']` over a test object `T` to the quadruple consisting of `T`, the image of `x` in
`S_{U'}`, the image of `x` in `[U/R]`, and the component of `t` at `x`. -/
noncomputable def auxComparison (φ : Hom G G')
    (t : (auxQuotientToTargetObjects φ).toFunctor ⋙ (quotientStackProjection G').toFunctor ≅
      (auxQuotientToSource φ).toFunctor ⋙ (quotientStackMap φ).toFunctor)
    (ht : ∀ x, (quotientStack G').p.IsHomLift
      (𝟙 ((quotientStack (auxGroupoid φ)).p.obj x)) (t.hom.app x)) :
    (quotientStack (auxGroupoid φ)).obj ⥤ auxTwoFibreProductObj φ :=
  TwoFibreProductOver.lift _ _ _ _ _ _ (auxQuotientToTargetObjects φ).toFunctor
    (auxQuotientToSource φ).toFunctor (auxQuotientToTargetObjects φ).w
    (auxQuotientToSource φ).w t ht

/-- **The comparison 1-morphism is strictly over the big fppf site**, so it is a 1-morphism of the
2-category of categories over the site. -/
theorem auxComparison_comp (φ : Hom G G')
    (t : (auxQuotientToTargetObjects φ).toFunctor ⋙ (quotientStackProjection G').toFunctor ≅
      (auxQuotientToSource φ).toFunctor ⋙ (quotientStackMap φ).toFunctor)
    (ht : ∀ x, (quotientStack G').p.IsHomLift
      (𝟙 ((quotientStack (auxGroupoid φ)).p.obj x)) (t.hom.app x)) :
    auxComparison φ t ht ⋙ auxTwoFibreProduct φ = (quotientStack (auxGroupoid φ)).p :=
  TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _

/-- **The first projection of the comparison 1-morphism is the first leg**, on the nose. -/
theorem auxComparison_comp_fst (φ : Hom G G')
    (t : (auxQuotientToTargetObjects φ).toFunctor ⋙ (quotientStackProjection G').toFunctor ≅
      (auxQuotientToSource φ).toFunctor ⋙ (quotientStackMap φ).toFunctor)
    (ht : ∀ x, (quotientStack G').p.IsHomLift
      (𝟙 ((quotientStack (auxGroupoid φ)).p.obj x)) (t.hom.app x)) :
    auxComparison φ t ht ⋙
        TwoFibreProductOver.fst (fibredCategory C S hS G'.objects.obj).val.p
          (quotientStack G).p (quotientStack G').p (quotientStackProjection G').toFunctor
          (quotientStackMap φ).toFunctor =
      (auxQuotientToTargetObjects φ).toFunctor :=
  rfl

/-- **The second projection of the comparison 1-morphism is the second leg**, on the nose. -/
theorem auxComparison_comp_snd (φ : Hom G G')
    (t : (auxQuotientToTargetObjects φ).toFunctor ⋙ (quotientStackProjection G').toFunctor ≅
      (auxQuotientToSource φ).toFunctor ⋙ (quotientStackMap φ).toFunctor)
    (ht : ∀ x, (quotientStack G').p.IsHomLift
      (𝟙 ((quotientStack (auxGroupoid φ)).p.obj x)) (t.hom.app x)) :
    auxComparison φ t ht ⋙
        TwoFibreProductOver.snd (fibredCategory C S hS G'.objects.obj).val.p
          (quotientStack G).p (quotientStack G').p (quotientStackProjection G').toFunctor
          (quotientStackMap φ).toFunctor =
      (auxQuotientToSource φ).toFunctor :=
  rfl

/-! ### The two legs on the pointwise presentations -/

/-- The first leg read on the pointwise groupoid presentations: a point `(u, r')` of `U''` over a
test object goes to the point `s'(r')` of `U'`, included in the evaluated groupoid of `G'`. -/
noncomputable def auxPointwiseFst (φ : Hom G G') :
    (presheafOfGroupoids
        (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj ⥤
      (presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).obj :=
  (pointwiseOfInvariant (auxGroupoid φ) (auxToTargetObjects φ).hom
      (hom_comp_eq_of_invariant (auxGroupoid φ) (auxToTargetObjects_invariant φ))).toFunctor ⋙
    pointwiseObjectInclusion G'

/-- The second leg read on the pointwise groupoid presentations: a point `(u, r')` of `U''` over a
test object goes to the point `f(u)` of `U'`. -/
noncomputable def auxPointwiseSnd (φ : Hom G G') :
    (presheafOfGroupoids
        (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj ⥤
      (presheafOfGroupoids (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).obj :=
  (quotientPointwiseMap (auxHom φ)).toFunctor ⋙ (quotientPointwiseMap φ).toFunctor

/-- The two pointwise legs agree on test objects. -/
@[simp]
theorem auxPointwiseFst_obj_base (φ : Hom G G')
    (P : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    ((auxPointwiseFst φ).obj P).base = P.base := rfl

/-- The two pointwise legs agree on test objects. -/
@[simp]
theorem auxPointwiseSnd_obj_base (φ : Hom G G')
    (P : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    ((auxPointwiseSnd φ).obj P).base = P.base := rfl

/-- **The first pointwise leg sends `(u, r')` to `s'(r')`.** -/
theorem auxPointwiseFst_obj_fiber (φ : Hom G G')
    (P : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    ((auxPointwiseFst φ).obj P).fiber =
      G'.source.hom.app (Opposite.op P.base)
        ((auxObjectsSnd φ).hom.app (Opposite.op P.base) P.fiber) := rfl

/-- **The second pointwise leg sends `(u, r')` to `f(u)`.** -/
theorem auxPointwiseSnd_obj_fiber (φ : Hom G G')
    (P : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    ((auxPointwiseSnd φ).obj P).fiber =
      φ.toGroupoidHom.mapObjects.app (Opposite.op P.base)
        ((auxObjectsFst φ).hom.app (Opposite.op P.base) P.fiber) := rfl

/-! ### The component of the 2-cell -/

section Cell

/- The presenting pseudofunctor of the pointwise groupoid fibration is reached through
`CategoryTheory.Functor.toPseudofunctor'` and the groupoid-to-category inclusion, none of which
the `implicit` transparency level unfolds; naming that chain is what lets the identity transport
of the pseudofunctor reduce. -/
attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc BasedCategory.ofFunctor
  Grpd.forgetToCat Grpd.of

/-- **The test object of a composite of arrows of a pointwise groupoid fibration.** The arrows of
the category attached to a presheaf of groupoids are pairs of a morphism of test objects and a
morphism of the fibre over the source, and the first component of a composite is the composite.

`CategoryTheory.Pseudofunctor.CoGrothendieck.categoryStruct_comp_base` is the same equation for
the raw Grothendieck construction. It does not apply here: it is stated for the
`CategoryStruct` instance, whereas the arrows of `AlgebraicGeometry.Stack.presheafOfGroupoids` are
composed by the `Category` instance of `CategoryTheory.Pseudofunctor.CoGrothendieck`, and the
chain `AlgebraicGeometry.Stack.presheafOfGroupoids` to that instance is not type-correct at the
`implicit` transparency level that `rw` and `simp` re-check against. -/
theorem pointwiseComp_base {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Grpd.{u, u}}
    {X Y Z : (presheafOfGroupoids F).obj} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- **The fibre component of a composite of arrows of a pointwise groupoid fibration**: the
fibre component of `f`, then the pullback along the test morphism of `f` of the fibre component
of `g`, then the comparison of the two pullbacks with the pullback along the composite.

This is `CategoryTheory.Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber` transported to
`AlgebraicGeometry.Stack.presheafOfGroupoids`, for the reason recorded on
`AlgebraicGeometry.Stack.pointwiseComp_base`: the generic lemma is stated for the `CategoryStruct`
instance and does not rewrite an arrow of a pointwise groupoid fibration, so the naturality square
of a 2-cell between two legs read on the pointwise presentations cannot be opened with it. -/
theorem pointwiseComp_fiber {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Grpd.{u, u}}
    {X Y Z : (presheafOfGroupoids F).obj} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫
        ((F ⋙ Grpd.forgetToCat).toPseudofunctor'.map f.base.op.toLoc).toFunctor.map g.fiber ≫
          ((F ⋙ Grpd.forgetToCat).toPseudofunctor'.mapComp g.base.op.toLoc
            f.base.op.toLoc).inv.toNatTrans.app Z.fiber := rfl

/-- The presenting pseudofunctor of the pointwise groupoid fibration of a groupoid in algebraic
spaces. -/
noncomputable abbrev presentingPseudofunctor (G' : GroupoidInAlgebraicSpaces C S hS B) :
    Pseudofunctor (LocallyDiscrete (BigFppfOver C S hS)ᵒᵖ) Cat.{u, u} :=
  (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor'

/-- **The component of the 2-cell of Stacks 04Y4 at a point `(u, r')` of `U''`**: the arrow `r'`
of the evaluated groupoid of `G'`, which goes from `s'(r')` — the value of the first pointwise leg
— to `f(u)` — the value of the second — the target of `r'` being `f(u)` by the defining square of
`U''`. It is vertical: its base component is an identity. -/
noncomputable def auxPointwiseCellHom (φ : Hom G G')
    (P : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    (auxPointwiseFst φ).obj P ⟶ (auxPointwiseSnd φ).obj P where
  base := 𝟙 P.base
  fiber := (auxIndex φ (Opposite.op P.base) P.fiber).arr ≫
    ((presentingPseudofunctor G').mapId ⟨Opposite.op P.base⟩).inv.toNatTrans.app
      ((auxPointwiseSnd φ).obj P).fiber

/-- The component of the 2-cell lies over an identity of the site. -/
@[simp]
theorem auxPointwiseCellHom_base (φ : Hom G G')
    (P : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) :
    (auxPointwiseCellHom φ P).base = 𝟙 P.base := rfl

/-- **The base components of the two sides of the naturality square of the 2-cell agree.** Both
pointwise legs act on test objects as the identity, so each side lies over the base morphism of
the given arrow. -/
theorem auxPointwiseCellHom_naturality_base (φ : Hom G G')
    {P Q : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj} (m : P ⟶ Q) :
    (((auxPointwiseFst φ).map m ≫ auxPointwiseCellHom φ Q) :
        (auxPointwiseFst φ).obj P ⟶ (auxPointwiseSnd φ).obj Q).base =
      ((auxPointwiseCellHom φ P ≫ (auxPointwiseSnd φ).map m) :
        (auxPointwiseFst φ).obj P ⟶ (auxPointwiseSnd φ).obj Q).base :=
  (Category.comp_id _).trans (Category.id_comp _).symm

end Cell

end AlgebraicGeometry.Stack

end
