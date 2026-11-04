module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackCell
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialitySquareTerminality

/-!
# The comparison 1-morphism of the square of Section 78.21

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over
a scheme `S` of a big fppf site, written `f : U ⟶ U'` on object spaces, and let
`(U'', R'', s'', t'', c'')` be the groupoid of Section 78.21 attached to it. The square

```
[U''/R''] ---[g]---> [U/R]
    |                  |
    |                 [φ]
    v                  v
  𝒮_{U'} ----π'----> [U'/R']
```

2-commutes by `AlgebraicGeometry.Stack.auxQuotientStackSquare`. This file records it as a
2-commutative square of stacks in groupoids over the big fppf site, builds the comparison
1-morphism

```
[U''/R''] ⟶ [U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}
```

into the 2-fibre product of Stacks 0040, and reduces the assertion that the square is a 2-fibre
product to the comparison 1-morphism being fully faithful and locally essentially surjective on
fibres.

## Main definitions

* `AlgebraicGeometry.Stack.auxSquareCell`: the filler of the square, as a natural isomorphism of
  the underlying functors.
* `AlgebraicGeometry.Stack.auxQuotientSquare`: the square of Section 78.21, as a 2-commutative
  square in the 2-category of stacks in groupoids over the big fppf site.
* `AlgebraicGeometry.Stack.auxQuotientComparison`: the comparison 1-morphism.

## Main results

* `AlgebraicGeometry.Stack.auxQuotientComparison_comp` and
  `AlgebraicGeometry.Stack.isFibredOneMorphism_auxQuotientComparison`: the comparison 1-morphism
  is strictly over the site, hence a 1-morphism of fibred categories over it.
* `AlgebraicGeometry.Stack.auxQuotientComparison_obj_x`,
  `AlgebraicGeometry.Stack.auxQuotientComparison_obj_y` and
  `AlgebraicGeometry.Stack.auxQuotientComparison_obj_iso`: its value on an object, which is the
  triple consisting of the image in `[U/R]`, the image in `𝒮_{U'}`, and the component of the
  filler.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare_of`: the square is a 2-fibre
  product as soon as the comparison 1-morphism is full, faithful and locally essentially
  surjective on fibres.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
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

/-! ### The filler of the square -/

/-- **The filler of the square of Section 78.21**, as a natural isomorphism between the
underlying functors of the two composites `[U''/R''] ⟶ [U/R] ⟶ [U'/R']` and
`[U''/R''] ⟶ 𝒮_{U'} ⟶ [U'/R']`, the object-space side being the universe-enlarged one. -/
noncomputable def auxSquareCell (φ : Hom G G') :
    (auxQuotientToSource φ).toFunctor ⋙ (quotientStackMap φ).toFunctor ≅
      (auxLiftedQuotientStackToObjects φ).toFunctor ⋙
        (liftedQuotientStackProjection G').toFunctor :=
  (BasedNatTrans.forgetful (quotientStack (auxGroupoid φ)) (quotientStack G')).mapIso
    (auxQuotientStackSquare φ).symm

/-- **Every component of the filler lies over an identity of the site**, so it is a 2-morphism
of the 2-category of categories over the big fppf site. -/
theorem auxSquareCell_isHomLift (φ : Hom G G') (x : (quotientStack (auxGroupoid φ)).obj) :
    (quotientStack G').p.IsHomLift (𝟙 ((quotientStack (auxGroupoid φ)).p.obj x))
      ((auxSquareCell φ).hom.app x) :=
  (auxQuotientStackSquare φ).inv.isHomLift' x

/-- **The filler, at an object coming from the presentation of `[U''/R'']`, is the comparison
built on that presentation**, which at a point `(u, r')` of `U''` over a test object is the arrow
`r'` of the evaluated groupoid of `G'`. -/
theorem auxSquareCell_hom_app_toQuotientStack (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxSquareCell φ).hom.app ((toQuotientStack (auxGroupoid φ)).obj X) =
      (auxRestrictedSquare φ).inv.toNatTrans.app X :=
  auxQuotientStackSquare_inv_app_toQuotientStack φ X

/-- **The inverse of the filler, at an object coming from the presentation of `[U''/R'']`.** -/
theorem auxSquareCell_inv_app_toQuotientStack (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxSquareCell φ).inv.app ((toQuotientStack (auxGroupoid φ)).obj X) =
      (auxRestrictedSquare φ).hom.toNatTrans.app X :=
  auxQuotientStackSquare_hom_app_toQuotientStack φ X

/-! ### The square -/

/-- **The square of Section 78.21**, as a 2-commutative square of stacks in groupoids over the
big fppf site: the quotient stack of the auxiliary groupoid, with the 1-morphism `[g]` induced by
the projection `(U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)` and the descent of the morphism
`U'' ⟶ U'`, against the cospan formed by the induced 1-morphism `[φ]` of Stacks 046Q and the
projection `π'` of Stacks 044R. -/
noncomputable def auxQuotientSquare (φ : Hom G G') :
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom (quotientStackMap φ) :
        quotientStackInGroupoids G ⟶ quotientStackInGroupoids G')
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G') :
        liftedFibredCategoryInGroupoids G'.objects ⟶ quotientStackInGroupoids G') where
  pt := quotientStackInGroupoids (auxGroupoid φ)
  fst := Bicategory.InducedBicategory.mkHom (auxQuotientToSource φ)
  snd := Bicategory.InducedBicategory.mkHom (auxLiftedQuotientStackToObjects φ)
  iso := Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (auxSquareCell φ) (auxSquareCell_isHomLift φ))

/-! ### The comparison 1-morphism -/

/-- **The comparison 1-morphism `[U''/R''] ⟶ [U/R] ×_{[U'/R']} 𝒮_{U'}` of Stacks 04Y4**: the
mediating 1-morphism of Stacks 0040 for the square of Section 78.21. On an object `x` of
`[U''/R'']` over a test object `T` it is the triple consisting of the image of `x` in `[U/R]`,
the image of `x` in `𝒮_{U'}` and the component of the filler at `x`. -/
noncomputable def auxQuotientComparison (φ : Hom G G') :
    (quotientStack (auxGroupoid φ)).obj ⥤ functorialityTwoFibreProductObj φ :=
  TwoFibreProductOver.lift (quotientStack G).p (liftedFibredCategory G'.objects).p
    (quotientStack G').p (quotientStackMap φ).toFunctor
    (liftedQuotientStackProjection G').toFunctor
    (quotientStack (auxGroupoid φ)).p
    (auxQuotientToSource φ).toFunctor (auxLiftedQuotientStackToObjects φ).toFunctor
    (auxQuotientToSource φ).w (auxLiftedQuotientStackToObjects φ).w
    (auxSquareCell φ) (auxSquareCell_isHomLift φ)

/-- The `[U/R]`-component of the value of the comparison 1-morphism. -/
@[simp]
theorem auxQuotientComparison_obj_x (φ : Hom G G') (x : (quotientStack (auxGroupoid φ)).obj) :
    ((auxQuotientComparison φ).obj x).x = (auxQuotientToSource φ).obj x := rfl

/-- The `𝒮_{U'}`-component of the value of the comparison 1-morphism. -/
@[simp]
theorem auxQuotientComparison_obj_y (φ : Hom G G') (x : (quotientStack (auxGroupoid φ)).obj) :
    ((auxQuotientComparison φ).obj x).y = (auxLiftedQuotientStackToObjects φ).obj x := rfl

/-- The comparison isomorphism of the value of the comparison 1-morphism is the component of the
filler. -/
@[simp]
theorem auxQuotientComparison_obj_iso (φ : Hom G G') (x : (quotientStack (auxGroupoid φ)).obj) :
    ((auxQuotientComparison φ).obj x).iso = (auxSquareCell φ).app x := rfl

/-- The `[U/R]`-component of the image of a morphism under the comparison 1-morphism. -/
@[simp]
theorem auxQuotientComparison_map_a (φ : Hom G G')
    {x y : (quotientStack (auxGroupoid φ)).obj} (m : x ⟶ y) :
    ((auxQuotientComparison φ).map m).a = (auxQuotientToSource φ).map m := rfl

/-- The `𝒮_{U'}`-component of the image of a morphism under the comparison 1-morphism. -/
@[simp]
theorem auxQuotientComparison_map_b (φ : Hom G G')
    {x y : (quotientStack (auxGroupoid φ)).obj} (m : x ⟶ y) :
    ((auxQuotientComparison φ).map m).b = (auxLiftedQuotientStackToObjects φ).map m := rfl

/-- **The comparison 1-morphism is strictly over the big fppf site.** -/
theorem auxQuotientComparison_comp (φ : Hom G G') :
    auxQuotientComparison φ ⋙ functorialityTwoFibreProduct φ =
      (quotientStack (auxGroupoid φ)).p :=
  TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _

/-- **The comparison 1-morphism is a 1-morphism of fibred categories over the big fppf site.** -/
theorem isFibredOneMorphism_auxQuotientComparison (φ : Hom G G') :
    Functor.IsFibredOneMorphism (quotientStack (auxGroupoid φ)).p
      (functorialityTwoFibreProduct φ) (auxQuotientComparison φ) :=
  (isFiberedInGroupoids_functorialityTwoFibreProduct φ).isFibredOneMorphism
    (auxQuotientComparison_comp φ)

/-! ### Reduction of the 2-fibre product property to the comparison 1-morphism -/

/-- **The square of Section 78.21 is a 2-fibre product once its comparison 1-morphism is fully
faithful and locally essentially surjective on fibres.** -/
noncomputable def isTwoFibreProduct_auxQuotientSquare_of (φ : Hom G G')
    (hfull : (auxQuotientComparison φ).Full) (hfaith : (auxQuotientComparison φ).Faithful)
    (hloc : Functor.LocallyEssSurjOnFibers (isFibered_functorialityTwoFibreProduct φ)
      (isFibredOneMorphism_auxQuotientComparison φ).comp_eq (BigFppfOver.topology C S hS)) :
    Bicategory.IsTwoFibreProduct (auxQuotientSquare φ) := by
  refine Nonempty.some ?_
  let h₀ : quotientStackInGroupoids G ⟶ quotientStackInGroupoids G' :=
    Bicategory.InducedBicategory.mkHom (quotientStackMap φ)
  let s₀ : liftedFibredCategoryInGroupoids G'.objects ⟶ quotientStackInGroupoids G' :=
    Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G')
  let hprod := isStackInGroupoids_functorialityTwoFibreProduct φ
  let hP := relativeProductIsTerminal h₀ s₀ hprod
  let k := relativeProductPreHom h₀ s₀ hprod (auxQuotientSquare φ)
  have := hfull
  have := hfaith
  have : (quotientStack (auxGroupoid φ)).p.IsFibered :=
    (isStack_quotientStack (auxGroupoid φ)).isFibered
  obtain ⟨hequiv⟩ := isEquivalenceOver_functorialityTwoFibreProduct φ
    (isStack_quotientStack (auxGroupoid φ)).hasEffectiveDescent
    (isFibredOneMorphism_auxQuotientComparison φ) hloc
  have hce : (auxQuotientComparison φ).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (auxQuotientComparison φ) hequiv.inv
      hequiv.unitIso.symm hequiv.counitIso).isEquivalence_functor
  obtain ⟨K, hK, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (quotientStack (auxGroupoid φ)).p (functorialityTwoFibreProduct φ)
    (isFiberedInGroupoids_quotientStack (auxGroupoid φ))
    (isFiberedInGroupoids_functorialityTwoFibreProduct φ)
    (auxQuotientComparison φ) (auxQuotientComparison_comp φ) hce
  exact ⟨Bicategory.isTwoFibreProduct_of_section hP
    (k.ofSection (Bicategory.InducedBicategory.mkHom ⟨K, hK⟩)
      (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso ε hε)))
    k.hom (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso η hη))⟩

end AlgebraicGeometry.Stack

end
