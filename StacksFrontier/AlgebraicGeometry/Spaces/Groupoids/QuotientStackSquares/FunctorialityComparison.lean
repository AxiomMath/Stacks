module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliarySpaces
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityProjectionCell
public import
StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityTwoFibreProduct

/-!
# The square of Stacks 04ZN and its comparison 1-morphism

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, written `f : U ⟶ U'` on object
spaces. Stacks 046Q gives the induced 1-morphism `[φ] : [U/R] ⟶ [U'/R']`, Stacks 044R the
projections `π : 𝒮_U ⟶ [U/R]` and `π' : 𝒮_{U'} ⟶ [U'/R']`, and Stacks 0458 the 1-morphism
`𝒮_f : 𝒮_U ⟶ 𝒮_{U'}`. This file assembles the square

```
𝒮_U ----π----> [U/R]
 |              |
𝒮_f            [φ]
 v              v
𝒮_{U'} --π'--> [U'/R']
```

of Stacks 04ZN as a 2-commutative square of stacks in groupoids over the big fppf site, and the
comparison 1-morphism

```
c : 𝒮_U ⟶ [U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}
```

into the 2-fibre product `AlgebraicGeometry.Stack.functorialityTwoFibreProduct` of Stacks 0040.
Stacks 04ZN asserts that the square is a 2-fibre product when the square formed by the two
**source** maps of the groupoids is cartesian. This file shows, with no hypothesis on `φ`, that
`c` is strictly over the site and faithful.

## Main definitions

* `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted`: the 2-isomorphism
  `π ≫ [φ] ≅ 𝒮_f ≫ π'` between the un-enlarged object-space fibrations.
* `AlgebraicGeometry.Stack.functorialityProjectionCellLifted`: the same 2-isomorphism for the
  universe-enlarged object-space fibrations, which is the filler the square needs.
* `AlgebraicGeometry.Stack.functorialitySquare`: the square of Stacks 04ZN, as a 2-commutative
  square of stacks in groupoids over the big fppf site.
* `AlgebraicGeometry.Stack.functorialityComparison`: the comparison 1-morphism `c`.

## Main results

* `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted_hom_app` and
  `AlgebraicGeometry.Stack.functorialityProjectionCellLifted_hom_app`: the components of the two
  2-isomorphisms.
* `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted_isHomLift` and
  `AlgebraicGeometry.Stack.functorialityProjectionCellLifted_isHomLift`: every component lies
  over an identity of the site.
* `AlgebraicGeometry.Stack.functorialityComparison_comp`: `c` is strictly over the site.
* `AlgebraicGeometry.Stack.isFibredOneMorphism_functorialityComparison`: `c` is a 1-morphism of
  fibred categories over the site.
* `AlgebraicGeometry.Stack.functorialityComparison_faithful`: `c` is faithful.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### The filler of the square -/

/-- **The 2-isomorphism `π ≫ [φ] ≅ 𝒮_f ≫ π'` filling the square of Stacks 04ZN**, between the
un-enlarged object-space fibrations. -/
noncomputable def functorialityProjectionCellUnlifted (φ : Hom G G') :
    (quotientStackProjection G).toFunctor ⋙ (quotientStackMap φ).toFunctor ≅
      (objectSpaceMap φ).toFunctor ⋙ (quotientStackProjection G').toFunctor :=
  NatIso.ofComponents
    (fun x ↦ (quotientStackProjectionCell φ).app x ≪≫
      eqToIso (Functor.congr_obj (pointwiseObjectInclusion_comp_quotientPointwiseMap_comp φ) x))
    (by
      intro x y g
      dsimp only [Iso.trans_hom, Iso.app_hom, eqToIso.hom]
      rw [← Category.assoc, (quotientStackProjectionCell φ).hom.naturality g, Category.assoc,
        Functor.congr_hom (pointwiseObjectInclusion_comp_quotientPointwiseMap_comp φ) g]
      simp)

/-- The component of `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted` at a point of
the object space: the component of Stacks 046Q followed by the `eqToHom` identifying the two
spellings of its target. -/
theorem functorialityProjectionCellUnlifted_hom_app (φ : Hom G G')
    (x : (fibredCategory C S hS G.objects.obj).val.obj) :
    (functorialityProjectionCellUnlifted φ).hom.app x =
      (quotientStackProjectionCell φ).hom.app x ≫
        eqToHom (Functor.congr_obj
          (pointwiseObjectInclusion_comp_quotientPointwiseMap_comp φ) x) :=
  rfl

/-- **Every component of `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted` lies over
an identity of the site.** -/
theorem functorialityProjectionCellUnlifted_isHomLift (φ : Hom G G')
    (x : (fibredCategory C S hS G.objects.obj).val.obj) :
    (quotientStack G').p.IsHomLift
      (𝟙 ((fibredCategory C S hS G.objects.obj).val.p.obj x))
      ((functorialityProjectionCellUnlifted φ).hom.app x) := by
  rw [functorialityProjectionCellUnlifted_hom_app]
  have := quotientStackProjectionCell_isHomLift φ x
  have : (quotientStack G').p.IsHomLift
      (𝟙 ((fibredCategory C S hS G.objects.obj).val.p.obj x))
      (eqToHom (Functor.congr_obj
        (pointwiseObjectInclusion_comp_quotientPointwiseMap_comp φ) x)) :=
    IsHomLift.eqToHom_domain_lift_id _ (IsHomLift.codomain_eq (quotientStack G').p
      (𝟙 ((fibredCategory C S hS G.objects.obj).val.p.obj x))
      ((quotientStackProjectionCell φ).hom.app x))
  infer_instance

/-- **The 2-isomorphism filling the square of Stacks 04ZN**, between the universe-enlarged
object-space fibrations: the un-enlarged 2-isomorphism whiskered with the comparison with the
enlargement. -/
noncomputable def functorialityProjectionCellLifted (φ : Hom G G') :
    (liftedQuotientStackProjection G).toFunctor ⋙ (quotientStackMap φ).toFunctor ≅
      (liftedAssociatedMap φ.objectsMap).toFunctor ⋙
        (liftedQuotientStackProjection G').toFunctor :=
  CategoryTheory.Functor.isoWhiskerLeft (liftedFibredCategoryDown G.objects).toFunctor
    (functorialityProjectionCellUnlifted φ)

/-- The component of `AlgebraicGeometry.Stack.functorialityProjectionCellLifted` is the component
of `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted` at the same point of the object
space, read through the comparison with the enlargement. -/
theorem functorialityProjectionCellLifted_hom_app (φ : Hom G G')
    (x : (liftedFibredCategory G.objects).obj) :
    (functorialityProjectionCellLifted φ).hom.app x =
      (functorialityProjectionCellUnlifted φ).hom.app
        ((liftedFibredCategoryDown G.objects).obj x) :=
  rfl

/-- **Every component of `AlgebraicGeometry.Stack.functorialityProjectionCellLifted` lies over an
identity of the site.** -/
theorem functorialityProjectionCellLifted_isHomLift (φ : Hom G G')
    (x : (liftedFibredCategory G.objects).obj) :
    (quotientStack G').p.IsHomLift
      (𝟙 ((liftedFibredCategory G.objects).p.obj x))
      ((functorialityProjectionCellLifted φ).hom.app x) :=
  functorialityProjectionCellUnlifted_isHomLift φ ((liftedFibredCategoryDown G.objects).obj x)

/-! ### The square -/

/-- **The square of Stacks 04ZN**: the projection of Stacks 044R against the induced 1-morphism
of Stacks 046Q, as a 2-commutative square of stacks in groupoids over the big fppf site. Its
filler is `AlgebraicGeometry.Stack.functorialityProjectionCellLifted`. -/
noncomputable def functorialitySquare (φ : Hom G G') :
    let J := BigFppfOver.topology C S hS
    let X : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack G, isStackInGroupoids_quotientStack G⟩
    let Y : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack G', isStackInGroupoids_quotientStack G'⟩
    let V : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory G'.objects, isStackInGroupoids_liftedFibredCategory G'.objects⟩
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom (quotientStackMap φ) : X ⟶ Y)
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G') : V ⟶ Y) := by
  let J := BigFppfOver.topology C S hS
  let W : StackInGroupoids (BigFppfOver C S hS) J :=
    ⟨liftedFibredCategory G.objects, isStackInGroupoids_liftedFibredCategory G.objects⟩
  exact {
    pt := W
    fst := Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G)
    snd := Bicategory.InducedBicategory.mkHom (liftedAssociatedMap φ.objectsMap)
    iso := Bicategory.InducedBicategory.isoMk
      (BasedNatIso.mkNatIso (functorialityProjectionCellLifted φ)
        (functorialityProjectionCellLifted_isHomLift φ)) }

/-! ### The comparison 1-morphism -/

/-- **The comparison 1-morphism `c : 𝒮_U ⟶ [U/R] ×_{[U'/R']} 𝒮_{U'}` of Stacks 04ZN**: the
mediating 1-morphism of Stacks 0040 for the square
`AlgebraicGeometry.Stack.functorialitySquare`. On a point `u` of the object space over a test
object `T` it is the triple consisting of the object `π(u)` of `[U/R]`, the point `f(u)` of
`U'` and the component of the filler at `u`. -/
noncomputable def functorialityComparison (φ : Hom G G') :
    (liftedFibredCategory G.objects).obj ⥤ functorialityTwoFibreProductObj φ :=
  TwoFibreProductOver.lift (quotientStack G).p (liftedFibredCategory G'.objects).p
    (quotientStack G').p (quotientStackMap φ).toFunctor
    (liftedQuotientStackProjection G').toFunctor
    (liftedFibredCategory G.objects).p
    (liftedQuotientStackProjection G).toFunctor
    (liftedAssociatedMap φ.objectsMap).toFunctor
    (liftedQuotientStackProjection G).w (liftedAssociatedMap φ.objectsMap).w
    (functorialityProjectionCellLifted φ) (functorialityProjectionCellLifted_isHomLift φ)

/-- **The comparison 1-morphism is strictly over the big fppf site.** -/
theorem functorialityComparison_comp (φ : Hom G G') :
    functorialityComparison φ ⋙ functorialityTwoFibreProduct φ =
      (liftedFibredCategory G.objects).p :=
  TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _

/-- **The comparison 1-morphism is a 1-morphism of fibred categories over the big fppf site.** -/
theorem isFibredOneMorphism_functorialityComparison (φ : Hom G G') :
    Functor.IsFibredOneMorphism (liftedFibredCategory G.objects).p
      (functorialityTwoFibreProduct φ) (functorialityComparison φ) :=
  (isFiberedInGroupoids_functorialityTwoFibreProduct φ).isFibredOneMorphism
    (functorialityComparison_comp φ)

/-- **The comparison 1-morphism is faithful.** -/
theorem functorialityComparison_faithful (φ : Hom G G') :
    (functorialityComparison φ).Faithful :=
  have := liftedFibredCategory_faithful G.objects
  Functor.Faithful.of_comp_eq (functorialityComparison_comp φ)

end AlgebraicGeometry.Stack

end
