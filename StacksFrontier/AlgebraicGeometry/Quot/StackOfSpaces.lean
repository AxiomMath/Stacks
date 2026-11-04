module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies

/-!
# The stack of algebraic spaces (Stacks 0D1D)

Stacks 0D1D sets up the two categories that the rest of its section studies: the category
`Spaces'_{ft}` of finite-type families of algebraic spaces over varying base schemes, with its
projection `p'_{ft}` to the big fppf site, and the *full subcategory*

```text
  Spaces'_{fp, flat, proper}  ⊂  Spaces'_{ft}
```

consisting of those families `X ⟶ T` whose structure morphism is of finite presentation, flat
and proper, with `p'_{fp, flat, proper}` the restriction of `p'_{ft}` to it. Both categories are
taken with cartesian morphisms only. The base of the two projections is the big fppf site of a
scheme `S`; taking `S = Spec(ℤ)` gives the setting of Stacks 0D1D.

The two categories and the two projections are
`AlgebraicGeometry.CartesianFiniteTypeSpaces`, `AlgebraicGeometry.CartesianProperFlatSpaces`,
`AlgebraicGeometry.cartesianFiniteTypeProjection` and
`AlgebraicGeometry.cartesianProperFlatProjection`. This file constructs the inclusion functor,
shows that it is fully faithful, and shows that the second projection is the restriction of the
first along it.

## Main definitions

* `CategoryTheory.ObjectProperty.wideιOfLE`: for `h : P ≤ Q` and a multiplicative morphism
  property `W`, the inclusion of the wide subcategory on `W` of `P.FullSubcategory` into the wide
  subcategory on `W` of `Q.FullSubcategory`.
* `AlgebraicGeometry.cartesianProperFlatInclusion`: **Stacks 0D1D**, the inclusion
  `Spaces'_{fp, flat, proper} ⊂ Spaces'_{ft}`.

## Main results

* `CategoryTheory.ObjectProperty.fullyFaithfulWideιOfLE`: the inclusion `wideιOfLE` is fully
  faithful.
* `CategoryTheory.ObjectProperty.wideιOfLE_comp_inclusion`: the inclusion `wideιOfLE` commutes
  with the forgetful functors to the ambient category.
* `AlgebraicGeometry.isProperFlatSpace_le_isFiniteTypeSpace`: a family that is of finite
  presentation, flat and proper is of finite type.
* `AlgebraicGeometry.fullyFaithfulCartesianProperFlatInclusion`: **Stacks 0D1D**, the inclusion
  is fully faithful, i.e. `Spaces'_{fp, flat, proper}` is a *full* subcategory of
  `Spaces'_{ft}`.
* `AlgebraicGeometry.cartesianProperFlatInclusion_comp_cartesianFiniteTypeProjection`:
  **Stacks 0D1D**, `p'_{fp, flat, proper}` is the restriction of `p'_{ft}`.

## References

* [Stacks Project, Tag 0D1D](https://stacks.math.columbia.edu/tag/0D1D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {P Q : ObjectProperty C}

/-- For properties of objects `P ≤ Q` of a category `C` and a multiplicative morphism property
`W` on `C`, the inclusion of the wide subcategory on `W` of `P.FullSubcategory` into the wide
subcategory on `W` of `Q.FullSubcategory`. -/
def wideιOfLE (h : P ≤ Q) :
    WideSubcategory (W.inverseImage P.ι) ⥤ WideSubcategory (W.inverseImage Q.ι) where
  obj X := ⟨(ιOfLE h).obj X.obj⟩
  map f := ⟨(ιOfLE h).map f.hom, f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying object of `C` is unchanged by `CategoryTheory.ObjectProperty.wideιOfLE`. -/
theorem wideιOfLE_obj_obj (h : P ≤ Q) (X : WideSubcategory (W.inverseImage P.ι)) :
    ((wideιOfLE W h).obj X).obj.obj = X.obj.obj :=
  rfl

/-- The underlying morphism of `C` is unchanged by
`CategoryTheory.ObjectProperty.wideιOfLE`. -/
theorem wideιOfLE_map_hom (h : P ≤ Q) {X Y : WideSubcategory (W.inverseImage P.ι)} (f : X ⟶ Y) :
    ((wideιOfLE W h).map f).hom.hom = f.hom.hom :=
  rfl

/-- `CategoryTheory.ObjectProperty.wideιOfLE` is fully faithful: a morphism of the larger wide
subcategory between objects of the smaller one is a morphism of the smaller one, with no further
condition. -/
def fullyFaithfulWideιOfLE (h : P ≤ Q) : (wideιOfLE W h).FullyFaithful where
  preimage f := ⟨homMk f.hom.hom, f.property⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- `CategoryTheory.ObjectProperty.wideιOfLE` is full. -/
instance full_wideιOfLE (h : P ≤ Q) : (wideιOfLE W h).Full :=
  (fullyFaithfulWideιOfLE W h).full

/-- `CategoryTheory.ObjectProperty.wideιOfLE` is faithful. -/
instance faithful_wideιOfLE (h : P ≤ Q) : (wideιOfLE W h).Faithful :=
  (fullyFaithfulWideιOfLE W h).faithful

/-- `CategoryTheory.ObjectProperty.wideιOfLE` is compatible with the two forgetful functors down
to `C`, on the nose. -/
theorem wideιOfLE_comp_inclusion (h : P ≤ Q) :
    wideιOfLE W h ⋙ wideSubcategoryInclusion (W.inverseImage Q.ι) ⋙ Q.ι =
      wideSubcategoryInclusion (W.inverseImage P.ι) ⋙ P.ι := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A family of algebraic spaces whose structure morphism is of finite presentation, flat and
proper is in particular of finite type. -/
theorem isProperFlatSpace_le_isFiniteTypeSpace :
    isProperFlatSpace B S hS ≤ isFiniteTypeSpace B S hS :=
  fun _ h ↦ h.2.2.2.1

/-- **Stacks 0D1D.** The inclusion
`Spaces'_{fp, flat, proper} ⊂ Spaces'_{ft}` of the families of algebraic spaces that are of
finite presentation, flat and proper over their base scheme into all the finite-type families,
both taken with cartesian morphisms only. -/
@[stacks 0D1D "the subcategory of finitely presented, flat and proper families"]
abbrev cartesianProperFlatInclusion :
    CartesianProperFlatSpaces B S hS ⥤ CartesianFiniteTypeSpaces B S hS :=
  ObjectProperty.wideιOfLE (stronglyCartesianOver (spacesProjection B S hS))
    (isProperFlatSpace_le_isFiniteTypeSpace B S hS)

/-- **Stacks 0D1D.** The subcategory `Spaces'_{fp, flat, proper}` of `Spaces'_{ft}` is *full*:
a cartesian morphism of finite-type families whose source and target are of finite presentation,
flat and proper is a morphism of `Spaces'_{fp, flat, proper}`, with no further condition. -/
@[stacks 0D1D "the subcategory is full"]
def fullyFaithfulCartesianProperFlatInclusion :
    (cartesianProperFlatInclusion B S hS).FullyFaithful :=
  ObjectProperty.fullyFaithfulWideιOfLE (stronglyCartesianOver (spacesProjection B S hS))
    (isProperFlatSpace_le_isFiniteTypeSpace B S hS)

/-- **Stacks 0D1D.** The projection `p'_{fp, flat, proper}` is the restriction of the projection
`p'_{ft}` to the subcategory `Spaces'_{fp, flat, proper}`. -/
@[stacks 0D1D "the projection of the subcategory is the restriction of the projection"]
theorem cartesianProperFlatInclusion_comp_cartesianFiniteTypeProjection :
    cartesianProperFlatInclusion B S hS ⋙ cartesianFiniteTypeProjection B S hS =
      cartesianProperFlatProjection B S hS := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

end AlgebraicGeometry

/-! ### The categories and projections of Stacks 0D1D -/

add_to_stacks 0D1D "the category of finite-type families"
  AlgebraicGeometry.CartesianFiniteTypeSpaces

add_to_stacks 0D1D "the projection to the big fppf site"
  AlgebraicGeometry.cartesianFiniteTypeProjection

add_to_stacks 0D1D "the finitely presented, flat and proper condition"
  AlgebraicGeometry.isProperFlatSpace

add_to_stacks 0D1D "the category of finitely presented, flat and proper families"
  AlgebraicGeometry.CartesianProperFlatSpaces

add_to_stacks 0D1D "the projection of the subcategory to the big fppf site"
  AlgebraicGeometry.cartesianProperFlatProjection

end
