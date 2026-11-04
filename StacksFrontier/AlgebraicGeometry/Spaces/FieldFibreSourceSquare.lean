module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpIsoTrivialGenericFibre

/-!
# The field fibre is functorial in the source, and the resulting square is cartesian

Let `f : X ⟶ Y` and `h : Y ⟶ Z` be morphisms of presheaves on the big fppf site of `S` and let
`z` be a field-valued point of `Z` with field of definition `K`.  Taking field fibres over `z`
turns the factorisation `X ⟶ Y ⟶ Z` into a morphism

```
X_z = Spec(K) ×_{z, Z} X  ⟶  Spec(K) ×_{z, Z} Y = Y_z
```

of field fibres, and the square it forms with `f` is cartesian:

```
X_z ----> Y_z
 |         |
 v         v
 X ---f--> Y
```

This is the pasting `X_z = Spec(K) ×_Z X = (Spec(K) ×_Z Y) ×_Y X = Y_z ×_Y X`.

## Main definitions

* `AlgebraicGeometry.Space.fieldFibreSourceMap` is the morphism `X_z ⟶ Y_z` of field fibres
  induced by `f`.

The field fibre of a morphism of algebraic spaces, as an object of
`AlgebraicGeometry.AlgebraicSpaces`, is the base's `AlgebraicGeometry.Space.fieldFibreSpace`
(`StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpIsoTrivialGenericFibre`).

## Main results

* `AlgebraicGeometry.Space.isPullback_fieldFibreSourceMap`: the square above is cartesian, for
  presheaves.
* `AlgebraicGeometry.Space.isPullback_fieldFibreSpace`: the same square in the category of
  algebraic spaces over the base.

## Implementation notes

`AlgebraicGeometry.Space.fieldFibre` is a plain `CategoryTheory.Limits.pullback` of presheaves,
so both statements here are pullback pasting and neither needs the algebraic-space axioms; the
presheaf-level results are stated for arbitrary presheaves on the site.  The morphism `X_z ⟶ Y_z`
is the one induced by the universal property of `Y_z`, and cartesianness of the upper square is
`CategoryTheory.IsPullback.of_bot` applied to the two defining field-fibre squares: the pasted
square is the defining square of `X_z` because the composite `X_z ⟶ Y_z ⟶ Spec(K)` is the
structure morphism of `X_z`, which is
`AlgebraicGeometry.Space.fieldFibreSourceMap_snd`.

The version for algebraic spaces is obtained by reflecting the presheaf square along the fully
faithful inclusion of the full subcategory of algebraic spaces, which is the idiom of
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Functoriality of the field fibre in the source -/

section Presheaf

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism of field fibres `X_z ⟶ Y_z` induced by a morphism `f : X ⟶ Y` over `Z`: the
field fibre of `f ≫ h` over a field-valued point `z` of `Z` maps to the field fibre of `h` over
`z`, by `f` on the first factor and the identity on `Spec(K)`. -/
noncomputable def fieldFibreSourceMap (f : X ⟶ Y) (h : Y ⟶ Z)
    (z : FieldValuedPoint B S hS Z) :
    fieldFibre B S hS (f ≫ h) z ⟶ fieldFibre B S hS h z :=
  pullback.lift (pullback.fst (f ≫ h) (yonedaEquiv.symm z.value) ≫ f)
    (pullback.snd (f ≫ h) (yonedaEquiv.symm z.value))
    (by rw [Category.assoc, pullback.condition])

/-- The morphism `X_z ⟶ Y_z` followed by the projection `Y_z ⟶ Y` is the projection
`X_z ⟶ X` followed by `f`. -/
@[simp]
theorem fieldFibreSourceMap_fst (f : X ⟶ Y) (h : Y ⟶ Z) (z : FieldValuedPoint B S hS Z) :
    fieldFibreSourceMap B S hS f h z ≫ pullback.fst h (yonedaEquiv.symm z.value) =
      pullback.fst (f ≫ h) (yonedaEquiv.symm z.value) ≫ f :=
  pullback.lift_fst _ _ _

/-- The morphism `X_z ⟶ Y_z` commutes with the structure morphisms of the two field fibres to
`Spec(K)`. -/
@[simp]
theorem fieldFibreSourceMap_snd (f : X ⟶ Y) (h : Y ⟶ Z) (z : FieldValuedPoint B S hS Z) :
    fieldFibreSourceMap B S hS f h z ≫ pullback.snd h (yonedaEquiv.symm z.value) =
      pullback.snd (f ≫ h) (yonedaEquiv.symm z.value) :=
  pullback.lift_snd _ _ _

/-- **The field fibre square of a factorisation is cartesian.**  For `f : X ⟶ Y`, `h : Y ⟶ Z`
and a field-valued point `z` of `Z`, the square

```
X_z ----> Y_z
 |         |
 v         v
 X ---f--> Y
```

whose horizontal arrows are `AlgebraicGeometry.Space.fieldFibreSourceMap` and `f` and whose
vertical arrows are the first projections of the two field fibres, is cartesian.

This is the pasting `X_z = Spec(K) ×_Z X = (Spec(K) ×_Z Y) ×_Y X = Y_z ×_Y X`: the square
obtained by pasting this one on top of the defining square of `Y_z` is the defining square of
`X_z`, because the composite `X_z ⟶ Y_z ⟶ Spec(K)` is the structure morphism of `X_z`. -/
theorem isPullback_fieldFibreSourceMap (f : X ⟶ Y) (h : Y ⟶ Z)
    (z : FieldValuedPoint B S hS Z) :
    IsPullback (pullback.fst (f ≫ h) (yonedaEquiv.symm z.value))
      (fieldFibreSourceMap B S hS f h z) f
      (pullback.fst h (yonedaEquiv.symm z.value)) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd h (yonedaEquiv.symm z.value)) (v₂₂ := h)
    (h₃₁ := yonedaEquiv.symm z.value) ?_ ?_ (IsPullback.of_hasPullback _ _)
  · rw [fieldFibreSourceMap_snd]
    exact IsPullback.of_hasPullback _ _
  · exact (fieldFibreSourceMap_fst B S hS f h z).symm

end Presheaf

/-! ### The field fibre of a morphism of algebraic spaces -/

section Spaces

variable {X Y Z : AlgebraicSpaces B S hS}

/-- A field-valued point of an algebraic space, read as a morphism `Spec(K) ⟶ Y` of algebraic
spaces over the base, where `Spec(K)` is `AlgebraicGeometry.Space.schemeSpace` of the object of
the site the point is a section over.  Its underlying morphism of presheaves is
`AlgebraicGeometry.Space.fieldMorphism`. -/
noncomputable def fieldPointSpaceHom {Y : AlgebraicSpaces B S hS}
    (z : FieldValuedPoint B S hS Y.1) : schemeSpace (z.siteObject B S hS Y.1) ⟶ Y :=
  ObjectProperty.homMk (yonedaEquiv.symm z.value)

/-- **The defining square of the field fibre of a morphism of algebraic spaces is cartesian.**
For `f : X ⟶ Y` and a field-valued point `z` of `Y`, the square with corners `X_z`, `X`,
`Spec(K)` and `Y` is cartesian in the category of algebraic spaces over the base. -/
theorem isPullback_fieldFibreSpace_snd (f : X ⟶ Y) (z : FieldValuedPoint B S hS Y.1) :
    IsPullback
      (ObjectProperty.homMk (pullback.fst f.hom (yonedaEquiv.symm z.value)) :
          fieldFibreSpace f z ⟶ X)
      (ObjectProperty.homMk (pullback.snd f.hom (yonedaEquiv.symm z.value)) :
          fieldFibreSpace f z ⟶ schemeSpace (z.siteObject B S hS Y.1))
      f (fieldPointSpaceHom B S hS z) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ pullback.condition)
    (IsPullback.of_hasPullback _ _)

/-- **The field fibre square of a factorisation of morphisms of algebraic spaces is
cartesian.**  For `f : X ⟶ Y`, `h : Y ⟶ Z` and a field-valued point `z` of `Z`, the square

```
X_z ----> Y_z
 |         |
 v         v
 X ---f--> Y
```

of algebraic spaces over the base is cartesian.  This is
`AlgebraicGeometry.Space.isPullback_fieldFibreSourceMap` reflected along the fully faithful
inclusion of the algebraic spaces into the presheaves on the site. -/
theorem isPullback_fieldFibreSpace (f : X ⟶ Y) (h : Y ⟶ Z)
    (z : FieldValuedPoint B S hS Z.1) :
    IsPullback
      (ObjectProperty.homMk
        (pullback.fst (f.hom ≫ h.hom) (yonedaEquiv.symm z.value)) :
          fieldFibreSpace (f ≫ h) z ⟶ X)
      (ObjectProperty.homMk (fieldFibreSourceMap B S hS f.hom h.hom z) :
          fieldFibreSpace (f ≫ h) z ⟶ fieldFibreSpace h z)
      f
      (ObjectProperty.homMk (pullback.fst h.hom (yonedaEquiv.symm z.value)) :
          fieldFibreSpace h z ⟶ Y) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (fieldFibreSourceMap_fst B S hS f.hom h.hom z).symm)
    (isPullback_fieldFibreSourceMap B S hS f.hom h.hom z)

end Spaces

end AlgebraicGeometry.Space

end
