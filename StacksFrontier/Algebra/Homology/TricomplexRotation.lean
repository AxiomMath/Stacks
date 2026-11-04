module

public import StacksCore.Algebra.Homology.HomologicalTricomplex
public import StacksFrontier.Algebra.Homology.MapTotalComplex

/-!
# Rotating the indices of a tricomplex

A tricomplex `HomologicalComplex₃ C c₁ c₂ c₃` is a complex of bicomplexes, so its three indices
are not interchangeable as data even though the three differentials play symmetric roles. This
file provides the cyclic rotation which moves the *third* index of a tricomplex to the front,

```
HomologicalComplex₃ C c₂ c₃ c₁ ⥤ HomologicalComplex₃ C c₁ c₂ c₃,
```

obtained by flipping the inner bicomplexes and then flipping the outer two directions. No signs
are involved: `HomologicalComplex₂.flip` exchanges two directions of a bicomplex without any,
all sign conventions being carried by the total complex shapes instead.

The rotation is what makes the following construction available. Let `G : C ⥤ HomologicalComplex
D c₁` be an additive functor with values in complexes and let `L : HomologicalComplex₂ C c₂ c₃`
be a bicomplex. Applying `G` to each term of `L` produces a tricomplex whose new index comes
*last*; rotating it gives `HomologicalComplex₃.ofComplexValuedFunctor G L`, the tricomplex

```
(i₁, i₂, i₃) ↦ (G (L^{i₂, i₃}))_{i₁}
```

with the new index first. Its slices and its columns are identified with the bicomplexes one
expects, by definitional equalities: the slice at `i₃` is `G` applied to the row `i₃` of `L` and
flipped, and the column at `i₁` is the bicomplex obtained by applying the ordinary functor
`G ⋙ HomologicalComplex.eval D c₁ i₁` to `L`.

## Main definitions

* `HomologicalComplex₃.rotateFunctor`: the cyclic rotation of the three indices.
* `HomologicalComplex₃.ofComplexValuedFunctor`: the tricomplex `(G (L^{i₂, i₃}))_{i₁}`.

## Main results

* `HomologicalComplex₃.ofComplexValuedFunctor_X`,
  `HomologicalComplex₃.ofComplexValuedFunctor_X'` and
  `HomologicalComplex₃.ofComplexValuedFunctor_d'`: the columns, the slices and the third
  differential of that tricomplex.

## Implementation notes

The two flips happen at different nesting levels: the first is `HomologicalComplex₂.flipFunctor`
applied degreewise through `Functor.mapHomologicalComplex`, and the second is
`HomologicalComplex₂.flipFunctor` for the category `HomologicalComplex D c₃` of complexes. The
identifications of the columns and the slices are therefore `rfl`, and are stated as equalities
rather than as isomorphisms so that no transport is needed downstream.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex₂

variable (C : Type*) [Category* C] [Preadditive C] {I₁ I₂ : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- Exchanging the two directions of a bicomplex is an additive functor. -/
instance flipFunctor_additive : (flipFunctor C c₁ c₂).Additive where
  map_add := by intros; ext; rfl

end HomologicalComplex₂

namespace HomologicalComplex₃

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {I₁ I₂ I₃ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

variable (C c₁ c₂ c₃) in
/-- **The cyclic rotation of the indices of a tricomplex**, moving the third index to the
front: the term of `rotateFunctor.obj W` in position `(i₁, i₂, i₃)` is the term of `W` in
position `(i₂, i₃, i₁)`. It is the composite of a flip of the inner bicomplexes with a flip of
the outer two directions, and introduces no signs. -/
def rotateFunctor :
    HomologicalComplex₃ C c₂ c₃ c₁ ⥤ HomologicalComplex₃ C c₁ c₂ c₃ :=
  (HomologicalComplex₂.flipFunctor C c₃ c₁).mapHomologicalComplex c₂ ⋙
    HomologicalComplex₂.flipFunctor (HomologicalComplex C c₃) c₂ c₁

/-- The tricomplex obtained from `W : HomologicalComplex₃ C c₂ c₃ c₁` by moving its third index
to the front. -/
abbrev rotate (W : HomologicalComplex₃ C c₂ c₃ c₁) : HomologicalComplex₃ C c₁ c₂ c₃ :=
  (rotateFunctor C c₁ c₂ c₃).obj W

variable (W : HomologicalComplex₃ C c₂ c₃ c₁)

/-- The terms of the rotation of a tricomplex are the terms of the tricomplex, with the indices
read in the rotated order. -/
lemma rotate_X_X_X (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    (((rotate W).X i₁).X i₂).X i₃ = ((W.X i₂).X i₃).X i₁ :=
  rfl

/-- The slice of the rotation of `W` at `i₃` is the column of `W` at `i₃`, flipped. -/
lemma rotate_X' (i₃ : I₃) :
    (rotate W).X' i₃ =
      (HomologicalComplex₂.flipFunctor C c₂ c₁).obj
        ((HomologicalComplex₂.flipFunctor (HomologicalComplex C c₁) c₂ c₃).obj W |>.X i₃) :=
  rfl

section

variable (G : C ⥤ HomologicalComplex D c₁) [G.Additive] (L : HomologicalComplex₂ C c₂ c₃)

/-- **The tricomplex `(i₁, i₂, i₃) ↦ (G (L^{i₂, i₃}))_{i₁}`** attached to a bicomplex `L` and an
additive functor `G` with values in complexes: apply `G` to each term of `L` and move the new
index to the front. -/
abbrev ofComplexValuedFunctor : HomologicalComplex₃ D c₁ c₂ c₃ :=
  rotate (((G.mapHomologicalComplex c₃).mapHomologicalComplex c₂).obj L)

/-- The term of `ofComplexValuedFunctor G L` in position `(i₁, i₂, i₃)`. -/
lemma ofComplexValuedFunctor_X_X_X (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    (((ofComplexValuedFunctor G L).X i₁).X i₂).X i₃ = (G.obj ((L.X i₂).X i₃)).X i₁ :=
  rfl

/-- **The column of `ofComplexValuedFunctor G L` at `i₁`** is the bicomplex obtained from `L` by
applying the ordinary functor `G ⋙ HomologicalComplex.eval D c₁ i₁` to each term. -/
lemma ofComplexValuedFunctor_X (i₁ : I₁) :
    (ofComplexValuedFunctor G L).X i₁ =
      HomologicalComplex₂.TotalMap.mapBicomplex (G ⋙ HomologicalComplex.eval D c₁ i₁) L :=
  rfl

/-- **The slice of `ofComplexValuedFunctor G L` at `i₃`** is `G` applied termwise to the row of
`L` at `i₃`, with the new index moved to the front. -/
lemma ofComplexValuedFunctor_X' (i₃ : I₃) :
    (ofComplexValuedFunctor G L).X' i₃ =
      HomologicalComplex₂.flip ((G.mapHomologicalComplex c₂).obj (L.flip.X i₃)) :=
  rfl

/-- **The third differential of `ofComplexValuedFunctor G L`** is `G` applied termwise to the
differential of the rows of `L`. -/
lemma ofComplexValuedFunctor_d' (i₃ i₃' : I₃) :
    (ofComplexValuedFunctor G L).d' i₃ i₃' =
      (HomologicalComplex₂.flipFunctor D c₂ c₁).map
        ((G.mapHomologicalComplex c₂).map (L.flip.d i₃ i₃')) :=
  rfl

end

end HomologicalComplex₃

end
