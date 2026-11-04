module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi

/-!
# The degree-zero base change map of a square of algebraic spaces, characterized

Let

```
X' --g'--> X
|f'         |f
v           v
Y' --g-->  Y
```

be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`.
`AlgebraicGeometry.Space.moduleBaseChangeMap` is the degree-zero base change map
`g^*f_* ⟶ f'_*(g')^*` of the square, defined as the mate, under the two adjunctions of
**Stacks 03LU** for the two *horizontal* morphisms, of the comparison of the two composite direct
images around the square.  This file identifies it with the mate under the two adjunctions of the
*vertical* morphisms of the comparison of the two composite inverse images, and derives from that
identification the adjoint characterization the source gives the map by:  under `(f')^* ⊣ f'_*`
it is the inverse image along `g'` of the counit of `f^* ⊣ f_*`, transported across the
comparison of the two composite inverse images.

The invertibility of this map for a cartesian square with `g` flat and `f` quasi-compact and
quasi-separated is the degree-zero clause of **Stacks 073K**, part (1), which this development
does not prove;  what is established here is the characterization of the map whose invertibility
that clause asserts.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_modulePullbackCompIso_inv` and
  `AlgebraicGeometry.Space.conjugateEquiv_modulePullbackCompIso_hom`: the comparison of direct
  images along a composite of **Stacks 03LU** is the conjugate of the comparison of inverse
  images, in both directions.
* `AlgebraicGeometry.Space.conjugateEquiv_modulePullbackSquareComparison_inv`: the same for the
  two comparisons attached to a commutative square.  Its third ingredient, that the transport of
  inverse images along an equality of morphisms is the mate of the transport of direct images, is
  `AlgebraicGeometry.Space.conjugateEquiv_eqToHom_modulePullback`.
* `AlgebraicGeometry.Space.moduleBaseChangeMap_eq_mateEquiv`: **the base change map is the mate,
  under the two adjunctions of the vertical morphisms, of the comparison of the two composite
  inverse images.**  The two mates agree by `CategoryTheory.iterated_mateEquiv_conjugateEquiv`,
  which applies because all four functors of the square of inverse images are left adjoints.
* `AlgebraicGeometry.Space.moduleBaseChangeMap_adjoint_split` and
  `AlgebraicGeometry.Space.moduleBaseChangeMap_adjoint_split'`: **the adjoint characterization**,
  with the comparison read as a single morphism and written out as its three factors.
* `AlgebraicGeometry.Space.pasteBaseComm`: two commutative squares stacked along the base paste
  to a commutative rectangle.

## What is not proved

**The pasting law is not proved here.**  The degree-zero shape of **Stacks 0E47** — that the base
change map of a rectangle obtained by stacking two squares along the base is the composite of the
two base change maps, read through the comparisons of **Stacks 03LU** for the two composite
horizontal legs — is exactly the instantiation of the two lemmas
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal` and
`Stacks.Cohomology.DerivedBaseChangePasting.baseChangeMate_horizontal` at the inverse and direct
images of `𝒪`-modules on algebraic spaces, and every input those two lemmas ask for is available:
the associativity coherence `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, the two
compatibilities `AlgebraicGeometry.Space.modulePullbackCompIso_congr_left` and
`AlgebraicGeometry.Space.modulePullbackCompIso_congr_right` of the comparison with an equality of
either of its two morphisms, and the adjoint characterization above.  The instantiation elaborates
and is rejected by the kernel, which runs out of its budget on it:  the comparison of iterated
inverse images around a rectangle is a twenty-fold application at the module categories of six
algebraic spaces, and checking it reaches into
`AlgebraicGeometry.Space.modulePullback`.  Splitting the argument into the abstract lemma plus a
single instantiation, which is what those two lemmas exist for, is not by itself enough here.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans)

universe u

namespace AlgebraicGeometry.Space

/-- The transport along an equality of functors, componentwise, is the canonical identification
of the two functors.  The componentwise form is a projection out of an explicit structure and so
reduces, which the canonical identification does not while the equality is a variable. -/
theorem eqToHom_eq_transportNatTrans {A C : Type*} [Category A] [Category C] {F G : A ⥤ C}
    (e : F = G) : eqToHom e = transportNatTrans e := by
  subst e
  ext M
  simp [transportNatTrans]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Conjugate

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The comparison of direct images along a composite is the conjugate of the comparison of
inverse images.**  The inverse image comparison of **Stacks 03LU** is the comparison of left
adjoints induced by the direct image comparison, and the conjugate of such a comparison is the
morphism it was induced by. -/
theorem conjugateEquiv_modulePullbackCompIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f))
        (modulePullbackAdjunction B S hS (f ≫ g)) (modulePullbackCompIso B S hS f g).inv =
      (modulePushforwardCompIso B S hS f g).hom := by
  rw [modulePullbackCompIso_eq_leftAdjointCompIso]
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- The conjugate of the forward direction of the comparison of inverse images along a composite
is the inverse of the comparison of direct images. -/
theorem conjugateEquiv_modulePullbackCompIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (modulePullbackAdjunction B S hS (f ≫ g))
        ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f))
        (modulePullbackCompIso B S hS f g).hom =
      (modulePushforwardCompIso B S hS f g).inv := by
  refine (Iso.comp_hom_eq_id (modulePushforwardCompIso B S hS f g)).1 ?_
  rw [← conjugateEquiv_modulePullbackCompIso_inv f g, conjugateEquiv_comp]
  simp

end Conjugate

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- The comparison of the two composite direct images around a commutative square is the
conjugate of the comparison of the two composite inverse images. -/
theorem conjugateEquiv_modulePullbackSquareComparison_inv (comm : g' ≫ f = f' ≫ g) :
    conjugateEquiv ((modulePullbackAdjunction B S hS f).comp
          (modulePullbackAdjunction B S hS g'))
        ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f'))
        (modulePullbackSquareComparison f g f' g' comm).inv =
      (modulePushforwardCompIso B S hS g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) comm) ≫
        (modulePushforwardCompIso B S hS f' g).inv := by
  have hα : (modulePullbackSquareComparison f g f' g' comm).inv =
      (modulePullbackCompIso B S hS f' g).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm ≫
        (modulePullbackCompIso B S hS g' f).inv := by
    rw [modulePullbackSquareComparison]
    simp
  rw [hα, ← conjugateEquiv_comp _ (modulePullbackAdjunction B S hS (f' ≫ g)),
    ← conjugateEquiv_comp _ (modulePullbackAdjunction B S hS (g' ≫ f)),
    conjugateEquiv_modulePullbackCompIso_inv, conjugateEquiv_eqToHom_modulePullback comm,
    conjugateEquiv_modulePullbackCompIso_hom, Category.assoc]

/-- **The base change map is the mate of the comparison of the two composite inverse images**
around the square, under the two adjunctions of the vertical morphisms.  It is defined as the
mate of the comparison of the two composite direct images under the two adjunctions of the
horizontal morphisms, and the two descriptions agree because iterating the mates operation on a
square all of whose four functors are left adjoints gives the conjugate. -/
theorem moduleBaseChangeMap_eq_mateEquiv (comm : g' ≫ f = f' ≫ g) :
    moduleBaseChangeMap f g f' g' comm =
      mateEquiv (modulePullbackAdjunction B S hS f) (modulePullbackAdjunction B S hS f')
        (TwoSquare.mk (modulePullback B S hS g) (modulePullback B S hS f)
          (modulePullback B S hS f') (modulePullback B S hS g')
          (modulePullbackSquareComparison f g f' g' comm).inv) := by
  refine (mateEquiv (modulePullbackAdjunction B S hS g')
    (modulePullbackAdjunction B S hS g)).injective ?_
  rw [moduleBaseChangeMap, Equiv.apply_symm_apply]
  exact ((iterated_mateEquiv_conjugateEquiv (modulePullbackAdjunction B S hS f)
        (modulePullbackAdjunction B S hS f') (modulePullbackAdjunction B S hS g)
        (modulePullbackAdjunction B S hS g') _).trans
      (conjugateEquiv_modulePullbackSquareComparison_inv f g f' g' comm)).symm

/-- The comparison of the two composite inverse images around a square, backwards, written out as
its three factors. -/
theorem modulePullbackSquareComparison_inv_eq (comm : g' ≫ f = f' ≫ g) :
    (modulePullbackSquareComparison f g f' g' comm).inv =
      (modulePullbackCompIso B S hS f' g).hom ≫
        transportNatTrans (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm ≫
        (modulePullbackCompIso B S hS g' f).inv := by
  rw [modulePullbackSquareComparison, ← eqToHom_eq_transportNatTrans]
  simp

/-- The comparison of the two composite inverse images around a square, at a module, written out
as its three factors. -/
theorem modulePullbackSquareComparison_inv_app (comm : g' ≫ f = f' ≫ g)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackSquareComparison f g f' g' comm).inv.app M =
      (modulePullbackCompIso B S hS f' g).hom.app M ≫
        (transportNatTrans
          (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm).app M ≫
        (modulePullbackCompIso B S hS g' f).inv.app M :=
  NatTrans.congr_app (modulePullbackSquareComparison_inv_eq f g f' g' comm) M

/-- **The adjoint characterization of the base change map.**  Under the adjunction of the
base-changed vertical morphism `f'`, the base change map is the inverse image along `g'` of the
counit of the adjunction of `f`, transported across the comparison of the two composite inverse
images around the square.  Since the adjunct is a bijection this pins the map down, and it is the
description the source gives the map by. -/
theorem moduleBaseChangeMap_adjoint_split (comm : g' ≫ f = f' ≫ g)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullbackAdjunction B S hS f').homEquiv _ _).symm
        ((moduleBaseChangeMap f g f' g' comm).app K) =
      (modulePullbackSquareComparison f g f' g' comm).inv.app
          ((modulePushforward B S hS f).obj K) ≫
        (modulePullback B S hS g').map
          ((modulePullbackAdjunction B S hS f).counit.app K) := by
  rw [moduleBaseChangeMap_eq_mateEquiv, Adjunction.homEquiv_counit,
    mateEquiv_counit (modulePullbackAdjunction B S hS f) (modulePullbackAdjunction B S hS f')]

/-- The adjoint characterization of the base change map, with the comparison of the two composite
inverse images written out as its three factors.  This is the shape the pasting argument
consumes. -/
theorem moduleBaseChangeMap_adjoint_split' (comm : g' ≫ f = f' ≫ g)
    (K : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullbackAdjunction B S hS f').homEquiv _ _).symm
        ((moduleBaseChangeMap f g f' g' comm).app K) =
      ((modulePullbackCompIso B S hS f' g).hom.app ((modulePushforward B S hS f).obj K) ≫
          (transportNatTrans
            (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm).symm).app
            ((modulePushforward B S hS f).obj K) ≫
          (modulePullbackCompIso B S hS g' f).inv.app
            ((modulePushforward B S hS f).obj K)) ≫
        (modulePullback B S hS g').map
          ((modulePullbackAdjunction B S hS f).counit.app K) := by
  rw [moduleBaseChangeMap_adjoint_split, modulePullbackSquareComparison_inv_app]

end Square

section Paste

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h : Y'' ⟶ Y') (f'' : X'' ⟶ Y'') (h' : X'' ⟶ X')

/-- **Stacking two commutative squares along the base**: the outer rectangle commutes. -/
theorem pasteBaseComm (comm₁ : g' ≫ f = f' ≫ g) (comm₂ : h' ≫ f' = f'' ≫ h) :
    (h' ≫ g') ≫ f = f'' ≫ (h ≫ g) := by
  rw [Category.assoc, comm₁, ← Category.assoc, comm₂, Category.assoc]

/-- The comparison of inverse images along a composite is compatible with an equality of its
first morphism. -/
theorem modulePullbackCompIso_congr_left {V W Z : AlgebraicSpaces B S hS} {k₁ k₂ : V ⟶ W}
    (e : k₁ = k₂) (a : W ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (transportNatTrans
          (congrArg (fun k : V ⟶ W => modulePullback B S hS k) e)).app
          ((modulePullback B S hS a).obj M) ≫
        (modulePullbackCompIso B S hS k₂ a).hom.app M =
      (modulePullbackCompIso B S hS k₁ a).hom.app M ≫
        (transportNatTrans
          (congrArg (fun k : V ⟶ W => modulePullback B S hS (k ≫ a)) e)).app M := by
  subst e
  simp [transportNatTrans]

/-- The comparison of inverse images along a composite is compatible with an equality of its
second morphism. -/
theorem modulePullbackCompIso_congr_right {V W Z : AlgebraicSpaces B S hS} (a : V ⟶ W)
    {k₁ k₂ : W ⟶ Z} (e : k₁ = k₂) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullback B S hS a).map
          ((transportNatTrans
            (congrArg (fun k : W ⟶ Z => modulePullback B S hS k) e)).app M) ≫
        (modulePullbackCompIso B S hS a k₂).hom.app M =
      (modulePullbackCompIso B S hS a k₁).hom.app M ≫
        (transportNatTrans
          (congrArg (fun k : W ⟶ Z => modulePullback B S hS (a ≫ k)) e)).app M := by
  subst e
  simp [transportNatTrans]

end Paste

end AlgebraicGeometry.Space

end
