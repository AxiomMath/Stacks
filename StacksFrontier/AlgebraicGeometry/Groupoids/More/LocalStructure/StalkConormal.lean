module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Stalk maps at a prescribed image point, and the conormal module of a morphism at a point

Mathlib's `AlgebraicGeometry.Scheme.Hom.stalkMap` of `f : X ⟶ Y` at `x : X` goes out of the
stalk of `Y` at the point `f x`.  When a morphism is known to send `x` to a particular point
`y`, writing `f x` everywhere forces a transport along `f x = y` at every composition.  This
file records the variant `AlgebraicGeometry.Scheme.Hom.stalkMapAt` that takes the target point
as an argument together with the proof that it is the image of `x`, and shows that it
composes.

It also records the *conormal ideal* of a morphism at a point of its source, the kernel of
the stalk map, together with the map of conormal modules `I/I² → I'/I'²` attached to a
commuting triangle.  For a section `e : X ⟶ Y` of a morphism `Y ⟶ X`, the conormal ideal at
`x` is the ideal `I` whose quotient `I/I²` is the conormal module of `e` at `x`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.stalkMapAt`: the stalk map of `f` at `x`, out of the stalk at
  a prescribed image point `y` of `x`.
* `AlgebraicGeometry.Scheme.Hom.conormalIdeal`: the kernel of the stalk map of a morphism at a
  point of its source.
* `AlgebraicGeometry.Scheme.Hom.conormalMap`: the map of conormal modules attached to a
  commuting triangle `d ≫ f = e`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.stalkMapAt_comp`: `stalkMapAt` turns a composite of morphisms
  into a composite of ring maps.
* `AlgebraicGeometry.Scheme.Hom.stalkMapAt_triangle`: for a commuting triangle `d ≫ f = e`,
  the stalk map of `e` factors through the stalk map of `d`.
* `AlgebraicGeometry.Scheme.Hom.conormalMap_toCotangent`: the conormal map on the image of an
  element of the conormal ideal.

## Implementation notes

The conormal map is `Ideal.mapCotangent` for the `ℤ`-algebra map underlying `stalkMapAt`, so
it is `ℤ`-linear; an equality of such maps is exactly an equality of the underlying functions
on `I/I²`, which is what the statements about a groupoid scheme at an identity need.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The stalk map of `f : X ⟶ Y` at `x : X`, written out of the stalk of `Y` at a point `y`
given together with a proof that `f x = y`. -/
noncomputable def stalkMapAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    Y.presheaf.stalk y →+* X.presheaf.stalk x :=
  (eqToHom (congrArg Y.presheaf.stalk h.symm) ≫ f.stalkMap x).hom

/-- The underlying ring maps of the stalk maps of `f` and `g` compose to that of `f ≫ g`. -/
private theorem comp_stalkMap_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom = ((f ≫ g).stalkMap x).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- The stalk maps at prescribed image points compose. -/
theorem stalkMapAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hf : f x = y) (hg : g y = z) :
    (f.stalkMapAt x y hf).comp (g.stalkMapAt y z hg) =
      (f ≫ g).stalkMapAt x z (by rw [Scheme.Hom.comp_apply, hf, hg]) := by
  subst y z
  exact comp_stalkMap_hom f g x

/-- For a commuting triangle `d ≫ f = e` the stalk map of `e` at `x` is the stalk map of `f`
at `d x` followed by the stalk map of `d` at `x`. -/
theorem stalkMapAt_triangle {X Y Z : Scheme.{u}} (e : X ⟶ Y) (d : X ⟶ Z) (f : Z ⟶ Y)
    (h : d ≫ f = e) (x : X) :
    (d.stalkMap x).hom.comp (f.stalkMapAt (d x) (e x) (by rw [← Scheme.Hom.comp_apply, h])) =
      (e.stalkMap x).hom := by
  subst e
  exact comp_stalkMap_hom d f x

/-- The stalk map of an identity morphism is the identity. -/
theorem stalkMapAt_id (X : Scheme.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMapAt x x rfl = RingHom.id (X.presheaf.stalk x) := by
  unfold stalkMapAt
  rw [Scheme.Hom.stalkMap_id]
  show (eqToHom (rfl : X.presheaf.stalk x = X.presheaf.stalk x) ≫ 𝟙 _).hom = _
  simp

/-- Equal morphisms have equal stalk maps at a prescribed image point. -/
theorem stalkMapAt_congr {X Y : Scheme.{u}} (f g : X ⟶ Y) (e : f = g) (x : X) (y : Y)
    (hf : f x = y) (hg : g x = y) : f.stalkMapAt x y hf = g.stalkMapAt x y hg := by
  subst g
  obtain rfl : hf = hg := Subsingleton.elim _ _
  rfl

/-- The stalk map of an identity morphism is the identity, for an arbitrary proof that the
identity fixes the point. -/
theorem stalkMapAt_id' (X : Scheme.{u}) (x : X) (h : (𝟙 X : X ⟶ X) x = x) :
    (𝟙 X : X ⟶ X).stalkMapAt x x h = RingHom.id (X.presheaf.stalk x) := by
  obtain rfl : h = rfl := Subsingleton.elim _ _
  exact stalkMapAt_id X x

/-- The stalk maps of the underlying morphisms of a composite in a slice category compose. -/
theorem stalkMapAt_comp_left {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.left) (y : Y.left) (z : Z.left) (hf : f.left x = y) (hg : g.left y = z) :
    (f.left.stalkMapAt x y hf).comp (g.left.stalkMapAt y z hg) =
      (f ≫ g).left.stalkMapAt x z
        (by rw [Over.comp_left, Scheme.Hom.comp_apply, hf, hg]) := by
  simpa only [← Over.comp_left] using stalkMapAt_comp f.left g.left x y z hf hg

/-- The conormal ideal of `e : X ⟶ Y` at a point `x` of its source: the kernel of the stalk
map of `e` at `x`.  When `e` is a section of a morphism `Y ⟶ X`, the quotient `I/I²` by its
square is the conormal module of `e` at `x`. -/
noncomputable def conormalIdeal {X Y : Scheme.{u}} (e : X ⟶ Y) (x : X) :
    Ideal (Y.presheaf.stalk (e x)) := RingHom.ker (e.stalkMap x).hom

/-- The map of conormal modules attached to a commuting triangle `d ≫ f = e`: the stalk map of
`f` carries the conormal ideal of `e` at `x` into the conormal ideal of `d` at `x`, hence
induces a `ℤ`-linear map on the conormal modules. -/
noncomputable def conormalMap {X Y Z : Scheme.{u}} (e : X ⟶ Y) (d : X ⟶ Z) (f : Z ⟶ Y)
    (h : d ≫ f = e) (x : X) :
    (conormalIdeal e x).Cotangent →ₗ[ℤ] (conormalIdeal d x).Cotangent :=
  Ideal.mapCotangent _ _
    (f.stalkMapAt (d x) (e x) (by rw [← Scheme.Hom.comp_apply, h])).toIntAlgHom
    (by
      intro b hb
      change (d.stalkMap x).hom
        (f.stalkMapAt (d x) (e x) (by rw [← Scheme.Hom.comp_apply, h]) b) = 0
      rw [← RingHom.comp_apply, stalkMapAt_triangle e d f h x]
      exact hb)

/-- The conormal map of a commuting triangle on the class of an element of the conormal
ideal. -/
theorem conormalMap_toCotangent {X Y Z : Scheme.{u}} (e : X ⟶ Y) (d : X ⟶ Z) (f : Z ⟶ Y)
    (h : d ≫ f = e) (x : X) (y : conormalIdeal e x) :
    conormalMap e d f h x (Ideal.toCotangent (conormalIdeal e x) y) =
      Ideal.toCotangent (conormalIdeal d x)
        ⟨f.stalkMapAt (d x) (e x) (by rw [← Scheme.Hom.comp_apply, h]) y, by
          change (d.stalkMap x).hom
            (f.stalkMapAt (d x) (e x) (by rw [← Scheme.Hom.comp_apply, h]) y) = 0
          rw [← RingHom.comp_apply, stalkMapAt_triangle e d f h x]
          exact y.property⟩ :=
  rfl

end AlgebraicGeometry.Scheme.Hom

end
