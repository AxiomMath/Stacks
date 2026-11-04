module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# Polynomial charts of an algebraic space over a ring

For an algebraic space `X` over a ring `Λ`, this file defines the category `C_{X/Λ}` whose
objects are the commutative squares
```
X ← U
↑   ↑
Spec Λ ← A
```
in which `U ⟶ X` is an object of the small étale site of `X` and `A` is an affine space over
`Spec Λ`. This is the index category used to define the cotangent complex of an algebraic space
over a ring, and it is the algebraic-space counterpart of
`AlgebraicGeometry.PolynomialChart`, the category of polynomial charts of a *scheme*
(Stacks 08V8).

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart`: an object of the category `C_{X/Λ}`.
* `AlgebraicGeometry.Space.PolynomialChart.Hom`: the commutative diagrams which are its
  morphisms.
* `AlgebraicGeometry.Space.PolynomialChart.toBase`: the structural arrow from the affine space
  of a chart to `Spec Λ`.
* `AlgebraicGeometry.Space.PolynomialChart.openFunctor`: the functor forgetting a polynomial
  chart to its object of the small étale site of `X`.
* `AlgebraicGeometry.Space.smallEtaleToScheme`: the functor taking an object of the small étale
  site of `X` to its underlying scheme.

## Implementation notes

An algebraic space is a presheaf on the big fppf site satisfying the conditions of Stacks 025Y,
and `U ⟶ X` ranges over the objects of its small étale site of Stacks 03ED, which are the étale
charts of the presheaf. Since those objects live over the big fppf site, the arrow `U ⟶ Spec Λ`
closing the square is the structure morphism of the corresponding object of the slice, read in
`Scheme` through the inclusion of the site's underlying category.

An affine space is recorded together with an isomorphism to the spectrum of a multivariate
polynomial ring, so the chosen arrow from it to `Spec Λ` is the one induced by the inclusion of
the constants.

## References

* [Stacks Project, Tag 08VI](https://stacks.math.columbia.edu/tag/08VI)
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Space

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)

/-- The functor taking an object of the small étale site of a presheaf `X` on the big fppf site
of `Spec Λ` to its underlying scheme. -/
abbrev smallEtaleToScheme : SmallEtale B (Spec (CommRingCat.of Λ)) hS X ⥤ Scheme.{u} :=
  SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X ⋙
    BigFppfOver.toScheme B (Spec (CommRingCat.of Λ)) hS

/-- A commutative square `U ⟶ A ⟶ Spec Λ`, `U ⟶ X ⟶ Spec Λ`, in which `U ⟶ X` is an object of
the small étale site of the algebraic space `X` and `A` is an affine space over `Spec Λ`. -/
@[stacks 08VI "the objects of the category C_{X/Λ}"]
structure PolynomialChart (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X) where
  /-- The object `U ⟶ X` of the small étale site of `X`. -/
  openPart : SmallEtale B (Spec (CommRingCat.of Λ)) hS X
  /-- The set of variables of the polynomial algebra presenting `A`. -/
  variableIndex : Type u
  /-- The scheme `A` in the displayed diagram. -/
  affineSpace : Scheme.{u}
  /-- A presentation of `A` as an affine space over `Spec Λ`. -/
  affineEquiv : affineSpace ≅ Spec (CommRingCat.of (MvPolynomial variableIndex Λ))
  /-- The arrow `U ⟶ A`. -/
  toAffine : (smallEtaleToScheme Λ B hS X).obj openPart ⟶ affineSpace
  /-- Commutativity of the displayed square. -/
  comm : toAffine ≫ affineEquiv.hom ≫ Scheme.Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : Λ →+* MvPolynomial variableIndex Λ)).op =
    B.inclusion.map
      ((SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X).obj openPart).hom

namespace PolynomialChart

variable {Λ B hS X} {hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X}

/-- The structural arrow from the affine space of a polynomial chart to `Spec Λ`, induced by
the inclusion of the constants into the polynomial algebra. -/
def toBase (P : PolynomialChart Λ B hS X hX) :
    P.affineSpace ⟶ Spec (CommRingCat.of Λ) :=
  P.affineEquiv.hom ≫ Scheme.Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ)).op

/-- A morphism of polynomial charts is a commutative diagram over both the algebraic space `X`
and `Spec Λ`. -/
@[ext, stacks 08VI "the morphisms of the category C_{X/Λ}"]
structure Hom (P Q : PolynomialChart Λ B hS X hX) where
  /-- The arrow between the objects of the small étale site of `X`. -/
  openMap : P.openPart ⟶ Q.openPart
  /-- The arrow between the affine spaces. -/
  affine : P.affineSpace ⟶ Q.affineSpace
  /-- Commutativity of the square involving the two objects of the small étale site. -/
  map_comm : P.toAffine ≫ affine =
    (smallEtaleToScheme Λ B hS X).map openMap ≫ Q.toAffine
  /-- Compatibility of the affine-space arrow with their maps to `Spec Λ`. -/
  base_comm : affine ≫ Q.toBase = P.toBase

/-- The identity morphism of a polynomial chart. -/
def homId (P : PolynomialChart Λ B hS X hX) : Hom P P where
  openMap := 𝟙 _
  affine := 𝟙 _
  map_comm := by simp
  base_comm := Category.id_comp _

/-- Composition of morphisms of polynomial charts. -/
def homComp {P Q R : PolynomialChart Λ B hS X hX} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  openMap := f.openMap ≫ g.openMap
  affine := f.affine ≫ g.affine
  map_comm := by
    rw [← Category.assoc, f.map_comm, Category.assoc, g.map_comm, ← Category.assoc,
      Functor.map_comp]
  base_comm := by rw [Category.assoc, g.base_comm, f.base_comm]

/-- Polynomial charts of `X` over `Λ` form a category, with morphisms `Hom`. -/
instance : Category (PolynomialChart Λ B hS X hX) where
  Hom := Hom
  id := homId
  comp := homComp
  id_comp := by intro P Q f; ext <;> simp [homId, homComp]
  comp_id := by intro P Q f; ext <;> simp [homId, homComp]
  assoc := by intro P Q R S f g h; ext <;> simp [homComp]

/-- The functor sending a polynomial chart `(U ⟶ A)` to the object `U ⟶ X` of the small étale
site of `X`. -/
@[stacks 08VI "the forgetful functor to the small étale site"]
def openFunctor :
    PolynomialChart Λ B hS X hX ⥤ SmallEtale B (Spec (CommRingCat.of Λ)) hS X where
  obj P := P.openPart
  map f := f.openMap
  map_id _ := rfl
  map_comp _ _ := rfl

end PolynomialChart

end AlgebraicGeometry.Space

end

end
