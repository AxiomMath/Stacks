module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute

/-!
# Polynomial charts of a scheme over a ring

For a scheme `X` over a ring `Λ`, this file defines the category whose objects are maps from an
open subscheme of `X` to an affine space over `Spec Λ`. The defining square with the structure
map of `X` is required to commute. This is the index category used to define the cotangent
complex of a scheme over a ring.

## Main definitions

* `AlgebraicGeometry.PolynomialChart`: an object of the category `C_{X/Λ}`.
* `AlgebraicGeometry.PolynomialChart.Hom`: the commutative diagrams which are its morphisms.
* `AlgebraicGeometry.PolynomialChart.toBase`: the structural arrow from the affine space of a
  chart to `Spec Λ`.
* `AlgebraicGeometry.PolynomialChart.openFunctor`: the functor forgetting a polynomial chart to
  its open subscheme.

## Implementation notes

An affine space is recorded together with an isomorphism to the spectrum of a multivariate
polynomial ring. Thus the chosen arrow from it to `Spec Λ` is the one induced by the constant
polynomial map. Open subschemes are represented by `Scheme.Opens`, so their arrows over `X` are
the canonical morphisms `Scheme.homOfLE`.

## References

* [Stacks Project, Tag 08V8](https://stacks.math.columbia.edu/tag/08V8)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A commutative diagram `U ⟶ A ⟶ Spec Λ`, `U ⟶ X ⟶ Spec Λ`, where `U` is an open subscheme of
`X` and `A` is an affine space over `Spec Λ`. -/
@[stacks 08V8]
structure PolynomialChart (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ)) where
  /-- The open subscheme `U` of `X`. -/
  openPart : X.Opens
  /-- The set of variables of the polynomial algebra. -/
  variableIndex : Type u
  /-- The scheme `A` in the displayed diagram. -/
  affineSpace : Scheme.{u}
  /-- A presentation of `A` as an affine space over `Spec Λ`. -/
  affineEquiv : affineSpace ≅ Spec (CommRingCat.of (MvPolynomial variableIndex Λ))
  /-- The arrow `U ⟶ A`. -/
  toAffine : (openPart : Scheme.{u}) ⟶ affineSpace
  /-- Commutativity of the displayed square. -/
  comm : toAffine ≫ affineEquiv.hom ≫
      Scheme.Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Λ →+* MvPolynomial variableIndex Λ)).op = openPart.ι ≫ structureMap

namespace PolynomialChart

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}
  {structureMap : X ⟶ Spec (CommRingCat.of Λ)}

/-- The structural arrow from the affine space of a polynomial chart to `Spec Λ`. -/
def toBase (P : PolynomialChart Λ X structureMap) :
    P.affineSpace ⟶ Spec (CommRingCat.of Λ) :=
  P.affineEquiv.hom ≫ Scheme.Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : Λ →+* MvPolynomial P.variableIndex Λ)).op

/-- A morphism of polynomial charts is a commutative diagram over both `X` and `Spec Λ`. -/
@[ext]
structure Hom (P Q : PolynomialChart Λ X structureMap) where
  /-- Inclusion of the underlying open subschemes. -/
  open_le : P.openPart ≤ Q.openPart
  /-- The arrow between the affine spaces. -/
  affine : P.affineSpace ⟶ Q.affineSpace
  /-- Commutativity of the square involving the two open subschemes. -/
  map_comm : P.toAffine ≫ affine = X.homOfLE open_le ≫ Q.toAffine
  /-- Compatibility of the affine-space arrow with their maps to `Spec Λ`. -/
  base_comm : affine ≫ Q.toBase = P.toBase

/-- The identity morphism of a polynomial chart. -/
def homId (P : PolynomialChart Λ X structureMap) : Hom P P where
  open_le := le_rfl
  affine := 𝟙 _
  map_comm := by rw [Category.comp_id, Scheme.homOfLE_rfl, Category.id_comp]
  base_comm := Category.id_comp _

/-- Composition of morphisms of polynomial charts. -/
def homComp {P Q R : PolynomialChart Λ X structureMap}
    (f : Hom P Q) (g : Hom Q R) : Hom P R where
  open_le := f.open_le.trans g.open_le
  affine := f.affine ≫ g.affine
  map_comm := by rw [← Category.assoc, f.map_comm, Category.assoc, g.map_comm,
    ← Category.assoc, Scheme.homOfLE_homOfLE]
  base_comm := by rw [Category.assoc, g.base_comm, f.base_comm]

/-- Polynomial charts with their morphisms `homId` and `homComp` form a category. -/
instance : Category (PolynomialChart Λ X structureMap) where
  Hom := Hom
  id := homId
  comp := homComp
  id_comp := by intro P Q f; ext; simp [homId, homComp]
  comp_id := by intro P Q f; ext; simp [homId, homComp]
  assoc := by intro P Q R S f g h; ext; simp [homComp]

/-- The functor sending a polynomial chart `(U ⟶ A)` to the open subscheme `U` of `X`. -/
def openFunctor : Functor (PolynomialChart Λ X structureMap) X.Opens where
  obj P := P.openPart
  map f := homOfLE f.open_le
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end PolynomialChart

end AlgebraicGeometry

end

end
