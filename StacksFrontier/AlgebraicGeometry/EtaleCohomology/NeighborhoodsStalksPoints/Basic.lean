module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometric points and their étale neighborhoods

A geometric point of a scheme is a morphism from the spectrum of an algebraically closed field. We
also define when it lies over an ordinary point, its étale neighborhoods, and the morphisms between
such neighborhoods.

## Main definitions

* `AlgebraicGeometry.GeometricPoint` is a geometric point of a scheme.
* `AlgebraicGeometry.GeometricPoint.LiesOver` says that a geometric point has a given image in the
  underlying space.
* `AlgebraicGeometry.GeometricPoint.map` is the geometric point obtained by composing with a
  morphism of schemes.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood` is an étale neighborhood of a geometric
  point.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.Hom` is a morphism of étale neighborhoods.

## Implementation notes

A geometric point records its chosen algebraically closed field. A morphism of étale neighborhoods
records both the map over the base and its compatibility with the chosen lifts of the geometric
point. Étale neighborhoods of a geometric point live in the namespace `GeometricPoint`, apart from
the étale neighborhoods of an ordinary point of a scheme.

## References

* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A geometric point of a scheme is a morphism from the spectrum of an algebraically closed field.
-/
@[stacks 03PO "part (1)", sga "4½ Arcata 2.3.1" "special case", sga "7 XIX 1.4"]
structure GeometricPoint (S : Scheme.{u}) where
  /-- The algebraically closed residue field of the geometric point. -/
  residueField : Type u
  [field_residueField : Field residueField]
  [isAlgClosed_residueField : IsAlgClosed residueField]
  /-- The morphism from the spectrum of the residue field to the scheme. -/
  hom : Spec (.of residueField) ⟶ S

namespace GeometricPoint

attribute [instance] field_residueField isAlgClosed_residueField

/-- The spectrum which is the source of a geometric point. -/
abbrev source {S : Scheme.{u}} (s : GeometricPoint S) : Scheme.{u} :=
  Spec (.of s.residueField)

/-- A geometric point lies over the point which is its image in the underlying topological space.
-/
@[stacks 03PO "part (2)"]
abbrev LiesOver {S : Scheme.{u}} (s : GeometricPoint S) (x : S) : Prop := s.hom default = x

/-- The geometric point obtained by composing with a morphism of schemes. -/
@[implicit_reducible, simps]
def map {X Y : Scheme.{u}} (s : GeometricPoint X) (f : X ⟶ Y) : GeometricPoint Y where
  residueField := s.residueField
  hom := s.hom ≫ f

/-- An étale neighborhood of a geometric point consists of an étale scheme over the base together
with a lift of the geometric point. -/
@[stacks 03PO "part (3)", sga "4 VIII 3.9" "objects of C_ξ"]
structure EtaleNeighborhood {S : Scheme.{u}} (s : GeometricPoint S) where
  /-- The scheme underlying the neighborhood. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the base scheme. -/
  toBase : scheme ⟶ S
  [etale_toBase : Etale toBase]
  /-- The chosen lift of the geometric point to the neighborhood. -/
  point : s.source ⟶ scheme
  /-- The chosen lift composes to the original geometric point. -/
  point_comp : point ≫ toBase = s.hom

namespace EtaleNeighborhood

attribute [instance] etale_toBase

/-- A morphism of étale neighborhoods is a morphism over the base which carries the chosen lift to
the chosen lift. -/
@[ext, stacks 03PO "part (4)"]
structure Hom {S : Scheme.{u}} {s : GeometricPoint S} (U V : EtaleNeighborhood s) where
  /-- The underlying morphism of schemes. -/
  hom : U.scheme ⟶ V.scheme
  /-- The underlying morphism is over the base scheme. -/
  over : hom ≫ V.toBase = U.toBase
  /-- The morphism carries the chosen lift of the geometric point to the chosen lift. -/
  point_comp : U.point ≫ hom = V.point

/-- Étale neighborhoods of a geometric point, with the morphisms above, form a category. -/
instance {S : Scheme.{u}} {s : GeometricPoint S} : Category (EtaleNeighborhood s) where
  Hom := Hom
  id U := { hom := 𝟙 U.scheme, over := by simp, point_comp := by simp }
  comp f g := { hom := f.hom ≫ g.hom
                over := by simp only [Category.assoc, g.over, f.over]
                point_comp := by simp only [← Category.assoc, f.point_comp, g.point_comp] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- The underlying scheme morphism of the identity is the identity. -/
@[simp] lemma id_hom {S : Scheme.{u}} {s : GeometricPoint S}
    (U : EtaleNeighborhood s) : Hom.hom (𝟙 U) = 𝟙 U.scheme := rfl

/-- The underlying scheme morphism of a composite is the composite. -/
@[simp] lemma comp_hom {S : Scheme.{u}} {s : GeometricPoint S}
    {U V W : EtaleNeighborhood s} (f : U ⟶ V) (g : V ⟶ W) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry

end
