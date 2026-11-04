module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension

/-!
# The category of families of curves (Stacks 0D4Z)

A *family of curves* is a morphism `f : X ⟶ S` whose base `S` is a scheme, whose total space
`X` is an algebraic space, and which is flat, proper, of finite presentation and of relative
dimension at most one. A morphism of families is a pair consisting of a morphism of total
spaces and a morphism of base schemes forming a cartesian square, and forgetting a family to
its base scheme exhibits the resulting category as a category over the big fppf site of
schemes.

The fibres of a family of curves are allowed to be reducible and non-reduced, so that the
category parametrizes proper schemes of dimension at most one; and the total space has to be
allowed to be an algebraic space rather than a scheme, since there are families of curves over
the affine line whose total space is not a scheme.

## Main definitions

* `AlgebraicGeometry.CurveFamily`: the families of curves.
* `AlgebraicGeometry.CurveFamily.Hom`: the morphisms of families of curves.
* `AlgebraicGeometry.CurveFamily.instCategory`: the category of families of curves.
* `AlgebraicGeometry.curvesProjection`: the forgetful functor to the big fppf site.

## Implementation notes

The big fppf site of the source is absolute, while this library's big fppf site is a
size-bounded category of schemes over a chosen base scheme. The two are reconciled by taking
the base to be `AlgebraicGeometry.integerBase`, the spectrum of the integers: it is a terminal
scheme (`AlgebraicGeometry.specULiftZIsTerminal`), so a scheme over it is a scheme with no
further data, and the slice site is the absolute one. Algebraic spaces over that base are the
full subcategory `AlgebraicGeometry.AlgebraicSpaces` of Stacks 02X2, and a base scheme is read
as an algebraic space by `AlgebraicGeometry.schemeSpace` of Stacks 04U8.

The relative dimension condition is Stacks 06LR, part (1), *relative dimension at most `d`* for
a morphism of algebraic spaces, at `d = 1`, written out: Stacks 06LR bounds the Stacks 04NM
relative dimension at each point of the source, which is the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint` of Stacks 04NC applied to the
fibre-dimension property `AlgebraicGeometry.HasFiberDimensionAt` of Stacks 04NL. It is not
`AlgebraicGeometry.RelativeDimensionLE`, the scheme-level relative dimension of Stacks 02NJ.

Properness is `AlgebraicGeometry.Space.IsProper` of Stacks 03ZM, whose universal closedness is
stated over the topology on points of an algebraic space; by
`AlgebraicGeometry.Space.PointTopologyFamily.topology_eq` this is the topology of any family of
topologies satisfying Stacks 03BX.

Both constituents of a morphism of families are morphisms of the ambient categories and the
cartesian condition is a `CategoryTheory.IsPullback` in the category of algebraic spaces, so
identities and composition are componentwise and the two square laws are the identity and
pasting lemmas for pullback squares.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The spectrum of the integers, `Spec (ULift ℤ)`. -/
abbrev integerBase : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A *family of curves*: a morphism from an algebraic space to a scheme of
the big fppf site which is flat, proper, of finite presentation and of relative dimension at
most one. -/
@[stacks 0D4Z "objects"]
structure CurveFamily where
  /-- The base scheme of the family. -/
  base : BigFppfOver B integerBase hZ
  /-- The total space of the family, an algebraic space. -/
  total : AlgebraicSpaces B integerBase hZ
  /-- The structure morphism of the family. -/
  toBase : total ⟶ schemeSpace base
  /-- The structure morphism is flat (Stacks 03ML, part (1)). -/
  flat : Space.IsFlat B integerBase hZ toBase.hom
  /-- The structure morphism is proper (Stacks 03ZM). -/
  proper : Space.IsProper B integerBase hZ toBase.hom
  /-- The structure morphism is of finite presentation (Stacks 03XP, part (3)). -/
  finitePresentation : Space.IsFinitePresentation B integerBase hZ toBase.hom
  /-- The structure morphism has relative dimension at most one (Stacks 06LR, part (1)): at
  every point of the total space the fibre dimension is bounded by one in every étale chart. -/
  relativeDimensionLE :
    ∀ x : Space.points B integerBase hZ total.obj,
      ∃ e : ℕ, e ≤ 1 ∧
        Space.HoldsOnEveryEtaleChartAtPoint B integerBase hZ
          (@HasFiberDimensionAt.{u} (e : ℕ∞)) toBase.hom x

namespace CurveFamily

/-- A morphism of families of curves: a morphism of total spaces over a
morphism of base schemes whose square is cartesian. -/
@[ext, stacks 0D4Z "morphisms"]
structure Hom (X Y : CurveFamily B hZ) where
  /-- The morphism of base schemes. -/
  baseMap : X.base ⟶ Y.base
  /-- The morphism of total spaces. -/
  totalMap : X.total ⟶ Y.total
  /-- The square of structure morphisms is cartesian. -/
  cartesian : IsPullback totalMap X.toBase Y.toBase (schemeSpaceMap baseMap)

end CurveFamily

private theorem schemeSpaceMap_id (U : BigFppfOver B integerBase hZ) :
    schemeSpaceMap (𝟙 U) = 𝟙 (schemeSpace U) := by
  simp [schemeSpaceMap]
  rfl

/-- Reading a scheme of the big fppf site as an algebraic space takes a composite of morphisms
of schemes to the composite of the induced morphisms of algebraic spaces. -/
theorem schemeSpaceMap_comp {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V W : BigFppfOver B S hS} (f : U ⟶ V) (g : V ⟶ W) :
    schemeSpaceMap (f ≫ g) = schemeSpaceMap f ≫ schemeSpaceMap g := by
  simp [schemeSpaceMap]
  rfl

/-- Families of curves and cartesian squares between them form a category,
with componentwise identities and composition. -/
@[stacks 0D4Z "category"]
instance : Category (CurveFamily B hZ) where
  Hom := CurveFamily.Hom B hZ
  id X :=
    { baseMap := 𝟙 X.base
      totalMap := 𝟙 X.total
      cartesian := by simpa only [schemeSpaceMap_id] using IsPullback.id_horiz X.toBase }
  comp f g :=
    { baseMap := f.baseMap ≫ g.baseMap
      totalMap := f.totalMap ≫ g.totalMap
      cartesian := by
        simpa only [schemeSpaceMap_comp] using f.cartesian.paste_horiz g.cartesian }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by intros; ext <;> simp [Category.assoc]

/-- The forgetful functor taking a family of curves to its base scheme, which makes the category
of families of curves a category over the big fppf site. -/
@[stacks 0D4Z "projection"]
def curvesProjection : CurveFamily B hZ ⥤ B.Schemes where
  obj X := X.base.left
  map f := f.baseMap.left
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection takes a family of curves to the scheme underlying its base. -/
@[simp]
theorem curvesProjection_obj (X : CurveFamily B hZ) :
    (curvesProjection B hZ).obj X = X.base.left := rfl

/-- The projection takes a morphism of families to the morphism underlying its base map. -/
@[simp]
theorem curvesProjection_map {X Y : CurveFamily B hZ} (f : X ⟶ Y) :
    (curvesProjection B hZ).map f = f.baseMap.left := rfl

end AlgebraicGeometry

end
