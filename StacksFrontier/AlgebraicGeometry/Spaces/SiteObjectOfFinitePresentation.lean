module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# An affine scheme of finite presentation over a site object is a site object

The size cutoff of a big fppf site is closed under passing to an affine scheme locally of
finite presentation over a scheme already contained in the site: such a scheme is quasi-compact
and the morphism is locally of finite type, so Tag 04T7 bounds its size by the size of the
target. Together with the structure morphism to `S` this presents it as an object of the big
fppf category over `S`, with a morphism to the given object whose underlying morphism of
schemes is the given one.

This is what turns an approximating base produced over the underlying schemes into a base over
which an algebraic space can be formed.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.siteObjectOver`: the object of the big fppf category over `S`
  determined by a contained scheme with a morphism to the underlying scheme of a given object.
* `AlgebraicGeometry.BigFppfOver.siteMapOver`: its morphism to that object.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_of_locallyOfFinitePresentation`: the size cutoff is
  closed under affine morphisms locally of finite presentation.

## Implementation notes

The size bound is Tag 04T7, `AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`, which is
already available in the general form "locally of finite type with quasi-compact source": an
affine scheme is quasi-compact and a morphism locally of finite presentation is locally of
finite type, so both instances are found by unification and no bound on the cardinality of a
finitely presented algebra has to be proved separately.

The underlying category of a big fppf site is a full subcategory of schemes cut off at a
cardinal, and the big fppf category over `S` is a slice of it, so an object is an `Over.mk` of a
wrapped morphism of schemes and the two compatibility statements below hold by `rfl`.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The size cutoff of a big fppf site is closed under passing to an affine scheme locally of
finite presentation over a contained scheme. -/
theorem BigFppfSite.contains_of_locallyOfFinitePresentation (B : BigFppfSite.{u})
    {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hY : B.Contains Y) : B.Contains X :=
  (Scheme.size_le_of_locallyOfFiniteType f).trans_lt hY

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme contained in the site, with a morphism to the scheme underlying an object of the
big fppf category over `S`, as an object of that category: its structure morphism to `S` is the
composite with the structure morphism of the target. -/
def siteObjectOver (U : BigFppfOver B S hS) {Z : Scheme.{u}} (hZ : B.Contains Z)
    (φ : Z ⟶ (toScheme B S hS).obj U) : BigFppfOver B S hS :=
  Over.mk (⟨φ ≫ U.hom.hom⟩ : B.obj hZ ⟶ B.obj hS)

/-- The morphism of `AlgebraicGeometry.BigFppfOver.siteObjectOver` to the given object. -/
def siteMapOver (U : BigFppfOver B S hS) {Z : Scheme.{u}} (hZ : B.Contains Z)
    (φ : Z ⟶ (toScheme B S hS).obj U) : siteObjectOver B S hS U hZ φ ⟶ U :=
  Over.homMk (⟨φ⟩ : B.obj hZ ⟶ U.left) (by ext; rfl)

/-- The scheme underlying `AlgebraicGeometry.BigFppfOver.siteObjectOver` is the given scheme. -/
@[simp]
theorem toScheme_obj_siteObjectOver (U : BigFppfOver B S hS) {Z : Scheme.{u}}
    (hZ : B.Contains Z) (φ : Z ⟶ (toScheme B S hS).obj U) :
    (toScheme B S hS).obj (siteObjectOver B S hS U hZ φ) = Z :=
  rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.BigFppfOver.siteMapOver` is the given
morphism. -/
@[simp]
theorem toScheme_map_siteMapOver (U : BigFppfOver B S hS) {Z : Scheme.{u}}
    (hZ : B.Contains Z) (φ : Z ⟶ (toScheme B S hS).obj U) :
    (toScheme B S hS).map (siteMapOver B S hS U hZ φ) = φ :=
  rfl

end BigFppfOver

end AlgebraicGeometry

end
