module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber

/-!
# Étale neighbourhoods of a geometric point inside a big étale site

Let `B` be a big étale site containing a scheme `S`, and let `s` be a geometric point of `S`.
An étale neighbourhood of `s` in the small étale site of `S` cut out by `B`, an object of the
category of elements of `AlgebraicGeometry.geometricPointFiber`, is in particular an étale
neighbourhood of `s` in the sense of Mathlib's point `AlgebraicGeometry.Scheme.pointSmallEtale`
of the small étale site, which has no size cutoff. This file constructs that comparison functor,
shows that it is fully faithful, and shows that every étale neighbourhood is refined by an affine
one coming from `B`.

## Main definitions

* `AlgebraicGeometry.geometricPointNeighborhoodInclusion`: the comparison functor.

## Main results

* `AlgebraicGeometry.exists_isAffine_geometricPointNeighborhoodInclusion`: every étale
  neighbourhood of `s` has an affine refinement inside the chosen size cutoff.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- Forget the size cutoff on an étale neighborhood: an étale neighborhood of `s` inside the chosen
big étale site is an étale neighborhood of `s` in the sense of the point
`AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site. -/
public def geometricPointNeighborhoodInclusion : (geometricPointFiber B S hS s).Elements ⥤
    (Scheme.pointSmallEtale s.hom).fiber.Elements where
  obj U := ⟨MorphismProperty.Over.mk _ (B.inclusion.map U.1.obj.hom) U.1.property,
    Over.homMk U.2.1 U.2.2⟩
  map {U V} f := ⟨MorphismProperty.Over.homMk ((SmallEtale.toScheme B S hS).map f.1)
    (by
      change B.inclusion.map f.1.hom.left ≫ B.inclusion.map V.1.obj.hom =
        B.inclusion.map U.1.obj.hom
      rw [← Functor.map_comp, Over.w]) (by trivial),
    Over.OverMorphism.ext (congrArg Subtype.val f.2)⟩

/-- The functor `AlgebraicGeometry.geometricPointNeighborhoodInclusion` is faithful. -/
public instance : (geometricPointNeighborhoodInclusion B S hS s).Faithful :=
  inferInstanceAs (neighborhoodInclusion B S hS s).Faithful

/-- The functor `AlgebraicGeometry.geometricPointNeighborhoodInclusion` is full. -/
public instance : (geometricPointNeighborhoodInclusion B S hS s).Full :=
  inferInstanceAs (neighborhoodInclusion B S hS s).Full

/-- Every étale neighborhood of `s` has an affine refinement inside the chosen size cutoff. -/
public theorem exists_isAffine_geometricPointNeighborhoodInclusion
    (U : (Scheme.pointSmallEtale s.hom).fiber.Elements) :
    ∃ V, IsAffine ((SmallEtale.toScheme B S hS).obj V.1) ∧
      Nonempty ((geometricPointNeighborhoodInclusion B S hS s).obj V ⟶ U) :=
  exists_neighborhood_refinement B S hS s U

end AlgebraicGeometry

end
