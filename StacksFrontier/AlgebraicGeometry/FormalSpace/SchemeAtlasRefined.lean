module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSchemeSourceRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas

/-!
# Affine charts of a sheaf covered by one object of the big fppf site

An affine chart, locally of finite type, of a presheaf on the big fppf site of `S` that receives a
locally surjective map from one object `U` of the site has size at most that of `U`.

## Main results

* `AlgebraicGeometry.FormalSpace.inverseImage_etale_le_locallyOfFiniteType`: an étale morphism of
  the big fppf site of `S` is locally of finite type.
* `AlgebraicGeometry.FormalSpace.affineChart_size_le'`: an affine chart, locally of finite type, of
  a presheaf receiving a locally surjective map from `h_U` has size at most `size U`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u
universe u₁ v₁

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms
  schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks

/-- An étale morphism of schemes is locally of finite type, read as an inequality of the
inverse-image morphism properties of the big fppf site of `S`. -/
public theorem inverseImage_etale_le_locallyOfFiniteType
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS) := fun _ _ _ h ↦ by
  have : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map _) := h
  exact inferInstanceAs (LocallyOfFiniteType _)

/-- **An affine chart of a sheaf covered by one object of the site is no larger than that
object.** Let `X` be a presheaf on the big fppf site of `S` receiving a locally surjective map
`t : h_U ⟶ X` from an object of the site, and let `c : h_V ⟶ X` be a map out of an *affine*
object of the site which is representable by objects of the site and locally of finite type.
Then `size V ≤ size U`. -/
public theorem affineChart_size_le'
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (U V : AlgebraicGeometry.BigFppfOver B S hS) [IsAffine V.left.obj]
    (t : uliftYoneda.{u + 1}.obj U ⟶ X)
    (ht : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) t)
    (c : uliftYoneda.{u + 1}.obj V ⟶ X)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c) :
    V.left.obj.size ≤ U.left.obj.size := by
  let Y := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  let p : hc.rep.pullback t ⟶ U := hc.rep.snd t
  let a : hc.rep.pullback t ⟶ V := Y.preimage (hc.rep.fst t)
  have : LocallyOfFiniteType p.left.hom := hc.property_snd t
  have ha : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology B S hS) (Y.map a) := by
    simpa only [a, Y.map_preimage] using isLocallySurjective_of_isPullback
      (AlgebraicGeometry.BigFppfOver.topology B S hS) (hc.rep.isPullback t).flip ht
  choose E d hd using exists_fppfCovering_of_isLocallySurjective B S hS a ha
  exact size_le_of_compact_of_fppf_factorsThrough p.left.hom a.left.hom E d hd

end AlgebraicGeometry.FormalSpace

end
