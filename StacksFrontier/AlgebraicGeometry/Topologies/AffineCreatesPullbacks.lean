module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Fibre products in an affine full subcategory

Let `G : C ⥤ Scheme` preserve fibre products. Then the full subcategory of `C` on the objects
whose image under `G` is affine creates fibre products: the fibre product taken in `C` has
affine image, because `G` carries it to the fibre product of two affine schemes over an affine
scheme.

The statement mentions no topology, and every big or small site of schemes whose affine objects
need fibre products instantiates it at its own inclusion functor — which is why it was separately
declared in five modules before it was put here.

## Main definitions

* `AlgebraicGeometry.affineCreatesPullbacks`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u' u

namespace AlgebraicGeometry

/-- **The affine objects of a category over `Scheme` create fibre products**, as soon as the
functor to schemes preserves them. -/
@[instance_reducible]
public noncomputable def affineCreatesPullbacks
    {C : Type u'} [Category.{v, u'} C] [HasPullbacks C]
    (G : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan G] :
    CreatesLimitsOfShape WalkingCospan
      (ObjectProperty.ι (fun X : C => IsAffine (G.obj X))) where
  CreatesLimit := fun {F} => by
    let D := F ⋙ ObjectProperty.ι (fun X : C => IsAffine (G.obj X))
    have : IsAffine (G.obj (D.obj .left)) := (F.obj .left).property
    have : IsAffine (G.obj (D.obj .right)) := (F.obj .right).property
    have : IsAffine (G.obj (D.obj .one)) := (F.obj .one).property
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _)) (by
        let e := PreservesPullback.iso G (D.map WalkingCospan.Hom.inl)
          (D.map WalkingCospan.Hom.inr)
        exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance)

end AlgebraicGeometry

end
