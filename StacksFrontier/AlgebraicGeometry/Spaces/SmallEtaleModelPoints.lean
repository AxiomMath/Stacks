module

public import Mathlib.CategoryTheory.Sites.Point.Map
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.Deformation.Artin.Obstruction.SpaceExtFunctors

/-!
# The geometric points of an algebraic space on the model of its small étale site

Let `X` be an algebraic space. The small étale site `X_et` has its objects in `Type (u + 1)`; its
model (`AlgebraicGeometry.Space.smallEtaleModelEquiv`) is an equivalent site with objects in
`Type u`, on which the cotangent complex of Stacks 08SU of a morphism of algebraic spaces is
formed (`AlgebraicGeometry.Space.modelRingedToposHom`). This file transports the geometric points
of `X` to points of the model (`AlgebraicGeometry.Space.modelSitePoint`), along the cocontinuous
functor `X_et ⥤ model` (Mathlib's `CategoryTheory.GrothendieckTopology.Point.map`), and proves:

* they form a conservative family of points of the model
  (`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_modelSitePoint`), from Stacks 04K5 on
  `X_et` and the equivalence of the categories of sheaves;
* the stalk at the point of `x̄` of the inverse image of a sheaf of rings `R` on `Y_et` along the
  transported morphism `X_model ⟶ Y_et` of `f : X ⟶ Y` is the stalk of `R` at `f ∘ x̄`, naturally
  in `R` (`AlgebraicGeometry.Space.modelInverseImageFiberRingIso`): the sheaf-of-rings form of
  Stacks 04K2 on the model.

The first is a general fact about a conservative family of points of a site and an equivalence
with a site carrying a dense-subsite structure
(`Stacks.SitePointMap.isConservativeFamilyOfPoints_map`).

## Main definitions

* `AlgebraicGeometry.Space.modelSitePoint`
* `AlgebraicGeometry.Space.modelInverseImageFiberRingIso`

## Main results

* `Stacks.SitePointMap.isConservativeFamilyOfPoints_map`
* `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_modelSitePoint`

## References

* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u₁ v₁ u₂ v₂ u

namespace Stacks.SitePointMap

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J] [LocallySmall.{w} D]

/-- **The images of a conservative family of points along an equivalence of sites are a
conservative family.** If `e : C ≌ D` is an equivalence for which `e.inverse` exhibits `(C, J)` as
a dense subsite of `(D, K)`, the points `Φ.map e.functor K` of `(D, K)` attached to a conservative
family of points `Φ` of `(C, J)` are conservative: the fibre of a sheaf `G` on `D` at `Φ.map` is
the fibre at `Φ` of its restriction to `C`, and restriction is an equivalence of categories of
sheaves. -/
theorem isConservativeFamilyOfPoints_map {I : Type*} (φ : I → J.Point.{w})
    (hφ : (ObjectProperty.ofObj φ).IsConservativeFamilyOfPoints) :
    (ObjectProperty.ofObj (fun i => (φ i).map e.functor K)).IsConservativeFamilyOfPoints := by
  refine ⟨⟨fun {G₁ G₂} f hf => ?_⟩⟩
  let g := (Equivalence.sheafCongr J K e (Type w)).inverse.map f
  have : ∀ Φ : (ObjectProperty.ofObj φ).FullSubcategory,
      IsIso (Φ.obj.sheafFiber (A := Type w).map g) := by
    rintro ⟨Φ, ⟨i⟩⟩
    exact (NatIso.isIso_map_iff (Functor.isoWhiskerLeft (sheafToPresheaf K (Type w))
      ((φ i).presheafFiberMapIso e.functor K (Type w))) f).1
        (hf ⟨(φ i).map e.functor K, ObjectProperty.ofObj_apply _ i⟩)
  have : IsIso g := hφ.jointlyReflectIsomorphisms_type.isIso g
  exact isIso_of_reflects_iso f (Equivalence.sheafCongr J K e (Type w)).inverse

end Stacks.SitePointMap

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The points -/

section Points

variable (X : AlgebraicSpaces B S hS)

/-- **The point of the model of the small étale site of `X` attached to a geometric point**: the
image of the point of `X_et` along the comparison `X_et ⥤ model`. -/
abbrev modelSitePoint (x : GeometricPoint B S hS X.1) :
    (smallEtaleModelTopology B S hS X.1).Point.{u} :=
  (etaleSitePoint B S hS X.1 x X.2).map (smallEtaleModelEquiv B S hS X).functor
    (smallEtaleModelTopology B S hS X.1)

/-- **The geometric points of `X` are a conservative family of points of the model of its small
étale site.** -/
theorem isConservativeFamilyOfPoints_modelSitePoint :
    (ObjectProperty.ofObj (modelSitePoint B S hS X)).IsConservativeFamilyOfPoints :=
  Stacks.SitePointMap.isConservativeFamilyOfPoints_map (smallEtaleModelEquiv B S hS X)
    (fun x => etaleSitePoint B S hS X.1 x X.2)
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2)

/-- The stalk at the point of a geometric point of the restriction to the model of a sheaf of
commutative rings on `X_et` is its stalk on `X_et`. -/
def modelRestrictionFiberRingIso (x : GeometricPoint B S hS X.1) :
    (smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
        (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1) ⋙
      (modelSitePoint B S hS X x).sheafFiber (A := CommRingCat.{u}) ≅
      (etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u}) :=
  Functor.isoWhiskerLeft _ ((etaleSitePoint B S hS X.1 x X.2).sheafFiberMapIso
      (smallEtaleModelEquiv B S hS X).functor (smallEtaleModelTopology B S hS X.1)
      CommRingCat.{u}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Equivalence.sheafCongr (SmallEtale.topology B S hS X.1)
      (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)
        CommRingCat.{u}).unitIso.symm _ ≪≫
    Functor.leftUnitor _

end Points

/-! ### Stalks of inverse images on the model -/

section InverseImage

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The inverse image of sheaves of commutative rings along the transported morphism of `f` is
the restriction to the model of the inverse image along `f`. -/
def modelInverseImageRingIso :
    Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
        (modelRingedToposHom f).toToposHom ≅
      Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom ⋙
        (smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
          (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1) :=
  Deformation.ToposThickening.RingedToposExtensionProblem.siteTransportInverseImageIso
    (X := smallEtaleRingedTopos B S hS X) (B := smallEtaleRingedTopos B S hS Y)
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)
    (smallEtaleRingedToposHom B S hS f).toToposHom

/-- **Stacks 04K2 on the model.** The stalk at the point of a geometric point `x̄` of `X` of the
inverse image of a sheaf of commutative rings `R` on `Y_et`, along the transported morphism of
`f : X ⟶ Y` from the model of `X_et`, is the stalk of `R` at `f ∘ x̄`, naturally in `R`. -/
def modelInverseImageFiberRingIso (x : GeometricPoint B S hS X.1) :
    Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor.{u, u, u, u, u, u + 1}
        (modelRingedToposHom f).toToposHom ⋙
        (modelSitePoint B S hS X x).sheafFiber (A := CommRingCat.{u}) ≅
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
        (A := CommRingCat.{u}) :=
  Functor.isoWhiskerRight (modelInverseImageRingIso f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (modelRestrictionFiberRingIso B S hS X x) ≪≫
    (smallEtaleInverseImageFiberRingIso B S hS f x).symm

end InverseImage

end AlgebraicGeometry.Space

end
