module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality

/-!
# The map of Stacks 08I3 on algebraic spaces is compatible with composition

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces and `K, L ∈ D(𝒪_Z)`, the map of
Stacks 08I3 for `f ≫ g`,

`c^{f ≫ g} : L(f ≫ g)^*R𝓗om(K, L) ⟶ R𝓗om(L(f ≫ g)^*K, L(f ≫ g)^*L)`,

is, through the compositor `ι : Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D, the composite
`Lf^*(c^g) ≫ c^f` of `Lf^*` of the map for `g` with the map for `f` at `(Lg^*K, Lg^*L)`.

The abstract form is `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_comp`
(the comparison of a composite functor) together with
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_congr'` (invariance under a
monoidal isomorphism of functors); the input of the second is the compatibility of Stacks 07A4
with composition, `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_comp`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomMap_comp`: the composition law.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_comp_iff`: hence the map for
  `f ≫ g` is invertible exactly when `Lf^*(c^g) ≫ c^f` is.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y Z : AlgebraicSpaces B S hS}

/-- **The map of Stacks 08I3 on algebraic spaces is compatible with composition.** For
`f : X ⟶ Y` and `g : Y ⟶ Z`, the map for `f ≫ g` at `(K, L)` is, through the compositor
`ι : Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`, `Lf^*` of the map for `g` followed by the map for `f` at
`(Lg^*K, Lg^*L)`. -/
theorem smallEtaleDerivedPullbackSheafHomMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    smallEtaleDerivedPullbackSheafHomMap (f ≫ g) K L =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).inv.app _ ≫
        (smallEtaleDerivedModulePullback B S hS f).map
          (smallEtaleDerivedPullbackSheafHomMap g K L) ≫
          smallEtaleDerivedPullbackSheafHomMap f ((smallEtaleDerivedModulePullback B S hS g).obj K)
            ((smallEtaleDerivedModulePullback B S hS g).obj L) ≫
            ((smallEtaleDerivedSheafHom B S hS X).map
                ((smallEtaleDerivedModulePullbackCompIso B S hS f g).inv.app K).op).app _ ≫
              ((smallEtaleDerivedSheafHom B S hS X).obj
                  (op ((smallEtaleDerivedModulePullback B S hS (f ≫ g)).obj K))).map
                ((smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app L) := by
  have hcongr := Transpose.homComparison_congr' (smallEtaleDerivedSheafHom B S hS Z)
    (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Z) (smallEtaleTensorHomEquiv B S hS X)
    (Transpose.compTensorIso (smallEtaleDerivedModulePullback B S hS g)
      (smallEtaleDerivedModulePullback B S hS f)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleDerivedPullbackTensorIso g) (smallEtaleDerivedPullbackTensorIso f))
    (smallEtaleDerivedPullbackTensorIso (f ≫ g)) (smallEtaleDerivedModulePullbackCompIso B S hS f g)
    (tensorHomEquivNaturalLeft_smallEtale B S hS X) (tensorHomEquivDinatural_smallEtale B S hS X)
    (tensorHomEquivTargetNatural_smallEtale B S hS X)
    (fun x => (NatTrans.congr_app (smallEtaleDerivedPullbackTensorIso_comp f g) x).trans
      (Category.assoc _ _ _).symm) K L
  have hcomp := Transpose.homComparison_comp (smallEtaleDerivedModulePullback B S hS g)
    (smallEtaleDerivedModulePullback B S hS f) (smallEtaleDerivedSheafHom B S hS Z)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS X)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleTensorHomEquiv B S hS Z) (smallEtaleTensorHomEquiv B S hS Y)
    (smallEtaleTensorHomEquiv B S hS X)
    (smallEtaleDerivedPullbackTensorIso g) (smallEtaleDerivedPullbackTensorIso f)
    (tensorHomEquivNaturalLeft_smallEtale B S hS Y) (tensorHomEquivNaturalLeft_smallEtale B S hS X)
    K L
  refine hcongr.trans ?_
  rw [hcomp]
  simp only [Category.assoc]
  rfl

/-- **The map of Stacks 08I3 for a composite is invertible exactly when `Lf^*(c^g) ≫ c^f` is.** -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_comp_iff (f : X ⟶ Y) (g : Y ⟶ Z)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap (f ≫ g) K L) ↔
      IsIso ((smallEtaleDerivedModulePullback B S hS f).map
          (smallEtaleDerivedPullbackSheafHomMap g K L) ≫
        smallEtaleDerivedPullbackSheafHomMap f ((smallEtaleDerivedModulePullback B S hS g).obj K)
          ((smallEtaleDerivedModulePullback B S hS g).obj L)) := by
  rw [smallEtaleDerivedPullbackSheafHomMap_comp, isIso_comp_left_iff]
  simp only [← Category.assoc]
  rw [isIso_comp_right_iff, isIso_comp_right_iff]

end AlgebraicGeometry.Space

end
