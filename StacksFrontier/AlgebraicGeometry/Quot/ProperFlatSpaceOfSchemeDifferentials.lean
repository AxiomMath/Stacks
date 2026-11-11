module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceOfScheme
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesChartDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsRepresented
public import StacksFrontier.Cotangent.Spaces.ModelCotangentHomologyZero

/-!
# The sheaf of differentials at the point given by a proper flat scheme over a field

Let `k` be a field with `Spec k` in a big fppf site `B`, and let `f : X ⟶ Spec k` be a flat,
proper morphism of finite presentation, giving the object
`AlgebraicGeometry.ProperFlatSpaceOfScheme.point` of `Spaces'_{fp, flat, proper}` over `Spec k`.
The deformation theory of the stack at this point uses the structure morphism of its chart,
`AlgebraicGeometry.Space.ProperFlatLift.chartStructureMap`, a morphism of algebraic spaces from
`X` to `Spec k`. This file identifies it with the morphism of represented algebraic spaces given by
`f` (`AlgebraicGeometry.ProperFlatSpaceOfScheme.chartStructureMap_point_eq`), so that its sheaf of
differentials is the étale module associated to the Zariski sheaf `Ω_{X/k}` (Stacks 04CS), and,
by `AlgebraicGeometry.Space.modelCotangentHomologyZeroIso`, so is `H⁰` of its cotangent complex
on the model of the small étale site of `X`.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.sheafOfDifferentialsChartStructureMapPointIso`:
  `Ω` of the chart structure map is the étale module of `Ω_{X/k}`.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.cotangentHomologyZeroChartStructureMapPointIso`:
  `H⁰` of the cotangent complex of the chart structure map is the étale module of `Ω_{X/k}`,
  carried to the model.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.chartStructureMap_point_eq`: the chart structure
  map at the point is the morphism of represented algebraic spaces given by `f`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 08UR](https://stacks.math.columbia.edu/tag/08UR)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
  AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

namespace AlgebraicGeometry.ProperFlatSpaceOfScheme

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **The chart structure map at the point is the morphism of represented algebraic spaces given
by `f`**: the structure morphism of the family `point B k hk f` is `yoneda.map` of
`toBaseObj B k hk f`, and the identification of its base with `Spec k` is the identity. -/
theorem chartStructureMap_point_eq :
    Space.ProperFlatLift.chartStructureMap (point B k hk f)
        (ProperFlatSpaceDeformation.obj_eq_specialFibre (point B k hk f)
          (projection_point B k hk f)) =
      schemeSpaceMap (toBaseObj B k hk f) := by
  change commaHomAsSpaceMap _ ≫ (schemeSpaceFunctor B (Spec (.of k)) hk).map (eqToHom rfl) = _
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- **The sheaf of differentials of the chart structure map at the point is the étale module of
`Ω_{X/k}`** (Stacks 04CS for the morphism of represented algebraic spaces given by `f`). -/
def sheafOfDifferentialsChartStructureMapPointIso :
    Space.sheafOfDifferentials B (Spec (.of k)) hk
        (Space.ProperFlatLift.chartStructureMap (point B k hk f)
          (ProperFlatSpaceDeformation.obj_eq_specialFibre (point B k hk f)
            (projection_point B k hk f))) ≅
      (Space.representedAssociatedModule B (Spec (.of k)) hk (siteObj B k hk f)
        (isAlgebraicSpace_yoneda _ _ _ _)).obj (Scheme.Hom.relativeDifferentials f) :=
  eqToIso (congrArg (fun g => Space.sheafOfDifferentials B (Spec (.of k)) hk g)
      (chartStructureMap_point_eq B k hk f)) ≪≫
    Space.sheafOfDifferentialsRepresentedIso B (Spec (.of k)) hk (toBaseObj B k hk f)

/-- **`H⁰` of the cotangent complex of the chart structure map at the point is the étale module
of `Ω_{X/k}`**, carried to the model of the small étale site of `X`: Stacks 08UR on the model
(`AlgebraicGeometry.Space.modelCotangentHomologyZeroIso`) followed by
`sheafOfDifferentialsChartStructureMapPointIso`. -/
def cotangentHomologyZeroChartStructureMapPointIso :
    (Space.modelRingedToposHom (Space.ProperFlatLift.chartStructureMap (point B k hk f)
        (ProperFlatSpaceDeformation.obj_eq_specialFibre (point B k hk f)
          (projection_point B k hk f)))).cotangentComplex.homology 0 ≅
      (Space.smallEtaleModelModulesEquiv B (Spec (.of k)) hk
          (point B k hk f).obj.obj.left).functor.obj
        ((Space.representedAssociatedModule B (Spec (.of k)) hk (siteObj B k hk f)
          (isAlgebraicSpace_yoneda _ _ _ _)).obj (Scheme.Hom.relativeDifferentials f)) :=
  Space.modelCotangentHomologyZeroIso B (Spec (.of k)) hk _ ≪≫
    (Space.smallEtaleModelModulesEquiv B (Spec (.of k)) hk
      (point B k hk f).obj.obj.left).functor.mapIso
        (sheafOfDifferentialsChartStructureMapPointIso B k hk f)

end AlgebraicGeometry.ProperFlatSpaceOfScheme

end
