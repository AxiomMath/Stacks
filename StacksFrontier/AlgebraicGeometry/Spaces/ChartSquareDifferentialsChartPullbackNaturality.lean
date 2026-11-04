module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentPullbackCompMorphism
public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackEquations
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleObjPullbackComposition

/-!
# Composition laws for the chart-square comparison

`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` exhibits the inverse image of
`a^*Ω_{Y/Bb}` to the small étale site of an étale chart space `A` of `Z` as the associated module
of the Zariski cotangent sheaf `r^*Ω_{W/V}` of a chart square of `q`, for a morphism `r` of the
site through which `chartSpace A ⟶ Z ⟶ Y` factors. This file proves two composition laws for the
ingredients of that comparison: the composition law of [Stacks Project, Tag 03LU] for the transport
of the inverse image at an associated module, with the inverse image of an arbitrary morphism in
front, and the compatibility of the Zariski comparison of two pullback cotangent sheaves with the
change of the inner sheaf.

## Main results

* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_map`: [Stacks Project, Tag
  03LU]'s composition law for the transport of the inverse image at an associated module, with the
  inverse image of an arbitrary morphism in front.
* `AlgebraicGeometry.Space.pullbackCotangentCompHom_cotangentSheafIso`: the Zariski comparison
  `Stacks.Smooth.pullbackCotangentCompHom` commutes with the change of the inner sheaf from
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` to `Stacks.Smooth.cotangentSheaf`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {Bb Z Y : AlgebraicSpaces B S hS} {W V : BigFppfOver B S hS}


/-- The Zariski comparison `Stacks.Smooth.pullbackCotangentCompHom` of two pullback cotangent
sheaves commutes with the change of the inner sheaf from
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` to `Stacks.Smooth.cotangentSheaf`. -/
theorem pullbackCotangentCompHom_cotangentSheafIso {X₀ S₀ T₀ T₀' : Scheme.{u}} (g : X₀ ⟶ S₀)
    (r : T₀ ⟶ X₀) (s : T₀' ⟶ T₀) (rr : T₀' ⟶ X₀) (hrr : s ≫ r = rr) :
    (Scheme.Modules.pullback s).map
          ((Scheme.Modules.pullback r).map (Scheme.Hom.cotangentSheafIso g).hom) ≫
        Stacks.Smooth.pullbackCotangentCompHom g r s rr hrr =
      (Scheme.Modules.pullbackComp s r).hom.app (Scheme.Hom.relativeDifferentials g) ≫
        (Scheme.Modules.pullbackCongr hrr).hom.app (Scheme.Hom.relativeDifferentials g) ≫
        (Scheme.Modules.pullback rr).map (Scheme.Hom.cotangentSheafIso g).hom := by
  refine (congrArg (fun z => (Scheme.Modules.pullback s).map
      ((Scheme.Modules.pullback r).map (Scheme.Hom.cotangentSheafIso g).hom) ≫ z)
    (Stacks.Smooth.pullbackCotangentCompHom_eq g r s rr hrr)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (Scheme.Modules.pullbackCongr hrr).hom.app
      (Stacks.Smooth.cotangentSheaf g))
    ((Scheme.Modules.pullbackComp s r).hom.naturality
      (Scheme.Hom.cotangentSheafIso g).hom)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => (Scheme.Modules.pullbackComp s r).hom.app
      (Scheme.Hom.relativeDifferentials g) ≫ z)
    ((Scheme.Modules.pullbackCongr hrr).hom.naturality (Scheme.Hom.cotangentSheafIso g).hom)

/-- The composition law for the transport of the inverse image at an associated module, with the
inverse image of an arbitrary morphism `ξ` into the associated module on `W` in front. -/
theorem representedAssociatedModulePullbackIso_comp_map {T T' : BigFppfOver B S hS}
    (r : T ⟶ W) (ρ : T' ⟶ T) (𝓕 : ((BigFppfOver.toScheme B S hS).obj W).Modules)
    {M : Modules.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2}
    (ξ : M ⟶ (representedSmallEtaleModuleEquivalence B S hS W).functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj W) W.left.property).obj 𝓕)) :
    (modulePullback B S hS (representedSpaceMap B S hS ρ)).map
          ((modulePullback B S hS (representedSpaceMap B S hS r)).map ξ ≫
            (representedAssociatedModulePullbackIso B S hS r
              (relativelyRepresentable_yoneda_map B S hS r) 𝓕).hom) ≫
        (representedAssociatedModulePullbackIso B S hS ρ
            (relativelyRepresentable_yoneda_map B S hS ρ)
            ((Scheme.Modules.pullback (B.inclusion.map r.left)).obj 𝓕)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((Scheme.Modules.pullbackComp (B.inclusion.map ρ.left)
              (B.inclusion.map r.left)).hom.app 𝓕)) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ)
            (representedSpaceMap B S hS r)).hom.app M ≫
        (modulePullback B S hS (representedSpaceMap B S hS ρ ≫
            representedSpaceMap B S hS r)).map ξ ≫
        (representedAssociatedModulePullbackIso B S hS (ρ ≫ r)
          (relativelyRepresentable_yoneda_map B S hS (ρ ≫ r)) 𝓕).hom := by
  exact CategoryTheory.square_of_factorizations
    ((modulePullback B S hS (representedSpaceMap B S hS ρ)).map_comp _ _)
    (representedAssociatedModulePullbackIso_comp B S hS ρ r
      (relativelyRepresentable_yoneda_map B S hS ρ)
      (relativelyRepresentable_yoneda_map B S hS r)
      (relativelyRepresentable_yoneda_map B S hS (ρ ≫ r)) 𝓕)
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ)
      (representedSpaceMap B S hS r)).hom.naturality ξ) rfl

end AlgebraicGeometry.Space

end
