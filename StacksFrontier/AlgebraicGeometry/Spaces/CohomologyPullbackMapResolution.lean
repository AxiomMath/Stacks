module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.Homology.CompositeCollapseResolution
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdgeAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityFlatInjection

/-!
# The pullback map on cohomology, on injective resolutions

For a flat affine morphism `f : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_Y`-module `𝓖`,
`AlgebraicGeometry.Space.cohomologyPullbackMap` is the map `H^i(Y, 𝓖) ⟶ H^i(X, f^*𝓖)` that part (2)
of **Stacks 073K** extends scalars of.  It is built from three chosen identifications: the collapse
`R^i(Γ(Y, −) ∘ f_*) ≅ R^iΓ(Y, f_*−)` of **Stacks 0733**, the derived form of **Stacks 0732**, and
the extraction of the exact restriction of scalars from a right derived functor.  This file
computes it on injective resolutions: read through an injective resolution `I` of `𝓖` and the
chosen injective resolution `J` of `f^*𝓖`, it is the cohomology of the morphism of complexes

`Γ(Y, I) ⟶ Γ(Y, f_*J) ⟶ Γ(X, J)`

given by a lift `γ : I ⟶ f_*J` of the unit `𝓖 ⟶ f_*f^*𝓖` and the comparison of **Stacks 0732**,
followed by the comparison of the exact restriction of scalars with cohomology.

## Main results

* `AlgebraicGeometry.Space.isoRightDerivedObj_inv_comp_cohomologyPullbackMap`

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.RightDerivedCoEdge (homologyToMapHomology)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

attribute [local instance 10000] spaceModulesAbelianWrittenOut
attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules


/-- **The pullback map on cohomology, on injective resolutions.** -/
theorem isoRightDerivedObj_inv_comp_cohomologyPullbackMap (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite)
    (γ : (injectiveResolution G).cocomplex ⟶
      ((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution ((modulePullback B S hS f).obj G)).cocomplex)
    (hγ : (injectiveResolution G).ι.f 0 ≫ γ.f 0 =
      (modulePullbackAdjunction B S hS f).unit.app G ≫
        (modulePushforward B S hS f).map
          ((injectiveResolution ((modulePullback B S hS f).obj G)).ι.f 0)) (n : ℕ) :
    ((injectiveResolution G).isoRightDerivedObj (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) n).inv ≫
        cohomologyPullbackMap B S hS f haff hflat G hG n =
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).mapHomologicalComplex
              (ComplexShape.up ℕ)).map γ) ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex (globalSectionsPushforwardIsoSite B S hS f).hom
            (ComplexShape.up ℕ)).app
              (injectiveResolution ((modulePullback B S hS f).obj G)).cocomplex) ≫
        (Stacks.DerivedIndexing.mapExactHomologyIso (globalSectionsRestrictScalars B S hS f)
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj
                (injectiveResolution ((modulePullback B S hS f).obj G)).cocomplex) n).hom ≫
        (globalSectionsRestrictScalars B S hS f).map
          ((injectiveResolution ((modulePullback B S hS f).obj G)).isoRightDerivedObj
            (globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) n).inv := by
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
  have hZ := fun n hn => isZero_rightDerived_modulePushforward_of_chartwise B S hS f
    (relativelyRepresentable_of_isAffineHom B S hS f haff) ((modulePullback B S hS f).obj G) n
    (chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f haff
      (relativelyRepresentable_of_isAffineHom B S hS f haff) _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG) n hn)
  have hA := Stacks.RightDerivedComp.isoRightDerivedObj_inv_comp_map_comp_objIsoOfAcyclicImage_inv
    (modulePushforward B S hS f) (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    hZ (acyclicPushforwardOfInjective_of_isFlat B S hS f hflat) (injectiveResolution G)
    ((modulePullbackAdjunction B S hS f).unit.app G) γ hγ n
  have hB := InjectiveResolution.rightDerived_app_eq (globalSectionsPushforwardIsoSite B S hS f).hom
    (injectiveResolution ((modulePullback B S hS f).obj G)) n
  have hC := Stacks.RightDerivedComp.isoRightDerivedObj_inv_comp_rightDerivedCompIso_hom_app
    (globalSectionsFunctor.{u + 1, u, u, u} (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (globalSectionsRestrictScalars B S hS f) n ((modulePullback B S hS f).obj G)
  have e1 : cohomologyPullbackMap B S hS f haff hflat G hG n =
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived n).map
          ((modulePullbackAdjunction B S hS f).unit.app G) ≫
        (Stacks.RightDerivedComp.objIsoOfAcyclicImage (modulePushforward B S hS f)
          (globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          hZ (acyclicPushforwardOfInjective_of_isFlat B S hS f hflat) n).inv ≫
        (NatTrans.rightDerived (globalSectionsPushforwardIsoSite B S hS f).hom n).app
          ((modulePullback B S hS f).obj G) ≫
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerivedCompIso
            (globalSectionsRestrictScalars B S hS f) n).hom.app
          ((modulePullback B S hS f).obj G) :=
    rfl
  refine (congrArg (((injectiveResolution G).isoRightDerivedObj
    (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) n).inv ≫ ·) e1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((Category.assoc _ _ _).trans hA)).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((congrArg (_ ≫ ·) hB).trans (Iso.inv_hom_id_assoc _ _))).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC)

end AlgebraicGeometry.Space

end
