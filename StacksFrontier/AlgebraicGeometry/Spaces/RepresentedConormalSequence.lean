module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceIdealForm
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModel
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule

/-!
# The ideal form of the conormal sequence of representable algebraic spaces

Let `W ⊆ h_{T₀}`, `Z ⊆ h_{T₁}` and `Y ⊆ h_{T₂}` be closed subspaces of algebraic spaces
represented by objects of the big fppf site over a scheme `S`, carried into each other by two
commutative squares over morphisms `g₀ : T₀ ⟶ T₁` and `g₁ : T₁ ⟶ T₂` of the site, and let
`W₀ ⟶ T₀`, `Z₀ ⟶ T₁` and `Y₀ ⟶ T₂` be the corresponding closed immersions of schemes, carried
into each other by commutative squares of schemes.  The sequence of `𝒪`-modules

```
  ι^*g₀^*g₁^*𝓘_Y ⟶ ι^*g₀^*𝓘_Z ⟶ ι^*𝓘_W
```

on `W`, built from the maps of defining ideal sheaves of Stacks 04CP, is short exact as soon as
the corresponding sequence `j^*g₀^*g₁^*I_Y ⟶ j^*g₀^*I_Z ⟶ j^*I_W` of sheaves of modules on the
scheme `W₀` is, `j : W₀ ⟶ T₀` being the closed immersion; both are read after inverse image to
the algebraic space represented by `W₀`.

The proof reads both sequences through the Zariski models
(`AlgebraicGeometry.Space.zariskiModel`): the defining ideal sheaves are the Zariski models of
the ideal sheaves of the closed immersions, the maps of defining ideal sheaves are the Zariski
models of the maps of ideal sheaves
(`AlgebraicGeometry.Space.idealSheafMap_eq_zariskiModel`), and the Zariski models commute with
inverse images (`AlgebraicGeometry.Space.zariskiModelPullbackIso`).  The Zariski model is exact,
which transports short exactness.

## Main results

* `AlgebraicGeometry.Space.shortExact_idealForm_of_scheme`: the statement.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The Zariski model of modules on a representable algebraic space is exact. -/
instance preservesFiniteLimits_zariskiModel (T : BigFppfOver B S hS) :
    PreservesFiniteLimits (zariskiModel B S hS T) := by
  have := _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  have : (structureModulesToModules B S hS
      ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩).IsEquivalence :=
    (structureModulesEquivalence B S hS _).isEquivalence_functor
  have : (representedSmallEtaleModuleEquivalence B S hS T).functor.IsEquivalence :=
    (representedSmallEtaleModuleEquivalence B S hS T).isEquivalence_functor
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
    (@comp_preservesFiniteLimits _ _ _ _ _ _ _ _ ‹_› inferInstance) inferInstance

/-- The Zariski model of modules on a representable algebraic space preserves finite colimits. -/
instance preservesFiniteColimits_zariskiModel (T : BigFppfOver B S hS) :
    PreservesFiniteColimits (zariskiModel B S hS T) :=
  haveI := (zariskiModelAdjunction B S hS T).leftAdjoint_preservesColimits.{0, 0}
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- The Zariski model of modules on a representable algebraic space preserves zero morphisms. -/
instance preservesZeroMorphisms_zariskiModel (T : BigFppfOver B S hS) :
    (zariskiModel B S hS T).PreservesZeroMorphisms :=
  haveI := (zariskiModelAdjunction B S hS T).isLeftAdjoint
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

section Sequence

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

variable {T₀ T₁ T₂ : BigFppfOver B S hS} (g₀ : T₀ ⟶ T₁) (g₁ : T₁ ⟶ T₂)
  (W : ClosedSubspaces B S hS (yoneda.obj T₀)) (Z : ClosedSubspaces B S hS (yoneda.obj T₁))
  (Y : ClosedSubspaces B S hS (yoneda.obj T₂))
  (f₀ : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (f₁ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
  (sq₀ : subspaceInclusion B S hS
      ⟨yoneda.obj T₀, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₀⟩ W ≫
        representedSpaceMap B S hS g₀ =
      f₀ ≫ subspaceInclusion B S hS
        ⟨yoneda.obj T₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₁⟩ Z)
  (sq₁ : subspaceInclusion B S hS
      ⟨yoneda.obj T₁, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₁⟩ Z ≫
        representedSpaceMap B S hS g₁ =
      f₁ ≫ subspaceInclusion B S hS
        ⟨yoneda.obj T₂, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T₂⟩ Y)
  (f₀' : (BigFppfOver.toScheme B S hS).obj (W.2.2.rep.pullback (idEtaleChart B S hS T₀).1.hom) ⟶
    (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback (idEtaleChart B S hS T₁).1.hom))
  (comm₀ : zariskiClosedImmersion B S hS T₀ W ≫ idChartSchemeHom B S hS g₀ =
    f₀' ≫ zariskiClosedImmersion B S hS T₁ Z)
  (f₁' : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback (idEtaleChart B S hS T₁).1.hom) ⟶
    (BigFppfOver.toScheme B S hS).obj (Y.2.2.rep.pullback (idEtaleChart B S hS T₂).1.hom))
  (comm₁ : zariskiClosedImmersion B S hS T₁ Z ≫ idChartSchemeHom B S hS g₁ =
    f₁' ≫ zariskiClosedImmersion B S hS T₂ Y)

include sq₀ sq₁ comm₀ comm₁ in
/-- **The ideal form of the conormal sequence of closed subspaces of representable algebraic
spaces is short exact when that of the corresponding closed immersions of schemes is.** -/
theorem shortExact_idealForm_of_scheme
    (h : ∃ h : (RingedSpaceModuleAdjunction.modulePullback
          (zariskiClosedImmersion B S hS T₀ W).toLRSHom.toShHom).map
          ((RingedSpaceModuleAdjunction.modulePullback
            (idChartSchemeHom B S hS g₀).toLRSHom.toShHom).map
            (Stacks.ClosedImmersion.idealSheafMap
              (zariskiClosedImmersion_toShHom_square B S hS g₁ Z Y f₁' comm₁))) ≫
        (RingedSpaceModuleAdjunction.modulePullback
          (zariskiClosedImmersion B S hS T₀ W).toLRSHom.toShHom).map
          (Stacks.ClosedImmersion.idealSheafMap
            (zariskiClosedImmersion_toShHom_square B S hS g₀ W Z f₀' comm₀)) = 0,
      (ShortComplex.mk _ _ h).ShortExact) :
    ∃ h : (modulePullback B S hS
          (representedSpaceMap B S hS (representedClosedHom B S hS T₀ W))).map
          ((modulePullback B S hS (representedSpaceMap B S hS g₀)).map
            (representedIdealSheafMap B S hS g₁ Z Y f₁ sq₁)) ≫
        (modulePullback B S hS
          (representedSpaceMap B S hS (representedClosedHom B S hS T₀ W))).map
          (representedIdealSheafMap B S hS g₀ W Z f₀ sq₀) = 0,
      (ShortComplex.mk _ _ h).ShortExact :=
  (ShortComplex.exists_shortExact_mk_iff_of_comparison _ _ _ _
    (definingIdealSheafZariskiModelIso B S hS T₂ Y) (definingIdealSheafZariskiModelIso B S hS T₁ Z)
    (definingIdealSheafZariskiModelIso B S hS T₀ W)
    (zariskiModelPullbackIso B S hS g₁ (relativelyRepresentable_yoneda_map B S hS g₁))
    (zariskiModelPullbackIso B S hS g₀ (relativelyRepresentable_yoneda_map B S hS g₀))
    (zariskiModelPullbackIso B S hS (representedClosedHom B S hS T₀ W)
      (relativelyRepresentable_yoneda_map B S hS _))
    (idealSheafMap_eq_zariskiModel B S hS g₁ (relativelyRepresentable_yoneda_map B S hS g₁) Z Y
      f₁ sq₁ f₁' comm₁)
    (idealSheafMap_eq_zariskiModel B S hS g₀ (relativelyRepresentable_yoneda_map B S hS g₀) W Z
      f₀ sq₀ f₀' comm₀)).mpr
    (ShortComplex.exists_shortExact_mk_map (zariskiModel B S hS _) _ _ h)

end Sequence

end AlgebraicGeometry.Space

end
