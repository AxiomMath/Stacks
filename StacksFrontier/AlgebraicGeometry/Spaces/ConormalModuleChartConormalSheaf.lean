module

public import StacksFrontier.AlgebraicGeometry.Conormal.IdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafMapComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleAmbientChartAnchoring

/-!
# The conormal module of a closed subspace is the scheme conormal sheaf on a chart

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S` contained in a big fppf
site `B`, and let `U` be an étale scheme chart of `X`.  The base change `Z ×_X U ⟶ U` is a closed
immersion of **schemes** (`AlgebraicGeometry.Space.chartBaseChangeHom`), and
`AlgebraicGeometry.Space.chartBaseChangeToSubspaceHom` is the resulting chart `h_{Z ×_X U} ⟶ Z` of
the subspace.

This file identifies the inverse image along that chart of the conormal module `𝒞_{Z/X}` of
[Stacks Project, Tag 04CN] with `ε^*` of the conormal sheaf
`Stacks.ClosedImmersion.conormalSheaf` of the closed immersion of schemes `Z ×_X U ⟶ U`, in the
factorised spelling `Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom` that
`Stacks.Immersion.immersionConormalSheafMap` has as its **target**.  At the level of ideal
sheaves, the identifications on the ambient chart and on a chart of a closed subspace are
expressed through the map of [Stacks Project, Tag 04CP].

## Main definitions

All names are in the namespace `AlgebraicGeometry.Space`.

* `chartModulePullbackDefiningIdealSheafIsoIdealSheaf`: the inverse image of the defining ideal
  sheaf of [Stacks Project, Tag 03MB] along an étale scheme chart of the ambient space is `ε^*` of
  the ideal sheaf of [Stacks Project, Tag 01C2] of the closed immersion of schemes
  `Z ×_X U ⟶ U`.
* `modulePullbackConormalModuleChartConormalSheafIso`: **the inverse image of the conormal module
  of a closed subspace along the chart of it cut out by an étale scheme chart of the ambient space
  is `ε^*` of the conormal sheaf of the closed immersion of schemes `Z ×_X U ⟶ U`.**
* `modulePullbackSubspaceChartDefiningIdealSheafIsoIdealSheaf`: the inverse image of `𝓘_Z` along
  a chart of a closed subspace `Y ⊆ X` cut out by a chart of `X` is `ε^*` of the ideal sheaf of
  the closed immersion of schemes `Z ×_X U ⟶ U`.

## Main results

* `ker_chartBaseChangeHom_eq_schemeSpaceIdeal`: the kernel of the closed immersion of schemes
  `Z ×_X U ⟶ U` is the sheaf of ideals that the inverse image of `Z` cuts out on the chart
  scheme.
* `chartModulePullbackDefiningIdealSheafIsoIdealSheaf_hom_comp_idealSheafι`: against `ε^*` of the
  inclusion of the ideal sheaf into the structure sheaf, the ideal-sheaf identification on the
  ambient chart is `chartModulePullbackDefiningIdealSheafIso` against `ε^*` of the inclusion of
  the submodule.
* `chartModulePullbackDefiningIdealSheafIsoIdealSheaf_hom_eq_idealSheafMap`: that identification
  is the map `φ^*𝓘_Z ⟶ 𝓘_{φ^{-1}Z}` of [Stacks Project, Tag 04CP] along the étale chart
  `φ : h_U ⟶ X`, transported along `representedDefiningIdealSheafIso` and the second factor.
* `modulePullbackSubspaceChartDefiningIdealSheafIsoIdealSheaf_hom_eq_idealSheafMap`: the
  identification on a chart of a closed subspace is the comparison of functors of
  [Stacks Project, Tag 03LU] at `𝓘_Z` followed by the inverse image of that same map of
  [Stacks Project, Tag 04CP].

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module of a
  closed subspace of an algebraic space.
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2), the conormal sheaf of an
  immersion of schemes.
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2), the ideal sheaf of a
  closed immersion of ringed spaces.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal
  sheaf.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the comparison `ε`.
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The forward map of `e ≪≫ F.mapIso i` is `e.hom ≫ F.map j` once `i.hom = j`. -/
private theorem trans_mapIso_hom_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P : D} {Q R : C} (e : P ≅ F.obj Q) (i : Q ≅ R) (j : Q ⟶ R) (h : i.hom = j) :
    (e ≪≫ F.mapIso i).hom = e.hom ≫ F.map j := by
  subst h
  rfl

/-! ### The sheaf of ideals of the chart is the kernel of the closed immersion -/

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (U : SmallEtale B S hS X.1)

/-- **The kernel of the closed immersion of schemes `Z ×_X U ⟶ U` is the sheaf of ideals that the
inverse image of `Z` cuts out on the chart scheme.** -/
theorem ker_chartBaseChangeHom_eq_schemeSpaceIdeal :
    (chartBaseChangeHom B S hS X Z U).ker =
      schemeSpaceIdeal B S hS U.1.left
        ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
          isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
            (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :=
  (schemeSpaceIdeal_eq_ker_of_range_eq B S hS U.1.left _ (Z.2.2.rep.snd U.1.hom)
    (preimage_eq_range_rep_snd B S hS X Z U.1.left U.1.hom).symm).symm

/-! ### The defining ideal sheaf on the ambient chart -/

/-- **The inverse image of the defining ideal sheaf of a closed subspace along an étale scheme
chart of the ambient space is `ε^*` of the ideal sheaf, in the sense of
[Stacks Project, Tag 01C2], of the closed immersion of schemes `Z ×_X U ⟶ U`.**

It is `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso`, to `ε^*` of the sheaf
of ideals `AlgebraicGeometry.Space.schemeSpaceIdeal` of the inverse-image subspace read as a
submodule of the structure sheaf, followed by `ε^*` of
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq` at
`AlgebraicGeometry.Space.ker_chartBaseChangeHom_eq_schemeSpaceIdeal`. -/
def chartModulePullbackDefiningIdealSheafIsoIdealSheaf :
    (modulePullback B S hS (chartToSchemeSpace B S hS X U)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      (representedAssociatedModule B S hS U.1.left
          (isAlgebraicSpace_yoneda B S hS U.1.left)).obj
        (Stacks.ClosedImmersion.idealSheaf
          (chartBaseChangeHom B S hS X Z U).toLRSHom.toShHom) :=
  chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
      (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
      (isEtale_chartToSchemeSpace B S hS X U) ≪≫
    (representedAssociatedModule B S hS U.1.left
        (isAlgebraicSpace_yoneda B S hS U.1.left)).mapIso
      (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq _
        (chartBaseChangeHom B S hS X Z U)
        (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U))

/-! ### The ideal-sheaf identification and the map of [Stacks Project, Tag 04CP] -/

/-- **The identification of the defining ideal sheaf on the ambient chart is the canonical one.**
Composed with `ε^*` of the inclusion of the ideal sheaf of the closed immersion of schemes
`Z ×_X U ⟶ U` into the structure sheaf,
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIsoIdealSheaf` is
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso` composed with `ε^*` of the
inclusion of the submodule `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`. -/
theorem chartModulePullbackDefiningIdealSheafIsoIdealSheaf_hom_comp_idealSheafι :
    (chartModulePullbackDefiningIdealSheafIsoIdealSheaf B S hS Z U).hom ≫
        (representedAssociatedModule B S hS U.1.left
            (isAlgebraicSpace_yoneda B S hS U.1.left)).map
          (Stacks.ClosedImmersion.idealSheafι
            (chartBaseChangeHom B S hS X Z U).toLRSHom.toShHom) =
      (chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
            (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
            (isEtale_chartToSchemeSpace B S hS X U)).hom ≫
        (representedAssociatedModule B S hS U.1.left
            (isAlgebraicSpace_yoneda B S hS U.1.left)).map
          (_root_.AlgebraicGeometry.SheafOfModules.Submodule.ιModules
            (schemeSpaceIdeal B S hS U.1.left
              ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
                isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
                  (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩).unitSubmodule) := by
  have hiso : chartModulePullbackDefiningIdealSheafIsoIdealSheaf B S hS Z U =
      chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
          (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
          (isEtale_chartToSchemeSpace B S hS X U) ≪≫
        (representedAssociatedModule B S hS U.1.left
            (isAlgebraicSpace_yoneda B S hS U.1.left)).mapIso
          (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq
            (schemeSpaceIdeal B S hS U.1.left
              ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
                isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
                  (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩)
            (chartBaseChangeHom B S hS X Z U)
            (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U)) :=
    rfl
  have hhom := (congrArg (fun i => Iso.hom i) hiso).trans
    (Iso.trans_hom
      (chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
        (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
        (isEtale_chartToSchemeSpace B S hS X U))
      ((representedAssociatedModule B S hS U.1.left
          (isAlgebraicSpace_yoneda B S hS U.1.left)).mapIso
        (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq
          (schemeSpaceIdeal B S hS U.1.left
            ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
              isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
                (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩)
          (chartBaseChangeHom B S hS X Z U)
          (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U))))
  have hassoc := Category.assoc
    (chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
      (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
      (isEtale_chartToSchemeSpace B S hS X U)).hom
    ((representedAssociatedModule B S hS U.1.left
        (isAlgebraicSpace_yoneda B S hS U.1.left)).mapIso
      (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq
        (schemeSpaceIdeal B S hS U.1.left
          ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩)
        (chartBaseChangeHom B S hS X Z U)
        (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U))).hom
    ((representedAssociatedModule B S hS U.1.left
        (isAlgebraicSpace_yoneda B S hS U.1.left)).map
      (Stacks.ClosedImmersion.idealSheafι
        (chartBaseChangeHom B S hS X Z U).toLRSHom.toShHom))
  have hmc := ((representedAssociatedModule B S hS U.1.left
      (isAlgebraicSpace_yoneda B S hS U.1.left)).map_comp
    (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq
      (schemeSpaceIdeal B S hS U.1.left
        ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
          isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
            (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩)
      (chartBaseChangeHom B S hS X Z U)
      (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U)).hom
    (Stacks.ClosedImmersion.idealSheafι
      (chartBaseChangeHom B S hS X Z U).toLRSHom.toShHom)).symm
  have hs := congrArg (representedAssociatedModule B S hS U.1.left
      (isAlgebraicSpace_yoneda B S hS U.1.left)).map
    (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq_hom_comp_idealSheafι
      (schemeSpaceIdeal B S hS U.1.left
        ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
          isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
            (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩)
      (chartBaseChangeHom B S hS X Z U)
      (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U))
  exact (congrArg (fun t => t ≫ (representedAssociatedModule B S hS U.1.left
        (isAlgebraicSpace_yoneda B S hS U.1.left)).map
      (Stacks.ClosedImmersion.idealSheafι
        (chartBaseChangeHom B S hS X Z U).toLRSHom.toShHom)) hhom).trans
    (hassoc.trans (congrArg (fun t =>
      (chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
        (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
        (isEtale_chartToSchemeSpace B S hS X U)).hom ≫ t) (hmc.trans hs)))

/-- **The chart identification of the defining ideal sheaf with the scheme-level ideal sheaf is
the map `φ^*𝓘_Z ⟶ 𝓘_{φ^{-1}Z}` of [Stacks Project, Tag 04CP], transported.**  For the étale
scheme chart `φ : h_U ⟶ X` of the ambient space,
`AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIsoIdealSheaf` is that map followed
by `AlgebraicGeometry.Space.representedDefiningIdealSheafIso` and `ε^*` of the scheme-level
comparison of [Stacks Project, Tag 03MB] with [Stacks Project, Tag 01C2]. -/
theorem chartModulePullbackDefiningIdealSheafIsoIdealSheaf_hom_eq_idealSheafMap
    (f : (⟨(⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
        isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
          (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
        ClosedSubspaces B S hS
          (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
            AlgebraicSpaces B S hS).1).1.toFunctor,
      (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
        isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
          (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
        ClosedSubspaces B S hS
          (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
            AlgebraicSpaces B S hS).1).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS
          ⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩
          (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
            ClosedSubspaces B S hS
              (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
                AlgebraicSpaces B S hS).1) ≫ chartToSchemeSpace B S hS X U =
        f ≫ subspaceInclusion B S hS X Z) :
    (chartModulePullbackDefiningIdealSheafIsoIdealSheaf B S hS Z U).hom =
      idealSheafMap B S hS
          (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
            ClosedSubspaces B S hS
              (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
                AlgebraicSpaces B S hS).1)
          Z (chartToSchemeSpace B S hS X U) f hsq ≫
        (representedDefiningIdealSheafIso B S hS U.1.left
            (isAlgebraicSpace_yoneda B S hS U.1.left)
            (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
              isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
                (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
              ClosedSubspaces B S hS
                (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
                  AlgebraicSpaces B S hS).1)).inv ≫
          (representedAssociatedModule B S hS U.1.left
              (isAlgebraicSpace_yoneda B S hS U.1.left)).map
            (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq
              (schemeSpaceIdeal B S hS U.1.left
                ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
                  isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
                    (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩)
              (chartBaseChangeHom B S hS X Z U)
              (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U)).hom := by
  refine (trans_mapIso_hom_eq (representedAssociatedModule B S hS U.1.left
      (isAlgebraicSpace_yoneda B S hS U.1.left))
    (chartModulePullbackDefiningIdealSheafIso B S hS Z U.1.left
      (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
      (isEtale_chartToSchemeSpace B S hS X U)) _ _ rfl).trans ?_
  rw [chartModulePullbackDefiningIdealSheafIso_hom_eq_idealSheafMap B S hS Z U.1.left
      (isAlgebraicSpace_yoneda B S hS U.1.left) (chartToSchemeSpace B S hS X U)
      (isEtale_chartToSchemeSpace B S hS X U) f hsq]
  exact Category.assoc _ _ _

/-! ### The chart identification -/

/-- **The inverse image of the conormal module of a closed subspace along the chart of it cut out
by an étale scheme chart of the ambient space is `ε^*` of the conormal sheaf of the closed
immersion of schemes `Z ×_X U ⟶ U`**, in the factorised spelling that
`Stacks.Immersion.immersionConormalSheafMap` has as its target.

It is `AlgebraicGeometry.Space.modulePullbackConormalModuleChartZariskiIso`, to `ε^*` of the
Zariski pullback of the sheaf of ideals of the inverse-image subspace, followed by
`AlgebraicGeometry.Scheme.IdealSheafData.modulePullbackUnitSubmoduleIsoConormalSheafOfKerEq` at
the kernel equation `AlgebraicGeometry.Space.ker_chartBaseChangeHom_eq_schemeSpaceIdeal`. -/
def modulePullbackConormalModuleChartConormalSheafIso :
    (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Z U)).obj
        (conormalModule B S hS X Z) ≅
      (representedAssociatedModule B S hS (Z.2.2.rep.pullback U.1.hom)
          (isAlgebraicSpace_yoneda B S hS (Z.2.2.rep.pullback U.1.hom))).obj
        (Stacks.ClosedImmersion.conormalSheaf
          (chartBaseChangeHom B S hS X Z U).liftCoborder.toLRSHom.toShHom) :=
  modulePullbackConormalModuleChartZariskiIso B S hS Z U ≪≫
    (representedAssociatedModule B S hS (Z.2.2.rep.pullback U.1.hom)
        (isAlgebraicSpace_yoneda B S hS (Z.2.2.rep.pullback U.1.hom))).mapIso
      (Scheme.IdealSheafData.modulePullbackUnitSubmoduleIsoConormalSheafOfKerEq _
        (chartBaseChangeHom B S hS X Z U)
        (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U))

/-! ### The source of the chart reading of the conormal map -/

/-- **The inverse image of the defining ideal sheaf of `Z ⊆ X` along a chart of a closed
subspace `Y ⊆ X` cut out by a chart of `X` is `ε^*` of the ideal sheaf of
[Stacks Project, Tag 01C2] of the closed immersion of schemes `Z ×_X U ⟶ U`.**

It is the comparison of functors `AlgebraicGeometry.Space.conormalModuleChartCompIso`, along the
factorisation `AlgebraicGeometry.Space.chartBaseChangeToSubspace_comp_subspaceInclusion` of the
composite `Y ×_X U ⟶ Y ⟶ X` through the chart `U` of `X`, evaluated at `𝓘_Z`, followed by the
inverse image of `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIsoIdealSheaf`. -/
def modulePullbackSubspaceChartDefiningIdealSheafIsoIdealSheaf
    (Y : ClosedSubspaces B S hS X.1) :
    (modulePullback B S hS (chartBaseChangeToSubspaceHom B S hS Y U)).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Y)).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≅
      (modulePullback B S hS (schemeSpaceMap (Y.2.2.rep.snd U.1.hom))).obj
        ((representedAssociatedModule B S hS U.1.left
            (isAlgebraicSpace_yoneda B S hS U.1.left)).obj
          (Stacks.ClosedImmersion.idealSheaf
            (chartBaseChangeHom B S hS X Z U).toLRSHom.toShHom)) :=
  (conormalModuleChartCompIso B S hS Y U).app
      (definingIdealSheaf B S hS X Z).toSheafOfModules ≪≫
    (modulePullback B S hS (schemeSpaceMap (Y.2.2.rep.snd U.1.hom))).mapIso
      (chartModulePullbackDefiningIdealSheafIsoIdealSheaf B S hS Z U)

/-- **The identification
`AlgebraicGeometry.Space.modulePullbackSubspaceChartDefiningIdealSheafIsoIdealSheaf` is the
comparison of functors of [Stacks Project, Tag 03LU] at `𝓘_Z`, followed by the inverse image
along `Y ×_X U ⟶ U` of the map `φ^*𝓘_Z ⟶ 𝓘_{φ^{-1}Z}` of [Stacks Project, Tag 04CP] on the
ambient chart, transported.** -/
theorem modulePullbackSubspaceChartDefiningIdealSheafIsoIdealSheaf_hom_eq_idealSheafMap
    (Y : ClosedSubspaces B S hS X.1)
    (f : (⟨(⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
        ClosedSubspaces B S hS
          (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
            AlgebraicSpaces B S hS).1).1.toFunctor,
      (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
        ClosedSubspaces B S hS
          (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
            AlgebraicSpaces B S hS).1).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS
          ⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩
          (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
            ClosedSubspaces B S hS
              (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
                AlgebraicSpaces B S hS).1) ≫ chartToSchemeSpace B S hS X U =
        f ≫ subspaceInclusion B S hS X Z) :
    (modulePullbackSubspaceChartDefiningIdealSheafIsoIdealSheaf B S hS Z U Y).hom =
      ((conormalModuleChartCompIso B S hS Y U).app
            (definingIdealSheaf B S hS X Z).toSheafOfModules).hom ≫
        (modulePullback B S hS (schemeSpaceMap (Y.2.2.rep.snd U.1.hom))).map
          (idealSheafMap B S hS
              (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
                ClosedSubspaces B S hS
                  (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
                    AlgebraicSpaces B S hS).1)
              Z (chartToSchemeSpace B S hS X U) f hsq ≫
            (representedDefiningIdealSheafIso B S hS U.1.left
                (isAlgebraicSpace_yoneda B S hS U.1.left)
                (⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
            isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
              (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩ :
                  ClosedSubspaces B S hS
                    (⟨yoneda.obj U.1.left, isAlgebraicSpace_yoneda B S hS U.1.left⟩ :
                      AlgebraicSpaces B S hS).1)).inv ≫
              (representedAssociatedModule B S hS U.1.left
                  (isAlgebraicSpace_yoneda B S hS U.1.left)).map
                (Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq
                  (schemeSpaceIdeal B S hS U.1.left
                    ⟨Z.1.preimage (chartToSchemeSpace B S hS X U).hom,
                      isClosedSubspace_preimage B S hS (chartToSchemeSpace B S hS X U).hom Z.1 X.2
                        (isAlgebraicSpace_yoneda B S hS U.1.left) Z.2⟩)
                  (chartBaseChangeHom B S hS X Z U)
                  (ker_chartBaseChangeHom_eq_schemeSpaceIdeal B S hS Z U)).hom) := by
  exact trans_mapIso_hom_eq (modulePullback B S hS (schemeSpaceMap (Y.2.2.rep.snd U.1.hom)))
    ((conormalModuleChartCompIso B S hS Y U).app
      (definingIdealSheaf B S hS X Z).toSheafOfModules) _ _
    (chartModulePullbackDefiningIdealSheafIsoIdealSheaf_hom_eq_idealSheafMap B S hS Z U f hsq)

end AlgebraicGeometry.Space

end
