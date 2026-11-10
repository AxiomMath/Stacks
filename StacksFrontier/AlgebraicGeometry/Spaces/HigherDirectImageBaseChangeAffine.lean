module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyPullbackMapResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeGlobalSectionsSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeCanonicalIsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleBaseChangeSpellings
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeHigher
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseTerminalChartIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBasePushforwardInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseHigherDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Algebra.Homology.BaseChangeSquareGlobalSections

/-!
# Stacks 073K, part (1), over affine bases

For the cartesian square of **Stacks 073J** with `Y` and `Y'` affine, `g` flat and `f`
quasi-compact and quasi-separated, the base change map of **Stacks 0736** is invertible at a
quasi-coherent `𝓕` placed in degree zero.

## Implementation notes

The base change map is invertible at `𝓕[0]` as soon as a chosen morphism of complexes
`Q : g^*f_*I ⟶ f'_*J` is a quasi-isomorphism, where `I` is the chosen injective resolution of `𝓕`,
`J` the one of `𝓕' = (g')^*𝓕`, and `Q` is the degree-zero base change map on `I` followed by
`f'_*` of a comparison `(g')^*I ⟶ J`
(`Stacks.Cohomology.BaseChange.isIso_derived_app_single_of_quasiIso_cocomplex`).  In each degree
the induced morphism `g^*Hⁿ(f_*I) ⟶ Hⁿ(f'_*J)` is a morphism of quasi-coherent modules on the
affine `Y'`, so it is invertible as soon as it is on global sections.  On global sections it is
read, through extension of scalars and the isomorphism
`AlgebraicGeometry.Space.isIso_globalSectionsPullbackBaseChange` of global sections of an inverse
image over affine bases, as the comparison map of **Stacks 073K**, part (2),
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap`, which is invertible by
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.RightDerivedCoEdge (homologyToMapHomology unitHomologicalComplex)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-- The identifications of global sections of direct images (**Stacks 0732**) commute with the
comparison of the direct images along the two sides of the square. -/
theorem globalSectionsPushforwardIsoSite_squareComparison_hom
    (N : Modules.{u, u} B S hS D.X'.1 D.X'.2) :
    (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).map
        ((modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w).hom.app N) ≫
      (globalSectionsPushforwardIsoSite B S hS D.g).hom.app
        ((modulePushforward B S hS D.f').obj N) ≫
      (globalSectionsRestrictScalars B S hS D.g).map
        ((globalSectionsPushforwardIsoSite B S hS D.f').hom.app N) =
    (globalSectionsPushforwardIsoSite B S hS D.f).hom.app ((modulePushforward B S hS D.g').obj N) ≫
      (globalSectionsRestrictScalars B S hS D.f).map
        ((globalSectionsPushforwardIsoSite B S hS D.g').hom.app N) ≫
      D.restrictScalarsSquareIso.hom.app ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).obj N) := by
  rw [modulePushforwardSquareComparisonIso_hom]
  exact ModuleCat.hom_ext (LinearMap.ext fun s ↦ by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact globalSectionsPushforwardIsoSite_squareComparison D.f D.g D.f' D.g' D.isPullback.w N s)

/-- **The degreewise square.**  For `ψ : (g')^*𝓚 ⟶ 𝓛`, reading on global sections of `Y'` the unit
of `g^* ⊣ g_*` at `f_*𝓚` followed by the base change map and `f'_*ψ`, and then reading the result
on `X'` through **Stacks 0732**, is reading on `X` through **Stacks 0732** the unit of
`(g')^* ⊣ g'_*` followed by `g'_*ψ`, and then reading the result on `X'`. -/
theorem globalSectionsPushforwardIsoSite_square_component (K : Modules.{u, u} B S hS D.X.1 D.X.2)
    {L : Modules.{u, u} B S hS D.X'.1 D.X'.2} (ψ : (modulePullback B S hS D.g').obj K ⟶ L) :
    (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).map
        ((modulePullbackAdjunction B S hS D.g).unit.app ((modulePushforward B S hS D.f).obj K) ≫
          (modulePushforward B S hS D.g).map
            ((Stacks.Cohomology.BaseChange.mate (modulePullbackAdjunction B S hS D.g)
              (modulePullbackAdjunction B S hS D.g') (modulePushforward B S hS D.f)
              (modulePushforward B S hS D.f')
              (modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w)).app K ≫
              (modulePushforward B S hS D.f').map ψ)) ≫
      (globalSectionsPushforwardIsoSite B S hS D.g).hom.app
        ((modulePushforward B S hS D.f').obj L) ≫
      (globalSectionsRestrictScalars B S hS D.g).map
        ((globalSectionsPushforwardIsoSite B S hS D.f').hom.app L) =
    (globalSectionsPushforwardIsoSite B S hS D.f).hom.app K ≫
      (globalSectionsRestrictScalars B S hS D.f).map
        ((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).map
            ((modulePullbackAdjunction B S hS D.g').unit.app K ≫
            (modulePushforward B S hS D.g').map ψ) ≫
          (globalSectionsPushforwardIsoSite B S hS D.g').hom.app L) ≫
      D.restrictScalarsSquareIso.hom.app ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).obj L) :=
  Stacks.Cohomology.RightDerivedCoEdge.baseChange_square_component
    (modulePullbackAdjunction B S hS D.g) (modulePullbackAdjunction B S hS D.g')
    (modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w)
    (globalSectionsPushforwardIsoSite B S hS D.f) (globalSectionsPushforwardIsoSite B S hS D.g)
    (globalSectionsPushforwardIsoSite B S hS D.f') (globalSectionsPushforwardIsoSite B S hS D.g')
    D.restrictScalarsSquareIso D.globalSectionsPushforwardIsoSite_squareComparison_hom K ψ

section Resolutions

attribute [local instance 10000] spaceModulesAbelianWrittenOut
attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable (hg : IsFlat B S hS D.g.hom)

include hg in
/-- If `g` is flat, then the inverse image along `g'` preserves finite limits. -/
theorem preservesFiniteLimits_pullback_g' :
    PreservesFiniteLimits (modulePullback B S hS D.g') :=
  preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS D.g' (D.isFlat_g' hg)

/-- The augmentation of the pullback of the chosen injective resolution of `𝓕` along `g'` is a
quasi-isomorphism. -/
private theorem quasiIso_mapι_pullback_g' (hg : IsFlat B S hS D.g.hom) :
    QuasiIso (Stacks.RightDerivedComp.mapι (modulePullback B S hS D.g')
      (injectiveResolution D.F)) := by
  have := D.preservesFiniteLimits_pullback_g' hg
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS D.g'
  exact Stacks.RightDerivedComp.quasiIso_mapι (modulePullback B S hS D.g')
    (injectiveResolution D.F)
    (fun n hn ↦ Functor.isZero_rightDerived_of_exact (modulePullback B S hS D.g') D.F n hn)

/-- The comparison `(g')^*I ⟶ J` of the inverse image of the chosen injective resolution `I` of
`𝓕` with the chosen injective resolution `J` of `𝓕' = (g')^*𝓕`: `(g')^*` is exact, so `(g')^*I` is
a resolution of `𝓕'`, and `J` is injective. -/
def resolutionComparison :
    ((modulePullback B S hS D.g').mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution D.F).cocomplex ⟶ (injectiveResolution D.pulledBack).cocomplex :=
  have := D.preservesFiniteLimits_pullback_g' hg
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS D.g'
  have := Stacks.RightDerivedComp.quasiIso_mapι (modulePullback B S hS D.g')
    (injectiveResolution D.F)
    (fun n hn ↦ Functor.isZero_rightDerived_of_exact (modulePullback B S hS D.g') D.F n hn)
  Stacks.RightDerivedComp.descOfResolution
    (Stacks.RightDerivedComp.mapι (modulePullback B S hS D.g') (injectiveResolution D.F))
    (injectiveResolution D.pulledBack)

/-- The comparison `(g')^*I ⟶ J` of injective resolutions is a quasi-isomorphism. -/
theorem quasiIso_resolutionComparison : QuasiIso (D.resolutionComparison hg) := by
  have := D.quasiIso_mapι_pullback_g' hg
  have h := Stacks.RightDerivedComp.comp_descOfResolution
    (Stacks.RightDerivedComp.mapι (modulePullback B S hS D.g') (injectiveResolution D.F))
    (injectiveResolution D.pulledBack)
  have : QuasiIso (Stacks.RightDerivedComp.mapι (modulePullback B S hS D.g')
      (injectiveResolution D.F) ≫ D.resolutionComparison hg) := by
    rw [resolutionComparison, h]; infer_instance
  exact quasiIso_of_comp_left (Stacks.RightDerivedComp.mapι (modulePullback B S hS D.g')
    (injectiveResolution D.F)) _

/-- The resolution comparison preserves the augmentations in degree zero. -/
theorem resolutionComparison_f_zero :
    (modulePullback B S hS D.g').map ((injectiveResolution D.F).ι.f 0) ≫
      (D.resolutionComparison hg).f 0 = (injectiveResolution D.pulledBack).ι.f 0 := by
  have := D.quasiIso_mapι_pullback_g' hg
  have h := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ 0)
    (Stacks.RightDerivedComp.comp_descOfResolution
      (Stacks.RightDerivedComp.mapι (modulePullback B S hS D.g') (injectiveResolution D.F))
      (injectiveResolution D.pulledBack))
  simp only [HomologicalComplex.comp_f, Stacks.RightDerivedComp.mapι_f_zero] at h
  exact h

/-- The lift `I ⟶ g'_*J` of the unit `𝓕 ⟶ g'_*(g')^*𝓕`. -/
def unitLift : (injectiveResolution D.F).cocomplex ⟶
    ((modulePushforward B S hS D.g').mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution D.pulledBack).cocomplex :=
  unitHomologicalComplex (modulePullbackAdjunction B S hS D.g')
      (injectiveResolution D.F).cocomplex ≫
    ((modulePushforward B S hS D.g').mapHomologicalComplex (ComplexShape.up ℕ)).map
      (D.resolutionComparison hg)

/-- In degree zero, the augmentation of `I` followed by the lift `I ⟶ g'_*J` is the unit
`𝓕 ⟶ g'_*(g')^*𝓕` followed by `g'_*` of the augmentation of `J`. -/
theorem unitLift_f_zero :
    (injectiveResolution D.F).ι.f 0 ≫ (D.unitLift hg).f 0 =
      (modulePullbackAdjunction B S hS D.g').unit.app D.F ≫
        (modulePushforward B S hS D.g').map ((injectiveResolution D.pulledBack).ι.f 0) := by
  have hn :=
    (modulePullbackAdjunction B S hS D.g').unit.naturality ((injectiveResolution D.F).ι.f 0)
  simp only [Functor.id_map, Functor.comp_map] at hn
  change (injectiveResolution D.F).ι.f 0 ≫
      (modulePullbackAdjunction B S hS D.g').unit.app ((injectiveResolution D.F).cocomplex.X 0) ≫
        (modulePushforward B S hS D.g').map ((D.resolutionComparison hg).f 0) = _
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, D.resolutionComparison_f_zero hg]
  rfl

end Resolutions

section PullbackChain

attribute [local instance 10000] spaceModulesAbelianWrittenOut
attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable (hg : IsFlat B S hS D.g.hom)

/-- On the chosen injective resolutions, the pullback map on cohomology along `g'` is the map on
cohomology induced by the lift `I ⟶ g'_*J` of the unit, read on global sections. -/
theorem isoRightDerivedObj_inv_comp_cohomologyPullbackMap_g' (hY : IsAffineSpace B S hS D.Y.1)
    (hY' : IsAffineSpace B S hS D.Y'.1) (n : ℕ) :
    ((injectiveResolution D.F).isoRightDerivedObj (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)) n).inv ≫
        cohomologyPullbackMap B S hS D.g' (D.isAffineHom_g' hY hY') (D.isFlat_g' hg) D.F
          D.isQuasicoherent n =
      HomologicalComplex.homologyMap (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (unitHomologicalComplex (modulePullbackAdjunction B S hS D.g')
              (injectiveResolution D.F).cocomplex ≫
            ((modulePushforward B S hS D.g').mapHomologicalComplex (ComplexShape.up ℕ)).map
              (D.resolutionComparison hg)) ≫
          (NatTrans.mapHomologicalComplex (globalSectionsPushforwardIsoSite B S hS D.g').hom
            (ComplexShape.up ℕ)).app (injectiveResolution D.pulledBack).cocomplex) n ≫
        homologyToMapHomology (globalSectionsRestrictScalars B S hS D.g')
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj (injectiveResolution D.pulledBack).cocomplex) n ≫
        (globalSectionsRestrictScalars B S hS D.g').map
          ((injectiveResolution D.pulledBack).isoRightDerivedObj
            (globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)) n).inv := by
  refine (isoRightDerivedObj_inv_comp_cohomologyPullbackMap B S hS D.g' (D.isAffineHom_g' hY hY')
    (D.isFlat_g' hg) D.F D.isQuasicoherent (D.unitLift hg) (D.unitLift_f_zero hg) n).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg₂ (· ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n).symm
    (congrArg (· ≫ _)
      (Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology_eq_mapExactHomologyIso_hom
        _ _ n).symm)

end PullbackChain

section Affine

attribute [local instance 10000] spaceModulesAbelianWrittenOut
attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

/-- Over an affine base, the direct image of an injective module is acyclic for global
sections. -/
theorem acyclic_globalSections_pushforward_of_injective {Z W : AlgebraicSpaces B S hS} (k : Z ⟶ W)
    (hW : IsAffineSpace B S hS W.1) (M : Modules.{u, u} B S hS Z.1 Z.2) (hM : Injective M) :
    Stacks.RightDerivedComp.acyclic (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)) ((modulePushforward B S hS k).obj M) :=
  acyclicPushforwardOfInjective_of_isAffineSpace B S hS k hW M hM

/-- Over an affine base, the higher direct images of a quasi-coherent module along a quasi-compact
quasi-separated morphism are acyclic for global sections. -/
theorem acyclic_globalSections_rightDerived_pushforward {Z W : AlgebraicSpaces B S hS} (k : Z ⟶ W)
    (hW : IsAffineSpace B S hS W.1) (hkqc : IsQuasiCompact B S hS k.hom)
    (hkqs : IsQuasiSeparated B S hS k.hom) (M : Modules.{u, u} B S hS Z.1 Z.2)
    [M.IsQuasicoherentOnSite] (q : ℕ) :
    Stacks.RightDerivedComp.acyclic (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
      (((modulePushforward B S hS k).rightDerived q).obj M) :=
  acyclicHigherDirectImages_of_isAffineSpace_of_affineTarget B S hS k hW hkqc hkqs M q

/-- Over an affine base, the comparison of global sections with the cohomology of the direct image
of the chosen injective resolution of a quasi-coherent module is invertible. -/
theorem isIso_homologyToMapHomology_globalSections_pushforward {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (hW : IsAffineSpace B S hS W.1) (hkqc : IsQuasiCompact B S hS k.hom)
    (hkqs : IsQuasiSeparated B S hS k.hom) (M : Modules.{u, u} B S hS Z.1 Z.2)
    [M.IsQuasicoherentOnSite] (n : ℕ) :
    have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS W.1 W.2
    IsIso (homologyToMapHomology (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
      (((modulePushforward B S hS k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution M).cocomplex) n) :=
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS W.1 W.2
  Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_acyclic
    (globalSectionsFunctor.{u + 1, u, u, u} (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
    (((modulePushforward B S hS k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution M).cocomplex)
    (fun q ↦ acyclic_globalSections_pushforward_of_injective k hW
      ((injectiveResolution M).cocomplex.X q) ((injectiveResolution M).injective q))
    (fun q ↦ Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso _
      ((injectiveResolution M).isoRightDerivedObj (modulePushforward B S hS k) q)
      (acyclic_globalSections_rightDerived_pushforward k hW hkqc hkqs M q)) n

/-- A morphism of `𝒪_Y`-modules whose global sections are bijective is bijective on a terminal
chart. -/
theorem bijective_val_app_of_bijective_globalSections {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) {V : SmallEtale B S hS Z.1}
    (hV : IsTerminal V)
    (h : Function.Bijective ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map φ).hom) :
    Function.Bijective (φ.val.app (Opposite.op V)).hom := by
  have e : (φ.val.app (Opposite.op V)).hom = (sectionsEvalAddEquiv N hV) ∘
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map φ).hom ∘
        (sectionsEvalAddEquiv M hV).symm := by
    funext x
    exact (congrArg (φ.val.app (Opposite.op V)).hom
      ((sectionsEvalAddEquiv M hV).apply_symm_apply x)).symm
  rw [e]
  exact ((sectionsEvalAddEquiv N hV).bijective.comp h).comp
    (sectionsEvalAddEquiv M hV).symm.bijective

/-- **The affine case of Stacks 073K, part (1), degreewise.**  Over affine bases, with `g` flat and
`f` quasi-compact and quasi-separated, the morphism of complexes `g^*f_*I ⟶ f'_*J` given by the
degree-zero base change map on the chosen injective resolution `I` of `𝓕` followed by `f'_*` of the
comparison `(g')^*I ⟶ J` is an isomorphism on cohomology in every degree. -/
theorem isIso_homologyMap_baseChange_affine (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] [IsAffine (chartScheme V₀)]
    (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀')] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Stacks.Cohomology.RightDerivedCoEdge.baseChangeComplexMap
        (modulePullbackAdjunction B S hS D.g) (modulePullbackAdjunction B S hS D.g')
        (modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w)
        (injectiveResolution D.F).cocomplex (D.resolutionComparison hg)) n) := by
  have hY := isAffineSpace_of_isIso_chart B S hS D.Y V₀
  have hY' := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
  have hsq := AlgebraicSpaces.isPullback_hom _ _ _ D.isPullback
  have hf'qc : IsQuasiCompact B S hS D.f'.hom := isQuasiCompact_of_isPullback B S hS hsq hqc
  have hf'qs : IsQuasiSeparated B S hS D.f'.hom := isQuasiSeparated_of_isPullback B S hS hsq hqs
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS D.g hg
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS D.g
  have := (modulePullbackAdjunction B S hS D.g).isRightAdjoint
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS D.Y.1 D.Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS D.Y'.1 D.Y'.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS D.X.1 D.X.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS D.X'.1 D.X'.2
  have hqF' := D.isQuasicoherentOnSite_pulledBack
  have hH : ((((modulePushforward B S hS D.f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution D.F).cocomplex).homology n).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((injectiveResolution D.F).isoRightDerivedObj (modulePushforward B S hS D.f) n)
      (isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS D.f hqc hqs D.F n)
  have hH' : ((((modulePushforward B S hS D.f').mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution D.pulledBack).cocomplex).homology n).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((injectiveResolution D.pulledBack).isoRightDerivedObj (modulePushforward B S hS D.f') n)
      (isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS D.f' hf'qc hf'qs
        D.pulledBack n)
  have hqF := D.isQuasicoherent
  have hEY := isIso_homologyToMapHomology_globalSections_pushforward D.f hY hqc hqs D.F n
  have hEY' := isIso_homologyToMapHomology_globalSections_pushforward D.f' hY' hf'qc hf'qs
    D.pulledBack n
  have hV₀ : IsTerminal V₀ := isTerminal_of_isIso_chart B S hS D.Y V₀
  have hV₀' : IsTerminal V₀' := isTerminal_of_isIso_chart B S hS D.Y' V₀'
  have hu : IsIso (globalSectionsPullbackBaseChange B S hS D.g
      ((((modulePushforward B S hS D.f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution D.F).cocomplex).homology n)) :=
    isIso_globalSectionsPullbackBaseChange B S hS D.g _ (baseChartHomDiagram B S hS D.g V₀ V₀')
      hV₀' hV₀ hH ‹IsAffine (chartScheme V₀')› ‹IsAffine (chartScheme V₀)›
  have hp : IsIso (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (globalSectionsRingHomSite B S hS D.g)).homEquiv _ _).symm
        (D.affineCohomologyPullbackOverBase hg hY hY' n)) :=
    D.isIso_affineCohomologyBaseChangeMap V₀ V₀' hZ hg hqc hqs n
  have hΓθ := Stacks.Cohomology.RightDerivedCoEdge.isIso_globalSections_baseChange_homology
    (modulePullbackAdjunction B S hS D.g) (modulePullbackAdjunction B S hS D.g')
    (modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w)
    (globalSectionsPushforwardIsoSite B S hS D.f) (globalSectionsPushforwardIsoSite B S hS D.g)
    (globalSectionsPushforwardIsoSite B S hS D.f') (globalSectionsPushforwardIsoSite B S hS D.g')
    D.restrictScalarsSquareIso D.globalSectionsPushforwardIsoSite_squareComparison_hom
    (injectiveResolution D.F).cocomplex (D.resolutionComparison hg) n
    ((injectiveResolution D.F).isoRightDerivedObj (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)) n)
    ((injectiveResolution D.pulledBack).isoRightDerivedObj (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)) n)
    (cohomologyPullbackMap B S hS D.g' (D.isAffineHom_g' hY hY') (D.isFlat_g' hg) D.F
      D.isQuasicoherent n)
    (D.isoRightDerivedObj_inv_comp_cohomologyPullbackMap_g' hg hY hY' n)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (globalSectionsRingHomSite B S hS D.g))
    (globalSectionsPullbackMap B S hS D.g _) (globalSectionsPullbackMap_eq B S hS D.g _) hu
    (D.affineCohomologyPullbackOverBase hg hY hY' n) rfl hp hEY hEY'
  have hθ : IsIso (inv (homologyToMapHomology (modulePullback B S hS D.g)
      (((modulePushforward B S hS D.f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution D.F).cocomplex) n) ≫
      HomologicalComplex.homologyMap
        (Stacks.Cohomology.RightDerivedCoEdge.baseChangeComplexMap
          (modulePullbackAdjunction B S hS D.g) (modulePullbackAdjunction B S hS D.g')
          (modulePushforwardSquareComparisonIso D.f D.g D.f' D.g' D.isPullback.w)
          (injectiveResolution D.F).cocomplex (D.resolutionComparison hg)) n) :=
    isIso_of_bijective_val_app_isTerminal B S hS D.Y'
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.g _ hH) hH' _ hV₀'
      ‹IsAffine (chartScheme V₀')›
      (bijective_val_app_of_bijective_globalSections _ hV₀' (ConcreteCategory.bijective_of_isIso _))
  exact IsIso.of_isIso_comp_left (inv (homologyToMapHomology (modulePullback B S hS D.g)
      (((modulePushforward B S hS D.f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution D.F).cocomplex) n)) _

end Affine

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
