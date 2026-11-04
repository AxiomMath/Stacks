module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleMapOfSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasQuotient
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionIsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiTwist

/-!
# Isomorphisms of projective bundles of algebraic spaces

Let `X` be an algebraic space over `S`.

* If `ℰ` is a finite locally free `𝒪_X`-module of rank one, the projection
  `π : 𝐏(ℰ) ⟶ X` is an isomorphism. Over the presenting chart `U` of `X` it is the projection of
  the chart bundle `𝐏(ℰ|_U) ⟶ U`, an isomorphism of schemes since `ℰ|_U` is invertible
  (`Stacks.RelativeProj.isIso_projectiveBundleToBase_of_isInvertible`), and the square with the
  charts is cartesian, so `π` is an isomorphism after the base change along the étale surjective
  chart, and being an isomorphism is fppf local on the target
  (`AlgebraicGeometry.Space.isIso_of_forall_isIso_pullback_snd`).

* If `e : ℰ ≅ ℰ'` is an isomorphism of finite locally free modules, the closed immersion
  `𝐏(ℰ') ⟶ 𝐏(ℰ)` of the quotient `e.hom` is an isomorphism over `X`: it is a monomorphism of
  sheaves, and locally surjective since the chart of `𝐏(ℰ)` factors through it, the closed
  immersion of chart bundles of an isomorphism being an isomorphism
  (`Stacks.RelativeProj.isIso_projectiveBundleMapOfEpi_of_comp_eq_id`). It matches the twists by
  `AlgebraicGeometry.Space.projectiveBundleSplitEpiTwistIso`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleIsoOfIso`: **`𝐏(ℰ') ≅ 𝐏(ℰ)` over `X`.**
* `AlgebraicGeometry.Space.projectiveBundleIsoOfIsoTwistIso`: `φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_bigFppfOver_toScheme_map`: a morphism of the big fppf
  site whose morphism of schemes is an isomorphism is an isomorphism.
* `AlgebraicGeometry.Space.isIso_projectiveBundleProj_of_isIso_chartBundleToChart`: `π` is an
  isomorphism when the projection of the presenting chart bundle is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of the big fppf site whose morphism of schemes is an isomorphism is an
isomorphism**: the inverse of the morphism of schemes lies over the base. -/
theorem isIso_of_isIso_bigFppfOver_toScheme_map {V W : BigFppfOver B S hS} (a : V ⟶ W)
    [IsIso ((BigFppfOver.toScheme B S hS).map a)] : IsIso a := by
  let b : W ⟶ V := Over.homMk (ObjectProperty.homMk (inv ((BigFppfOver.toScheme B S hS).map a)))
    (by
      apply B.inclusion.map_injective
      have hw := congrArg B.inclusion.map (Over.w a)
      rw [Functor.map_comp] at hw
      show inv ((BigFppfOver.toScheme B S hS).map a) ≫ B.inclusion.map V.hom =
        B.inclusion.map W.hom
      rw [IsIso.inv_comp_eq]
      exact hw.symm)
  refine ⟨b, ?_, ?_⟩ <;> apply (BigFppfOver.toScheme B S hS).map_injective <;>
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
  · exact IsIso.hom_inv_id ((BigFppfOver.toScheme B S hS).map a)
  · exact IsIso.inv_hom_id ((BigFppfOver.toScheme B S hS).map a)

variable {X : AlgebraicSpaces B S hS}

/-- **The projection of the projective bundle is an isomorphism when the projection of the
presenting chart bundle is**: the square of `π` with the presenting charts is cartesian, and being
an isomorphism is fppf local on the target. -/
theorem isIso_projectiveBundleProj_of_isIso_chartBundleToChart
    (E : Modules.{u, u} B S hS X.1 X.2) [E.IsQuasicoherentOnSite]
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (h : IsIso (chartBundleToChart E (presentationChart (projectiveBundlePresentation X)))) :
    IsIso (projectiveBundleProj E hfree) := by
  have : IsIso ((projectiveBundleChartFamily E hfree).siteToChart
      (presentationChart (projectiveBundlePresentation X))) :=
    @isIso_of_isIso_bigFppfOver_toScheme_map B S hS _ _ _ h
  have hsnd : IsIso (pullback.snd (projectiveBundleProj E hfree).hom
      (presentationChart (projectiveBundlePresentation X)).obj.hom) := by
    rw [← (isPullback_projectiveBundleProj E hfree).isoPullback_inv_snd]
    infer_instance
  let c : (schemeSpace ((projectiveBundlePresentation X).U) : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk (presentationChart (projectiveBundlePresentation X)).obj.hom
  exact isIso_of_forall_isIso_pullback_snd B S hS (projectiveBundleProj E hfree)
    (fun _ : PUnit.{1} => _) (fun _ => c)
    (isFppfCovering_atlas B S hS X.2 (surjective_projectiveBundlePresentation X)
      (projectiveBundlePresentation X).etale)
    (fun _ => isIso_pullback_snd_of_isIso_pullback_snd_hom B S hS _ c hsnd)

section ModuleIso

variable (E E' : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  [hE' : E'.IsQuasicoherentOnSite] (e : E ≅ E')
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfree' : SheafOfModules.IsFiniteLocallyFreeOnSite E')

/-- The closed immersion of chart bundles of the reading of an isomorphism is an isomorphism. -/
theorem isIso_projectiveBundleMapOfEpi_chartModuleMap_hom (V : SmallEtale B S hS X.1) :
    IsIso (@Stacks.RelativeProj.projectiveBundleMapOfEpi _ _ _ _ _ (chartModuleMap e.hom V)
      (epi_chartModuleMap e.hom e.inv e.inv_hom_id V)) :=
  @Stacks.RelativeProj.isIso_projectiveBundleMapOfEpi_of_comp_eq_id _ _ _ _ _
    (chartModuleMap e.hom V) (epi_chartModuleMap e.hom e.inv e.inv_hom_id V)
    (chartModuleMap e.inv V)
    ((schemeReadingMap_comp (chartToSpace B S hS X V) e.hom e.inv).symm.trans
      (by rw [e.hom_inv_id]; exact schemeReadingMap_id _))

/-- **The morphism of projective bundles of an isomorphism of modules is an isomorphism.** It is
a closed immersion, hence a monomorphism of sheaves, and it is locally surjective: the chart of
`𝐏(ℰ)` factors through it, the closed immersion of chart bundles being an isomorphism. -/
theorem isIso_projectiveBundleMapOfSplitEpi_of_iso :
    IsIso (projectiveBundleMapOfSplitEpi E E' e.hom e.inv e.inv_hom_id hfree hfree') := by
  have : IsIso ((projectiveBundleChartFamilyHomOfSplitEpi E E' e.hom e.inv e.inv_hom_id hfree
      hfree').siteApp (presentationChart (projectiveBundlePresentation X))) :=
    @isIso_of_isIso_bigFppfOver_toScheme_map B S hS _ _ _
      (isIso_projectiveBundleMapOfEpi_chartModuleMap_hom E E' e
        (presentationChart (projectiveBundlePresentation X)))
  have hfac : (inv (yoneda.map ((projectiveBundleChartFamilyHomOfSplitEpi E E' e.hom e.inv
      e.inv_hom_id hfree hfree').siteApp (presentationChart (projectiveBundlePresentation X)))) ≫
        projectiveBundleChart E' hfree') ≫
        (projectiveBundleMapOfSplitEpi E E' e.hom e.inv e.inv_hom_id hfree hfree').hom =
      projectiveBundleChart E hfree := by
    rw [Category.assoc, projectiveBundleChart_comp_projectiveBundleMapOfSplitEpi,
      IsIso.inv_hom_id_assoc]
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (projectiveBundleChart E hfree) :=
    Stacks.Groupoids.isLocallySurjective_quotientChart _ _ _ _
  exact (ObjectProperty.isIso_hom_iff _).1
    (NormalizationGluing.isIso_of_mono_of_isLocallySurjective_of_isSheaf B S hS
      (projectiveBundle E' hfree').property.isSheaf (projectiveBundle E hfree).property.isSheaf _
      (mono_of_isClosedImmersion B S hS _ (isClosedImmersion_projectiveBundleMapOfSplitEpi E E'
        e.hom e.inv e.inv_hom_id hfree hfree'))
      (Presheaf.isLocallySurjective_of_isLocallySurjective_fac (BigFppfOver.topology B S hS) hfac))

/-- **The isomorphism `𝐏(ℰ') ≅ 𝐏(ℰ)` of projective bundles of an isomorphism `e : ℰ ≅ ℰ'`**:
the morphism of projective bundles of the quotient `e.hom`. -/
def projectiveBundleIsoOfIso :
    projectiveBundle E' hfree' ≅ projectiveBundle E hfree :=
  haveI := isIso_projectiveBundleMapOfSplitEpi_of_iso E E' e hfree hfree'
  asIso (projectiveBundleMapOfSplitEpi E E' e.hom e.inv e.inv_hom_id hfree hfree')

/-- The isomorphism `𝐏(ℰ') ≅ 𝐏(ℰ)` is `projectiveBundleMapOfSplitEpi` of `e.hom`. -/
theorem projectiveBundleIsoOfIso_hom :
    (projectiveBundleIsoOfIso E E' e hfree hfree').hom =
      projectiveBundleMapOfSplitEpi E E' e.hom e.inv e.inv_hom_id hfree hfree' :=
  rfl

/-- **The isomorphism `𝐏(ℰ') ≅ 𝐏(ℰ)` lies over `X`.** -/
@[reassoc]
theorem projectiveBundleIsoOfIso_hom_comp_projectiveBundleProj :
    (projectiveBundleIsoOfIso E E' e hfree hfree').hom ≫ projectiveBundleProj E hfree =
      projectiveBundleProj E' hfree' :=
  projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' e.hom e.inv e.inv_hom_id hfree hfree'

/-- **The isomorphism `𝐏(ℰ') ≅ 𝐏(ℰ)` matches the twists**: `φ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)`,
`AlgebraicGeometry.Space.projectiveBundleSplitEpiTwistIso` at the quotient `e.hom`. -/
def projectiveBundleIsoOfIsoTwistIso :
    (modulePullback B S hS (projectiveBundleIsoOfIso E E' e hfree hfree').hom).obj
        (projectiveBundleTwist E hfree).obj ≅ (projectiveBundleTwist E' hfree').obj :=
  projectiveBundleSplitEpiTwistIso E E' e.hom e.inv e.inv_hom_id hfree hfree'

/-- **The twist comparison of `𝐏(ℰ') ≅ 𝐏(ℰ)` carries the inverse image of the tautological
quotient of `𝐏(ℰ)` to `π'^*e` followed by the tautological quotient of `𝐏(ℰ')`.** -/
theorem comp_projectiveBundleIsoOfIsoTwistIso_hom :
    ((QuasiCoherentDescent.pullbackComparison B S hS
        (projectiveBundleMapOfSplitEpi E E' e.hom e.inv e.inv_hom_id hfree hfree')
        (projectiveBundleProj E hfree) (projectiveBundleProj E' hfree')
        (projectiveBundleMapOfSplitEpi_comp_projectiveBundleProj E E' e.hom e.inv e.inv_hom_id
          hfree hfree') E).hom ≫
      (modulePullback B S hS
          (projectiveBundleMapOfSplitEpi E E' e.hom e.inv e.inv_hom_id hfree hfree')).map
        (X := (modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
        (projectiveBundleTautological E hfree).hom) ≫
        (projectiveBundleIsoOfIsoTwistIso E E' e hfree hfree').hom =
      (modulePullback B S hS (projectiveBundleProj E' hfree')).map e.hom ≫
        (projectiveBundleTautological E' hfree').hom :=
  comp_projectiveBundleSplitEpiTwistIso_hom E E' e.hom e.inv e.inv_hom_id hfree hfree'

end ModuleIso

end AlgebraicGeometry.Space

end
