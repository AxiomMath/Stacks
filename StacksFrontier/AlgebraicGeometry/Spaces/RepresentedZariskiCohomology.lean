module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LeftAdjoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.AdjointPushforwardInjectiveAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicSections
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Locality

/-!
# Cohomology of a scheme read as an algebraic space

Let `U` be an object of the big fppf site over a scheme `S`, with underlying scheme `T`, and let
`h_U = yoneda.obj U` be the algebraic space it represents.  A quasi-coherent `𝒪_{h_U}`-module `M`
lives on the small étale site of `h_U`; its restriction `ε_* M` to the Zariski opens of `T` is a
quasi-coherent `𝒪_T`-module.  This file proves that the cohomology of `M` on the small étale site
is the Zariski cohomology of `ε_* M`, in every degree, as modules over `Γ(T, 𝒪_T)`.

The comparison is the Leray collapse for the morphism of ringed sites
`ε : (h_U)_étale ⟶ T_Zar` given by the inclusion of the Zariski opens of `T` among the étale
charts of `h_U`, as in [Stacks, Tag 03DW] and [Stacks, Tag 03P2].  Its two inputs are:

* the higher direct images `R^q ε_* M` vanish for `q > 0`: by [Stacks, Tag 072W] in the form
  `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`, it
  suffices that the higher cohomology of `M` vanish over the affine opens of `T`, read as affine
  étale charts of `h_U`, which is the étale Serre vanishing
  `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`;
* the direct image along `ε` of an injective module is acyclic for the global sections over `T`:
  its underlying abelian sheaf is totally acyclic by
  `Stacks.Cohomology.AdjointPushforward.isTotallyAcyclic_of_injective`, the direct image of
  abelian sheaves having an exact left adjoint by [Stacks, Tag 08NH] because the inclusion of
  the Zariski opens has the image-open functor as a left adjoint (openness of étale morphisms,
  [Stacks, Tag 03WT]); and a totally acyclic module is acyclic for sections over an object
  ([Stacks, Tag 0731], part (1)).

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiDirectImage`: `ε_*`, the direct image of
  `𝒪_{h_U}`-modules to `𝒪_T`-modules.
* `AlgebraicGeometry.Space.representedImageOpenAdjunctionSelf`: the image-open functor is left
  adjoint to the inclusion of the Zariski opens of `T` among the étale charts of `h_U`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_representedZariskiDirectImage`:
  `R^q ε_* M = 0` for `q > 0` and `M` quasi-coherent.
* `AlgebraicGeometry.Space.acyclic_evaluation_representedZariskiDirectImage`: `ε_*` of
  an injective module is acyclic for the global sections over `T`.
* `AlgebraicGeometry.Space.representedZariskiCohomologyIso`: **the comparison**
  `H^n((h_U)_étale, M) ≅ H^n(T, ε_* M)`, over `Γ(T, 𝒪_T)`.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 08NH](https://stacks.math.columbia.edu/tag/08NH)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

-- As in `StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicSections.lean`:
-- stating `Functor.rightAcyclic` needs a `HasRightDerivedFunctor` instance, and the cheap one
-- coming from `EnoughInjectives` is given precedence over the default route.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The image-open functor is left adjoint to the inclusion
`AlgebraicGeometry.Space.selfOpensFunctor` of the Zariski opens of the scheme underlying `U`
among the étale charts of `yoneda.obj U`: the identification of the two small étale sites,
followed by `AlgebraicGeometry.SmallEtale.imageOpenAdjunction` (openness of étale morphisms). -/
def representedImageOpenAdjunctionSelf :
    ((representedSmallEtaleEquivalence B S hS U).functor ⋙
        _root_.AlgebraicGeometry.SmallEtale.imageOpenFunctor (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⊣
      selfOpensFunctor B S hS U :=
  (representedSmallEtaleEquivalence B S hS U).toAdjunction.comp
    (_root_.AlgebraicGeometry.SmallEtale.imageOpenAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)

/-- `ε_*`: the direct image of `𝒪_{h_U}`-modules on the small étale site of `yoneda.obj U` to
`𝒪_T`-modules on the Zariski site of the scheme `T` underlying `U`, along the inclusion of the
Zariski opens of `T` among the étale charts. -/
abbrev representedZariskiDirectImage :
    SheafOfModules.{u} (representedStructureRingSheaf B S hS U) ⥤
      SheafOfModules.{u} (chartScheme (idEtaleChart B S hS U)).ringCatSheaf :=
  SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)

/-- `ε_*` is additive: on underlying presheaves it is restriction along the inclusion of the
Zariski opens. -/
instance additive_representedZariskiDirectImage :
    (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).Additive where
  map_add := rfl

/-- `ε_*` is left exact: limits of sheaves of modules are computed on underlying presheaves,
where `ε_*` is restriction along the inclusion of the Zariski opens. -/
instance preservesFiniteLimits_representedZariskiDirectImage :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)) :=
  Stacks.SheafOfModules.preservesFiniteLimits_pushforward _

/-- The `𝒪_{h_U}`-modules have enough injectives, at the spelling
`SheafOfModules (representedStructureRingSheaf B S hS U)` of
`AlgebraicGeometry.Space.modules_eq_sheafOfModules_representedStructureRingSheaf`. -/
theorem enoughInjectives_representedModules :
    EnoughInjectives (SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :=
  enoughInjectives_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)

/-- The `𝒪_{h_U}`-modules have injective resolutions, at the spelling of
`AlgebraicGeometry.Space.enoughInjectives_representedModules`. -/
theorem hasInjectiveResolutions_representedModules :
    HasInjectiveResolutions (SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :=
  hasInjectiveResolutions_modules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)

/-- An affine open of the scheme underlying `U`, read as an étale chart of `yoneda.obj U`, is an
affine chart. -/
theorem isAffineChart_selfOpensFunctor_obj (W : (chartScheme (idEtaleChart B S hS U)).Opens)
    (hW : IsAffineOpen W) :
    IsAffineChart B S hS (yoneda.obj U) ((selfOpensFunctor B S hS U).obj W) := by
  rw [selfOpensFunctor_obj]
  exact hW

/-- **The higher direct images of a quasi-coherent module along `ε` vanish**: for a
quasi-coherent `𝒪_{h_U}`-module `M`, `R^q ε_* M = 0` for `q > 0`.

By [Stacks, Tag 072W] in the form
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve` it
suffices that, over every open `V` of the scheme underlying `U`, the higher cohomology of `M`
vanish over the members of a covering family of `V`; the affine opens of `V` are one, and over
an affine open, read as an affine étale chart, the higher cohomology of a quasi-coherent module
vanishes. -/
theorem isZero_rightDerived_representedZariskiDirectImage
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hM : SheafOfModules.IsQuasicoherentOnSite M) (q : ℕ) (hq : 0 < q) :
    have := enoughInjectives_representedModules B S hS U
    IsZero (((representedZariskiDirectImage B S hS U).rightDerived q).obj M) := by
  have := enoughInjectives_representedModules B S hS U
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (selfOpensFunctor B S hS U) (representedStructureRingSheaf B S hS U)
    (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (selfOpensStructureMap B S hS U) q M ?_
  intro V
  refine ⟨fun W _ => IsAffineOpen W, ?_, fun W g hW => ?_⟩
  · intro x hx
    obtain ⟨W, hWaff, hxW, hWV⟩ :=
      (Opens.isBasis_iff_nbhd.mp (chartScheme (idEtaleChart B S hS U)).isBasis_affineOpens) hx
    exact ⟨W, homOfLE hWV, ⟨W, 𝟙 W, homOfLE hWV, hWaff, Subsingleton.elim _ _⟩, hxW⟩
  · exact isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ((selfOpensFunctor B S hS U).obj W)
      (isAffineChart_selfOpensFunctor_obj B S hS U W hW) M hM q hq

open Stacks.Cohomology in
/-- **The direct image along `ε` of an injective module is acyclic for the sections over the
whole scheme.**

The direct image of abelian sheaves along the inclusion `u` of the Zariski opens has an exact
left adjoint, by [Stacks, Tag 08NH], because `u` has the image-open functor as a left adjoint;
so the abelian sheaf underlying `ε_* I` is totally acyclic,
`Stacks.Cohomology.AdjointPushforward.isTotallyAcyclic_of_injective`, and a totally acyclic
module is acyclic for sections over an object, [Stacks, Tag 0731] part (1). -/
theorem acyclic_evaluation_representedZariskiDirectImage
    (I : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) (hI : Injective I) :
    Stacks.RightDerivedComp.acyclic
      (SheafOfModules.evaluation.{u} (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤))
      ((representedZariskiDirectImage B S hS U).obj I) := by
  let := HasExt.standard
    (Sheaf (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U))) AddCommGrpCat.{u})
  have : EnoughInjectives (Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) AddCommGrpCat.{u}) :=
    enoughInjectives_sheaf_smallEtale B S hS (yoneda.obj U)
  have hadj := representedImageOpenAdjunctionSelf B S hS U
    |>.nonempty_adjunction_preservesFiniteLimits_isRightAdjoint_and_iso_sheafPushforwardCocontinuous
      AddCommGrpCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
      (SmallEtale.topology B S hS (yoneda.obj U))
  obtain ⟨adj⟩ := hadj.1
  have hlex := hadj.2.1
  have : Injective I := hI
  have htot := AdjointPushforward.isTotallyAcyclic_of_injective adj
    (representedStructureRingSheaf B S hS U) I
  have hra := rightAcyclic_evaluation_of_isTotallyAcyclic
    (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
    (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤)
    ((representedZariskiDirectImage B S hS U).obj I) htot
  exact (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _).1 hra

/-- The ring map `Γ(T, 𝒪_T) ⟶ 𝒪_{h_U}(u(T))` of the structure map of `ε` over the whole scheme:
functions on `T` read as functions on the étale chart of `yoneda.obj U` that the open `⊤` of `T`
becomes. -/
abbrev representedTopRingHom :
    (chartScheme (idEtaleChart B S hS U)).ringCatSheaf.obj.obj (op ⊤) →+*
      (representedStructureRingSheaf B S hS U).obj.obj (op ((selfOpensFunctor B S hS U).obj ⊤)) :=
  ((selfOpensStructureMap B S hS U).hom.app (op ⊤)).hom

/-- Sections over `T` of `ε_* M` are the sections of `M` over the étale chart that `⊤` becomes,
with scalars restricted along `AlgebraicGeometry.Space.representedTopRingHom`. -/
def representedZariskiDirectImageCompEvaluationIso :
    representedZariskiDirectImage B S hS U ⋙
        SheafOfModules.evaluation.{u} (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤) ≅
      SheafOfModules.evaluation.{u} (representedStructureRingSheaf B S hS U)
          (op ((selfOpensFunctor B S hS U).obj ⊤)) ⋙
        ModuleCat.restrictScalars (representedTopRingHom B S hS U) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The cohomology of a quasi-coherent module on `h_U` over the étale chart `⊤` is the Zariski
cohomology of its restriction to `T`.**  For a quasi-coherent `𝒪_{h_U}`-module `M` and every
degree `n`,

`H^n(u(⊤), M) ≅ H^n(T, ε_* M)`

as modules over `Γ(T, 𝒪_T)`.  This is the Leray collapse
`Stacks.RightDerivedComp.objIsoOfAcyclicImage` for `ε_*` followed by the sections over `T`: its
two inputs are `isZero_rightDerived_representedZariskiDirectImage` and
`acyclic_evaluation_representedZariskiDirectImage`. -/
def representedZariskiCohomologyIso
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hM : SheafOfModules.IsQuasicoherentOnSite M) (n : ℕ) :
    have := hasInjectiveResolutions_representedModules B S hS U
    (ModuleCat.restrictScalars (representedTopRingHom B S hS U)).obj
        (((SheafOfModules.evaluation.{u} (representedStructureRingSheaf B S hS U)
          (op ((selfOpensFunctor B S hS U).obj ⊤))).rightDerived n).obj M) ≅
      ((SheafOfModules.evaluation.{u} (chartScheme (idEtaleChart B S hS U)).ringCatSheaf
          (op ⊤)).rightDerived n).obj ((representedZariskiDirectImage B S hS U).obj M) := by
  have := hasInjectiveResolutions_representedModules B S hS U
  have := enoughInjectives_representedModules B S hS U
  refine ((Functor.rightDerivedCompIso
      (SheafOfModules.evaluation.{u} (representedStructureRingSheaf B S hS U)
        (op ((selfOpensFunctor B S hS U).obj ⊤)))
      (ModuleCat.restrictScalars (representedTopRingHom B S hS U)) n).app M).symm ≪≫ ?_
  refine ((Functor.rightDerivedIsoOfNatIso
      (representedZariskiDirectImageCompEvaluationIso B S hS U) n).app M).symm ≪≫ ?_
  exact Stacks.RightDerivedComp.objIsoOfAcyclicImage (representedZariskiDirectImage B S hS U)
      (SheafOfModules.evaluation.{u} (chartScheme (idEtaleChart B S hS U)).ringCatSheaf (op ⊤))
      (fun q hq => isZero_rightDerived_representedZariskiDirectImage B S hS U M hM q hq)
      (fun I hI => acyclic_evaluation_representedZariskiDirectImage B S hS U I hI) n

/-- **`ε_*` is the chart restriction to the identity chart**, read as the chart-scheme transport
`AlgebraicGeometry.Space.chartSchemeModule`: the restriction to the identity chart is `ε_*` by
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` and
`AlgebraicGeometry.Space.selfOpensPushforwardIso`, and it is the chart-scheme transport by
`AlgebraicGeometry.Space.restrictToChartSchemeIsoChartSchemeModule`. -/
def representedZariskiDirectImageIsoChartSchemeModule
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hM : SheafOfModules.IsQuasicoherentOnSite M) :
    (representedZariskiDirectImage B S hS U).obj M ≅
      chartSchemeModule B S hS (schemeSpace U) M hM (idEtaleChart B S hS U) :=
  (restrictToChartSchemeIdEtaleChartIso B S hS U M ≪≫ selfOpensPushforwardIso B S hS U M).symm ≪≫
    restrictToChartSchemeIsoChartSchemeModule B S hS (schemeSpace U) M hM
      (idEtaleChart B S hS U)

/-- **`ε_*` of a coherent module is coherent**, when the scheme underlying `U` is locally
Noetherian: it is the chart-scheme transport, which is coherent by
`AlgebraicGeometry.Space.isCoherent_chartSchemeModule_of_isLocallyNoetherian`. -/
theorem isCoherent_representedZariskiDirectImage
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hM : IsCoherent B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) M)
    [hU : _root_.AlgebraicGeometry.IsLocallyNoetherian (chartScheme (idEtaleChart B S hS U))] :
    SheafOfModules.IsCoherent ((representedZariskiDirectImage B S hS U).obj M) :=
  Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_iso
    (representedZariskiDirectImageIsoChartSchemeModule B S hS U M
      hM.toIsQuasicoherentOnSite).symm
    (isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS (schemeSpace U) M hM
      (idEtaleChart B S hS U) hU)

/-- **The cohomology of a coherent module on a scheme proper over an affine Noetherian scheme,
read as an algebraic space, is finite over the base.**  Let `g` be a proper morphism from the
scheme underlying `U` to an affine locally Noetherian scheme `W`, and `M` a coherent
`𝒪_{h_U}`-module.  Then the cohomology of `M` over the étale chart `u(⊤)` is a finite
`Γ(W, 𝒪_W)`-module in every degree.

This is [Stacks, Tag 02O6] for the scheme,
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, at the coherent module
`ε_* M`, read through the comparison
`AlgebraicGeometry.Space.representedZariskiCohomologyIso`. -/
theorem moduleFinite_rightDerived_evaluation_selfOpensTop {W : Scheme.{u}}
    (g : chartScheme (idEtaleChart B S hS U) ⟶ W) [_root_.AlgebraicGeometry.IsProper g] [IsAffine W]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hM : IsCoherent B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) M) (n : ℕ) :
    have := hasInjectiveResolutions_representedModules B S hS U
    Module.Finite Γ(W, ⊤)
      ((ModuleCat.restrictScalars ((representedTopRingHom B S hS U).comp g.appTop.hom)).obj
        (((SheafOfModules.evaluation.{u} (representedStructureRingSheaf B S hS U)
          (op ((selfOpensFunctor B S hS U).obj ⊤))).rightDerived n).obj M)) := by
  have := hasInjectiveResolutions_representedModules B S hS U
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (chartScheme (idEtaleChart B S hS U)) :=
    LocallyOfFiniteType.isLocallyNoetherian g
  have : SheafOfModules.IsCoherent ((representedZariskiDirectImage B S hS U).obj M) :=
    isCoherent_representedZariskiDirectImage B S hS U M hM
  have h := ProperCoherenceWitness.moduleFinite_cohomology g
    ((representedZariskiDirectImage B S hS U).obj M) n
  exact @Module.Finite.equiv _ _ _ _ _ _ _ _ h ((ModuleCat.restrictScalars g.appTop.hom).mapIso
    (representedZariskiCohomologyIso B S hS U M hM.toIsQuasicoherentOnSite n)).symm.toLinearEquiv

end AlgebraicGeometry.Space

end
