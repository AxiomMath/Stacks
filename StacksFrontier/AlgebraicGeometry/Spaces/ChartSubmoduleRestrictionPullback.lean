module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmoduleDirected.Capture
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSubmoduleRestrictionSections
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# The chart restriction of a submodule along a morphism of charts

Let `X` be an algebraic space, `M` a quasi-coherent `𝒪_X`-module and `K ⊆ M` a quasi-coherent
submodule on the small étale site.  For a morphism `g : V ⟶ U` of étale scheme charts of `X`, the
chart restriction `K|_V` is the image, under the comparison isomorphism
`(chartSchemeMap g)^* M|_U ≅ M|_V`, of the pullback of `K|_U`.  Consequently the chart
restriction of quasi-coherent submodules is monotone along morphisms of charts, and over a
terminal chart (for instance the identity chart of a scheme) comparing two quasi-coherent
submodules at that one chart suffices.

## Main results

* `Stacks.AlgebraicGeometry.SubmodulePrimitives.ofHom_epi_comp`: the local image of a morphism
  does not change under precomposition with an epimorphism.
* `AlgebraicGeometry.Space.restrictSubmoduleToChart_eq_ofHom`: the chart restriction of a
  submodule is the local image of the restricted inclusion.
* `AlgebraicGeometry.Space.restrictSubmoduleToChart_eq_ofHom_pullback`: **the chart restriction
  of a quasi-coherent submodule along a morphism of charts** is the local image of the pullback of
  its restriction to the larger chart, followed by the comparison isomorphism.
* `AlgebraicGeometry.Space.restrictSubmoduleToChart_le_of_le`: inclusions of chart restrictions
  of quasi-coherent submodules descend along morphisms of charts.
* `AlgebraicGeometry.Space.le_of_restrictSubmoduleToChart_le_of_isTerminal`: **over a terminal
  chart, one chart suffices**: `K₁ ≤ K₂` as soon as `K₁|_U ≤ K₂|_U`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.SubmodulePrimitives

variable {X : AlgebraicGeometry.Scheme.{u}} {F : X.Modules}

/-- The factorization of a morphism through its local image is an epimorphism. -/
instance epi_toImageModule {A : X.Modules} (f : A ⟶ F) : Epi (toImageModule f) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {U} s => ?_⟩
  refine GrothendieckTopology.superset_covering _ (fun V i hi => ?_) s.2
  obtain ⟨a, ha⟩ := hi
  exact ⟨a, Subtype.ext ha⟩

/-- **The local image does not change under precomposition with an epimorphism.** -/
theorem ofHom_epi_comp {A B : X.Modules} (e : A ⟶ B) [Epi e] (f : B ⟶ F) :
    ofHom (e ≫ f) = ofHom f := by
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  refine le_antisymm (Stacks.FiniteTypeSubmodule.ofHom_comp_le e f) ?_
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
  rintro ⟨U⟩ s hs
  have : @Epi (SheafOfModules X.ringCatSheaf) _ A B e := ‹Epi e›
  have he := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi
    (R := X.ringCatSheaf) (M := A) (N := B) e
  refine (mem_ofHom_iff (e ≫ f) s).2 fun x hx => ?_
  obtain ⟨V, hVU, hxV, t, ht⟩ := (mem_ofHom_iff f s).1 hs x hx
  obtain ⟨W, j, ⟨a, ha⟩, hxW⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map e.val) (U := op V) t x hxV
  refine ⟨W, j.le.trans hVU, hxW, a, ?_⟩
  have ha' : e.app W a = B.presheaf.map j.op t := ha
  change f.app W (e.app W a) = _
  rw [ha', show f.app W (B.presheaf.map j.op t) = F.presheaf.map j.op (f.app V t) from
    PresheafOfModules.naturality_apply f.val j.op t, ht]
  exact (ConcreteCategory.congr_hom (F.presheaf.map_comp (homOfLE hVU).op j.op) s).symm

/-- The local image does not change under precomposition with an isomorphism. -/
theorem ofHom_iso_comp {A B : X.Modules} (e : A ⟶ B) [IsIso e] (f : B ⟶ F) :
    ofHom (e ≫ f) = ofHom f :=
  ofHom_epi_comp e f

end Stacks.AlgebraicGeometry.SubmodulePrimitives

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.FiniteTypeSubmodule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS)

/-- The chart restriction of a submodule is the local image of the chart restriction of its
inclusion. -/
theorem restrictSubmoduleToChart_eq_ofHom (M : Modules.{u, u} B S hS X.1 X.2) (K : M.Submodule)
    (W : SmallEtale B S hS X.1) :
    restrictSubmoduleToChart M K W =
      ofHom (X := chartScheme W) ((restrictToChartSchemeFunctor B S hS X.1 X.2 W).map K.ι) :=
  rfl

/-- **The chart restriction of a quasi-coherent submodule along a morphism of charts.**  For a
quasi-coherent `𝒪_X`-module `M`, a quasi-coherent submodule `K ⊆ M` and a morphism `g : V ⟶ U` of
étale charts, `K|_V` is the local image of the pullback along `chartSchemeMap g` of the inclusion
`K|_U ⊆ M|_U`, followed by the comparison isomorphism `(chartSchemeMap g)^* M|_U ≅ M|_V`. -/
theorem restrictSubmoduleToChart_eq_ofHom_pullback (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (K : M.Submodule)
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite) {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    restrictSubmoduleToChart M K V =
      ofHom ((Scheme.Modules.pullback (chartSchemeMap g)).map
          (inclusion (restrictSubmoduleToChart M K U)) ≫
        (restrictToChartSchemePullbackComparisonIso X M hM g).hom) := by
  have hiso := isIso_restrictToChartSchemePullbackComparison X K.toSheafOfModules hK g
  have hfac : toImageModule ((restrictToChartSchemeFunctor B S hS X.1 X.2 U).map K.ι) ≫
      inclusion (restrictSubmoduleToChart M K U) =
        (restrictToChartSchemeFunctor B S hS X.1 X.2 U).map K.ι :=
    toImageModule_imageModuleι _
  have hnat := restrictToChartSchemePullbackComparison_naturality X K.ι g
  have : (Scheme.Modules.pullback (chartSchemeMap g)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g))
  have hepi := @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback (chartSchemeMap g)) this _ _
    (toImageModule ((restrictToChartSchemeFunctor B S hS X.1 X.2 U).map K.ι))
    (epi_toImageModule _)
  refine (@ofHom_iso_comp _ _ _ _ _ hiso _).symm.trans ?_
  refine (congrArg ofHom hnat.symm).trans ?_
  refine Eq.trans ?_ (@ofHom_epi_comp _ _ _ _ _ hepi _)
  refine congrArg ofHom ?_
  exact (congrArg (· ≫ restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g)
    ((congrArg (Scheme.Modules.pullback (chartSchemeMap g)).map hfac.symm).trans
      ((Scheme.Modules.pullback (chartSchemeMap g)).map_comp _ _))).trans (Category.assoc _ _ _)

/-- **Inclusions of chart restrictions of quasi-coherent submodules descend along morphisms of
charts.** -/
theorem restrictSubmoduleToChart_le_of_le (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) {K₁ K₂ : M.Submodule}
    (hK₁ : K₁.toSheafOfModules.IsQuasicoherentOnSite)
    (hK₂ : K₂.toSheafOfModules.IsQuasicoherentOnSite) {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (h : restrictSubmoduleToChart M K₁ U ≤ restrictSubmoduleToChart M K₂ U) :
    restrictSubmoduleToChart M K₁ V ≤ restrictSubmoduleToChart M K₂ V := by
  rw [restrictSubmoduleToChart_eq_ofHom_pullback X M hM K₁ hK₁ g,
    restrictSubmoduleToChart_eq_ofHom_pullback X M hM K₂ hK₂ g, ← inclusionOfLE_inclusion h]
  refine le_of_eq_of_le (congrArg ofHom ?_) (ofHom_comp_le
    ((Scheme.Modules.pullback (chartSchemeMap g)).map (inclusionOfLE h)) _)
  exact (congrArg (· ≫ _) ((Scheme.Modules.pullback (chartSchemeMap g)).map_comp _ _)).trans
    (Category.assoc _ _ _)

/-- **Over a terminal chart, comparing two quasi-coherent submodules at that chart suffices.**  If
`U` is a terminal étale chart of `X` (for instance the identity chart of a scheme,
`AlgebraicGeometry.Space.isTerminalIdEtaleChart`) and `K₁|_U ≤ K₂|_U`, then `K₁ ≤ K₂`. -/
theorem le_of_restrictSubmoduleToChart_le_of_isTerminal (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) {K₁ K₂ : M.Submodule}
    (hK₁ : K₁.toSheafOfModules.IsQuasicoherentOnSite)
    (hK₂ : K₂.toSheafOfModules.IsQuasicoherentOnSite) {U : SmallEtale B S hS X.1}
    (hU : Limits.IsTerminal U)
    (h : restrictSubmoduleToChart M K₁ U ≤ restrictSubmoduleToChart M K₂ U) : K₁ ≤ K₂ :=
  le_of_forall_restrictSubmoduleToChart_le X M fun W =>
    restrictSubmoduleToChart_le_of_le X M hM hK₁ hK₂ (hU.from W) h

/-- Over a terminal chart, two quasi-coherent submodules with the same restriction to that chart
are equal. -/
theorem eq_of_restrictSubmoduleToChart_eq_of_isTerminal (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) {K₁ K₂ : M.Submodule}
    (hK₁ : K₁.toSheafOfModules.IsQuasicoherentOnSite)
    (hK₂ : K₂.toSheafOfModules.IsQuasicoherentOnSite) {U : SmallEtale B S hS X.1}
    (hU : Limits.IsTerminal U)
    (h : restrictSubmoduleToChart M K₁ U = restrictSubmoduleToChart M K₂ U) : K₁ = K₂ :=
  le_antisymm (le_of_restrictSubmoduleToChart_le_of_isTerminal X M hM hK₁ hK₂ hU h.le)
    (le_of_restrictSubmoduleToChart_le_of_isTerminal X M hM hK₂ hK₁ hU h.ge)

end AlgebraicGeometry.Space

end
