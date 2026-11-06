module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionAction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmodulePullbackChart
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupportFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyGlobalSplitting

/-!
# A finite type part of `π^!ℱ` on which the trace is surjective over the chart

In the situation of [Stacks, Tag 0GUY], with `π_*𝒪_Y` of finite presentation, let `ℱ` be a
finite type quasi-coherent `𝒪_X`-module and `𝒢 = π^!ℱ`
(`AlgebraicGeometry.Space.affinePushforwardRightAdjoint`).  The module `𝒢` need not be of finite
type, but the part of it that the trace sees over the chart `V` is: for a split section
`ε : 𝒪_V ⟶ (π_*𝒪_Y)|_V`, multiplication by `ε(1)` followed by the trace `π_*𝒢 ⟶ ℱ` is an
epimorphism onto `ℱ|_V` (`AlgebraicGeometry.Space.epi_etaleSectionAction_comp_map_counit`), and
finitely many sections of `ℱ|_V` generate it.  Lifting them to `π_*𝒢` over the affine chart and
enclosing the lifts in a finite type quasi-coherent submodule `ℳ' ⊆ π_*𝒢` (Stacks 0829) gives a
finite type quasi-coherent `𝒪_Y`-module `π^*ℳ'` with a map `θ : π^*ℳ' ⟶ 𝒢` through which the
trace is still surjective over `V`.

## Main results

* `AlgebraicGeometry.Space.exists_finiteType_modulePullback_epi_traceAction`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **A finite type quasi-coherent `𝒪_Y`-module mapping to `π^!ℱ` through which the trace,
cut down by a split section over the chart `V`, is surjective over `V`.** -/
theorem exists_finiteType_modulePullback_epi_traceAction
    (hfp : (pushforwardStructureModule B S hS
      (D.piHom B S hS hZ X hqc hqs)).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (ε : SheafOfModules.unit (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)) ⟶
      (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
        (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
        (directImageAlgebraUnitModule B S hS (D.piHom B S hS hZ X hqc hqs)))
    (pr : (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
        (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
        (directImageAlgebraUnitModule B S hS (D.piHom B S hS hZ X hqc hqs)) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)))
    (hε : ε ≫ pr = 𝟙 _) :
    ∃ (M' : Modules.{u, u} B S hS X.1 X.2) (_ : M'.IsQuasicoherentOnSite)
      (_ : SheafOfModules.IsFiniteTypeOnSite M')
      (θ : (modulePullback B S hS (D.piHom B S hS hZ X hqc hqs)).obj M' ⟶
        (affinePushforwardRightAdjoint B S hS (D.piHom B S hS hZ X hqc hqs)).obj F),
      Epi (etaleSectionAction B S hS (D.piHom B S hS hZ X hqc hqs)
          (D.chartHom B S hS hZ X hqc hqs) (D.isEtale_chartHom B S hS hZ X hqc hqs) ε
          ((moduleDirectImage B S hS (D.piHom B S hS hZ X hqc hqs)).obj
            ((modulePullback B S hS (D.piHom B S hS hZ X hqc hqs)).obj M')) ≫
        (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
          (D.isEtale_chartHom B S hS hZ X hqc hqs)).map
          ((directImageAlgebraRestrictScalars B S hS (D.piHom B S hS hZ X hqc hqs)).map
              ((moduleDirectImage B S hS (D.piHom B S hS hZ X hqc hqs)).map θ) ≫
            (directImageAlgebraRestrictScalars B S hS (D.piHom B S hS hZ X hqc hqs)).map
              (moduleDirectImage_affinePushforwardRightAdjointIso B S hS
                (D.piHom B S hS hZ X hqc hqs) D.isFinite_π.isAffineHom hfp F hFq).inv ≫
            (directImageAlgebraRestrictCoextendAdjunction B S hS
              (D.piHom B S hS hZ X hqc hqs)).counit.app F)) := by
  let π := D.piHom B S hS hZ X hqc hqs
  let g := D.chartHom B S hS hZ X hqc hqs
  have hg : IsEtale B S hS g.hom := D.isEtale_chartHom B S hS hZ X hqc hqs
  have hπA : IsAffineHom B S hS π.hom := D.isFinite_π.isAffineHom
  let e := moduleDirectImage_affinePushforwardRightAdjointIso B S hS π hπA hfp F hFq
  let G := (affinePushforwardRightAdjoint B S hS π).obj F
  have hGq : G.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_affinePushforwardRightAdjoint_obj B S hS π hπA hfp F hFq
  -- the trace cut down by `ε`, on `π_*𝒢`, transported along `e`
  let c := (etaleModulePullback B S hS g hg).map
      ((directImageAlgebraRestrictScalars B S hS π).map e.inv) ≫
    etaleSectionAction B S hS π g hg ε ((directImageAlgebraCoextendScalars B S hS π).obj F) ≫
    (etaleModulePullback B S hS g hg).map
      ((directImageAlgebraRestrictCoextendAdjunction B S hS π).counit.app F)
  have hc : Epi c := by
    have h0 := epi_etaleSectionAction_comp_map_counit B S hS π g hg ε F pr hε
    have h1 : Epi ((etaleModulePullback B S hS g hg).map
        ((directImageAlgebraRestrictScalars B S hS π).map e.inv)) :=
      @IsIso.epi_of_iso _ _ _ _ _ (Functor.map_isIso _ _)
    exact epi_comp _ _
  -- the terminal affine chart of `V`, and generators of `ℱ|_V` over it
  let T₀ : SmallEtale B S hS (D.chartSpace B S hS hZ X hqc hqs).1 :=
    isoChart B S hS (Iso.refl (yoneda.obj D.V))
  have hT : IsTerminal T₀ := isTerminal_isoChart B S hS (Iso.refl (yoneda.obj D.V))
  have hTa : IsAffine ((SmallEtale.toOver B S hS (D.chartSpace B S hS hZ X hqc hqs).1 ⋙
      BigFppfOver.toScheme B S hS).obj T₀) := D.isAffine_V
  have hgFq := isQuasicoherentOnSite_etaleModulePullback B S hS g hg F hFq
  have hgFft := isFiniteTypeOnSite_etaleModulePullback B S hS g hg F hFft
  have hgFcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS _ _ _ hgFq
  obtain ⟨n, s, hs⟩ := generates_of_module_finite_sections _ hgFcart hTa
    (module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite _ hgFcart hgFft T₀
      hTa)
  -- lifts to `π_*𝒢` over the chart
  let N := (modulePushforward B S hS π).obj G
  have hNq : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS π hπA G hGq
  have hgNq := isQuasicoherentOnSite_etaleModulePullback B S hS g hg N hNq
  have hsurj := surjective_val_app_of_epi_of_isQuasicoherentOnSite c hc hgNq hgFq T₀ hTa
  choose x hx using fun i => hsurj (s i)
  -- the chart `V ⟶ X`, and a finite type quasi-coherent submodule of `π_*𝒢` containing the lifts
  let VX : SmallEtale B S hS X.1 := (smallEtalePostcomp B S hS g hg).obj T₀
  have hVXa : IsAffine (chartScheme VX) := D.isAffine_V
  have hNcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 N hNq
  obtain ⟨Dsub, hDsub⟩ := (chartExtensionProperty_id hZ hqc hqs hNcart).exists_forall_mem hNcart
    (Finset.univ : Finset (Fin n)) (fun _ => VX) (fun _ => VX.1.hom) (fun _ => Category.comp_id _)
    (fun _ => hVXa) (fun i => (x i : N.val.obj (op VX)))
  let M'sub := Dsub.toSubmodule _
  have hM'q : M'sub.toSheafOfModules.IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2 _).2
      (Dsub.isCartesianOnAffineCharts_toSubmodule hNcart)
  have hM'ft : SheafOfModules.IsFiniteTypeOnSite M'sub.toSheafOfModules :=
    Dsub.isFiniteTypeOnSite_toSubmodule hNcart
  have hmem : ∀ i, (x i : N.val.obj (op VX)) ∈ M'sub.obj (op VX) := fun i =>
    hDsub i (Finset.mem_univ i)
  let θ : (modulePullback B S hS π).obj M'sub.toSheafOfModules ⟶ G :=
    ((modulePullbackAdjunction B S hS π).homEquiv _ _).symm M'sub.ι
  have hθ : (modulePullbackAdjunction B S hS π).unit.app M'sub.toSheafOfModules ≫
      (modulePushforward B S hS π).map θ = M'sub.ι :=
    ((modulePullbackAdjunction B S hS π).homEquiv_unit _ _ θ).symm.trans
      (Equiv.apply_symm_apply _ _)
  refine ⟨M'sub.toSheafOfModules, hM'q, hM'ft, θ, ?_⟩
  have hnat := etaleSectionAction_naturality B S hS π g hg ε
    ((moduleDirectImage B S hS π).map θ ≫ e.inv)
  simp only [Functor.map_comp, Category.assoc] at hnat ⊢
  rw [← reassoc_of% hnat]
  change Epi (_ ≫ c)
  refine Preadditive.epi_of_cancel_zero _ fun {Z} d hd => ?_
  refine Stacks.SheafOfModules.eq_zero_of_generates hT s hs d fun i => ?_
  let z : ((etaleModulePullback B S hS g hg).obj ((modulePushforward B S hS π).obj
      ((modulePullback B S hS π).obj M'sub.toSheafOfModules))).val.obj (op T₀) :=
    (((modulePullbackAdjunction B S hS π).unit.app M'sub.toSheafOfModules).val.app (op VX)).hom
      ⟨x i, hmem i⟩
  have hz : (((etaleModulePullback B S hS g hg).map
      ((modulePushforward B S hS π).map θ)).val.app (op T₀)).hom z = x i :=
    congrArg (fun φ : M'sub.toSheafOfModules ⟶ N => (φ.val.app (op VX)).hom ⟨x i, hmem i⟩) hθ
  rw [← hx i, ← hz]
  exact congrArg (fun φ => (φ.val.app (op T₀)).hom z) hd

end AlgebraicGeometry.Space

end
