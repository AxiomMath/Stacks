module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTransposeChartBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentAffineChartOverLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Pushout.ClosedImmersionIntegral
public import StacksFrontier.Algebra.Category.ModuleCat.SurjectiveKerSmulTop

/-!
# `H⁰(K) ⊗ 𝒪_Z ≅ F` over the charts above an affine chart, from the derived sections

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces lying over a morphism `p₀ : T₀ ⟶ T` of
affine bases, `K ∈ D_QCoh(𝒪_X)`, `F` a quasi-coherent `𝒪_Z`-module and `π : K ⟶ (i_* F)[0]`.
Let `c` be an affine étale chart of `X` with ring map `φ : Γ(T) → Γ(c)`. If the map
`H⁰(RΓ(c, K)) ⟶ H⁰(RΓ(c, (i_* F)[0]))` induced by `π` is surjective with kernel
`ker(Γ(T) → Γ(T₀)) • H⁰(RΓ(c, K))`, then the transpose `i^* H⁰(K) ⟶ F` of `H⁰(π)` is an
isomorphism over every chart of `Z` above the base change `c ×_X Z`.

This is part (3) of [Stacks, Tag 0CX9] on one chart: `H⁰(RΓ(c, K)) = Γ(c, H⁰(K))` and
`H⁰(RΓ(c, (i_* F)[0])) = Γ(c, i_* F)` by the affine dictionary
(`AlgebraicGeometry.Space.isIso_hypercohomologyEdge_app_of_isAffineChart`), the ring of
`c ×_X Z` is a quotient of `Γ(c)` killing `φ(ker(Γ(T) → Γ(T₀)))`, and
`AlgebraicGeometry.Space.bijective_homEquiv_symm_val_app_of_surjective` concludes on
`c ×_X Z`; quasi-coherence propagates it to the charts above
(`AlgebraicGeometry.Space.bijective_val_app_of_bijective_affineChart`).

## Main results

* `AlgebraicGeometry.Space.homologyZeroTranspose`: the transpose `i^* H⁰(K) ⟶ F` of `H⁰(π)`.
* `AlgebraicGeometry.Space.isIso_homologyZeroTranspose_val_app_of_chart`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] enoughInjectives_modules_ringUniverse
  isGrothendieckAbelian_modules_ringUniverse
attribute [local instance] hasRightDerivedFunctor_chartSections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Z : AlgebraicSpaces B S hS}

/-- The transpose `i^* H⁰(K) ⟶ F` of `H⁰(π) : H⁰(K) ⟶ H⁰((i_* F)[0]) = i_* F`, for
`π : K ⟶ (i_* F)[0]`. -/
abbrev homologyZeroTranspose (i : Z ⟶ X) (K : spaceDerivedCategory B S hS X)
    (F : Modules.{u, u} B S hS Z.1 Z.2)
    (π : K ⟶ (spaceDerivedSingle B S hS X 0).obj ((modulePushforward B S hS i).obj F)) :
    (modulePullback B S hS i).obj ((spaceDerivedHomology B S hS X 0).obj K) ⟶ F :=
  ((modulePullbackAdjunction B S hS i).homEquiv _ _).symm
    ((spaceDerivedHomology B S hS X 0).map π ≫
      ((@DerivedCategory.singleFunctorCompHomologyFunctorIso _ _
        (modulesAbelianSmallEtale B S hS X.1 X.2) (spaceHasDerivedCategory B S hS X) 0).app
          ((modulePushforward B S hS i).obj F)).hom)

/-- Over a chart diagram over `i` above `p₀`, functions on the base killed in `Γ(T₀)` are killed on
the chart of `Z`. -/
theorem chartDiagramRestrict_appTop_eq_zero {T T₀ : BigFppfOver B S hS} (hX : X.1 ⟶ yoneda.obj T)
    (hZ : Z.1 ⟶ yoneda.obj T₀) (p₀ : T₀ ⟶ T) (i : Z ⟶ X)
    (hsq : i.hom ≫ hX = hZ ≫ yoneda.map p₀) (d : ChartDiagram B S hS Z.1 X.1 i.hom)
    (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (ha : a ∈ RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map p₀)).hom) :
    chartDiagramRestrict B S hS i d
      ((Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (d.V.1.hom ≫ hX)))).hom a) = 0 := by
  have heq : d.g ≫ yoneda.preimage (d.V.1.hom ≫ hX) = yoneda.preimage (d.U.1.hom ≫ hZ) ≫ p₀ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, yoneda.map_preimage, yoneda.map_preimage,
      ← Category.assoc, ← d.comm, Category.assoc, hsq, Category.assoc]
  have e := congrArg (fun k => (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map k)).hom a) heq
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply] at e
  rw [RingHom.mem_ker.1 ha, map_zero] at e
  exact e

/-- **Part (3) of [Stacks, Tag 0CX9] over the charts above one affine chart.** -/
theorem isIso_homologyZeroTranspose_val_app_of_chart {T T₀ : BigFppfOver B S hS}
    (hX : X.1 ⟶ yoneda.obj T) (hZ : Z.1 ⟶ yoneda.obj T₀) (p₀ : T₀ ⟶ T) (i : Z ⟶ X)
    (hsq : i.hom ≫ hX = hZ ≫ yoneda.map p₀) (hci : IsClosedImmersion B S hS i.hom)
    (haff : IsAffineHom B S hS i.hom) (K : spaceDerivedCategory B S hS X)
    (hK : spaceQuasicoherentProp B S hS X K) (F : Modules.{u, u} B S hS Z.1 Z.2)
    (hF : F.IsQuasicoherentOnSite)
    (π : K ⟶ (spaceDerivedSingle B S hS X 0).obj ((modulePushforward B S hS i).obj F))
    (c : SmallEtale B S hS X.1) (hc : IsAffineChart B S hS X.1 c)
    (hsurj : Function.Surjective ((DerivedCategory.homologyFunctor _ 0).map
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) c).map π)))
    (hker : LinearMap.ker ((ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS
          (yoneda.preimage (c.1.hom ≫ hX))).hom).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} ((structurePresheaf B S hS
            X.1).obj (op c))) 0).map
          ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O) c).map π))).hom =
        RingHom.ker (representedAffineCommRingCatHom B S hS p₀).hom • ⊤)
    (W : SmallEtale B S hS Z.1) (f : W ⟶ (smallBaseChange B S hS i hci.rep).obj c) :
    IsIso ((homologyZeroTranspose i K F π).val.app (op W)) := by
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let N := (modulePushforward B S hS i).obj F
  have hN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_isAffineHom _ _ _ i haff F hF
  have hNK : spaceQuasicoherentProp B S hS X ((spaceDerivedSingle B S hS X 0).obj N) :=
    derivedCategoryB_singleFunctor_obj B S hS X.1 X.2 N hN
  let e := (@DerivedCategory.singleFunctorCompHomologyFunctorIso _ _
    (modulesAbelianSmallEtale B S hS X.1 X.2) (spaceHasDerivedCategory B S hS X) 0).app N
  let ψ : (spaceDerivedHomology B S hS X 0).obj K ⟶ N :=
    (spaceDerivedHomology B S hS X 0).map π ≫ e.hom
  let E0 := (Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge O c 0).app K
  let E1 := (Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge O c 0).app
    ((spaceDerivedSingle B S hS X 0).obj N)
  let h := (DerivedCategory.homologyFunctor _ 0).map
    ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections O c).map π)
  let ι0 := e.hom.val.app (op c)
  have hι0 : Function.Bijective ι0 := SheafOfModules.bijective_iso_hom_val_app e (op c)
  have hE0b : Function.Bijective E0 := (ConcreteCategory.isIso_iff_bijective E0).1
    (isIso_hypercohomologyEdge_app_of_isAffineChart B S hS X K hK c hc 0)
  have hE1b : Function.Bijective E1 := (ConcreteCategory.isIso_iff_bijective E1).1
    (isIso_hypercohomologyEdge_app_of_isAffineChart B S hS X _ hNK c hc 0)
  -- the naturality square of the edge map
  have hnat : ∀ w, ψ.val.app (op c) (E0 w) = ι0 (E1 (h w)) := by
    intro w
    have := congrArg (fun k => k w)
      ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge O c 0).naturality π)
    exact congrArg ι0 this.symm
  -- surjectivity and kernel of `ψ` over `c`
  have hψs : Function.Surjective (ψ.val.app (op c)) := by
    intro y
    obtain ⟨z, rfl⟩ := hι0.2 y
    obtain ⟨z', rfl⟩ := hE1b.2 z
    obtain ⟨w, rfl⟩ := hsurj z'
    exact ⟨E0 w, hnat w⟩
  let J : Ideal (chartRing B S hS X.1 X.2 c) :=
    (RingHom.ker (representedAffineCommRingCatHom B S hS p₀).hom).map
      (representedAffineCommRingCatHom B S hS (yoneda.preimage (c.1.hom ≫ hX))).hom
  have hψk : ∀ m, ψ.val.app (op c) m = 0 →
      m ∈ J • (⊤ : Submodule (chartRing B S hS X.1 X.2 c)
        (((spaceDerivedHomology B S hS X 0).obj K).val.obj (op c))) := by
    intro m hm
    obtain ⟨w, rfl⟩ := hE0b.2 m
    have hw : h w = 0 := by
      apply hE1b.1
      apply hι0.1
      rw [← hnat w, hm]
      exact (ι0.hom.map_zero).symm.trans (congrArg ι0.hom (E1.hom.map_zero).symm)
    have hw' := (SetLike.ext_iff.mp hker w).1 hw
    have hw'' := (ModuleCat.mem_smul_top_restrictScalars_iff _ _ _ w).1 hw'
    refine Submodule.smul_induction_on hw'' (fun a ha n _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  -- bijectivity over the base change `c ×_X Z`
  let d := smallBaseChangeDiagram i hci.rep c
  have : IsAffine (chartScheme c) := hc
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hci.rep.snd c.1.hom)) := hci.property_snd c.1.hom
  have hV : IsAffine ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) :=
    isAffine_smallBaseChange_obj B S hS i hci.rep haff c hc
  have hbij := bijective_homEquiv_symm_val_app_of_surjective i
    ((spaceDerivedHomology B S hS X 0).obj K) (hK 0) F ψ d hV hc
    (bijective_modulePushforwardCounitApp_smallBaseChangeDiagram i hci.rep F c)
    (Stacks.Pushout.surjective_appTop_of_isClosedImmersion (X := chartScheme c)
      ((BigFppfOver.toScheme B S hS).map (hci.rep.snd c.1.hom))) J
    (Ideal.map_le_iff_le_comap.2 fun a ha =>
      chartDiagramRestrict_appTop_eq_zero hX hZ p₀ i hsq d a ha)
    hψs hψk
  have hpb : ((modulePullback B S hS i).obj
      ((spaceDerivedHomology B S hS X 0).obj K)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS i _ (hK 0)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_val_app_of_bijective_affineChart hpb hF (homologyZeroTranspose i K F π) hV hbij W f)

end AlgebraicGeometry.Space

end
