module

public import StacksFrontier.Algebra.Module.Projective.InvertibleOfFibres
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResidueFibreCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineSectionsFlat

/-!
# Modules whose fibres are invertible

Let `f : X ⟶ T` be a morphism from an algebraic space to a scheme and `𝓕` a quasi-coherent
`𝒪_X`-module, flat over `T` and of finite presentation on the affine étale charts of `X`. If for
every point `s ∈ T` the pullback of `𝓕` to the fibre `X_s` is invertible, then `𝓕` is invertible.

Everything is local. On an affine étale chart `U` of `X` over an affine open `O` of `T`, with
`A = Γ(U)`, `R = Γ(O)` and `M = Γ(U, 𝓕)`, the chart `U ×_O Spec κ(s)` of the fibre is the
spectrum of `A' = A ⊗_R κ(s)`, and the pullback of `𝓕` to it is the module associated with
`A' ⊗_A M`, which is therefore invertible over `A'`. The algebra is
`Module.nonempty_linearEquiv_localizedModule_of_invertible_baseChange`: `M` is free of rank one at
every prime of `A`, hence invertible, and so is `𝓕` on `U`. Such charts form an étale covering
of `X`, along which invertibility descends.

## Main results

* `AlgebraicGeometry.Space.OpenAffineChartSquare.module_invertible_chartSections`:
  the sections over an affine chart over an affine open are an invertible module.
* `AlgebraicGeometry.Space.isInvertibleModule_of_isInvertibleModule_residueFibre`: the
  statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} {f : X ⟶ representedSpace T}

namespace OpenAffineChartSquare

variable (c : OpenAffineChartSquare f)

/-- The sections `Γ(U, 𝓕)` of a module over the affine chart of an `OpenAffineChartSquare`. -/
abbrev chartSections (F : Modules.{u, u} B S hS X.1 X.2) :
    ModuleCat.{u} Γ(chartScheme c.toChartDiagram.U, ⊤) :=
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj c.U)) :=
    c.isAffine_U
  (representedAffineSections B S hS ((SmallEtale.toOver B S hS X.1).obj c.U)).obj
    ((modulePullback B S hS (chartToSpace B S hS X c.U)).obj F)

/-- **The sections over an affine chart are invertible.** Let `𝓕` be quasi-coherent, flat over
`T`, with finitely presented sections over the chart `U` of `c`, and with invertible pullbacks to
the fibres of `f`. Then `Γ(U, 𝓕)` is an invertible `Γ(U)`-module. -/
theorem module_invertible_chartSections (F : Modules.{u, u} B S hS X.1 X.2)
    (hFq : F.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS X.2 f.hom F)
    (hfp : Module.FinitePresentation Γ(chartScheme c.toChartDiagram.U, ⊤) (c.chartSections F))
    (hfib : ∀ s, IsInvertibleModule (residueFibre f s)
      ((modulePullback B S hS (residueFibreι f s)).obj F)) :
    Module.Invertible Γ(chartScheme c.toChartDiagram.U, ⊤) (c.chartSections F) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj c.U)) :=
    c.isAffine_U
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj c.U.obj.left) := c.isAffine_U
  let M := c.chartSections F
  let gR := ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤) :=
    gR.toAlgebra
  let : Module Γ(chartScheme c.toChartDiagram.V, ⊤) M := Module.compHom M gR
  have : IsScalarTower Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ(chartScheme c.toChartDiagram.U, ⊤) M :=
    ⟨fun r a m => mul_smul (gR r) a m⟩
  have hMflat : Module.Flat Γ(chartScheme c.toChartDiagram.V, ⊤) M :=
    flat_representedAffineSections_modulePullback_of_isFlatOver B S hS f F hFq hflat
      (chartToSpace B S hS X c.U) (isEtale_chartToSpace B S hS X c.U)
      (chartToSpace B S hS (representedSpace T) c.toChartDiagram.V)
      (isEtale_chartToSpace B S hS (representedSpace T) c.toChartDiagram.V)
      c.toChartDiagram.g (chartToSpace_comp_eq f c.toChartDiagram).symm
  refine Module.invertible_of_forall_nonempty_linearEquiv_localizedModule fun q _ => ?_
  let p : PrimeSpectrum Γ(chartScheme c.toChartDiagram.V, ⊤) :=
    ⟨q.comap (algebraMap Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤)),
      Ideal.comap_isPrime _ _⟩
  obtain ⟨s, hs, hker⟩ := c.exists_ker_residuePoint_eq p
  have := c.isAffine_residueFibreChart s hs
  let : Field Γ((BigFppfOver.toScheme B S hS).obj
      ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤) :=
    (isField_siteObject s).toField
  have hsq := c.isPullback_residueFibreChart s hs
  let ℓR := (c.residuePoint s hs).appTop.hom
  let qR := ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s c.U)).appTop.hom
  let rR := ((BigFppfOver.toScheme B S hS).map (residueFibreChartSnd f s c.U)).appTop.hom
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤) :=
    ℓR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := qR.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := rR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := (qR.comp gR).toAlgebra
  have hw : qR.comp gR = rR.comp ℓR := by
    have h1 : ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s c.U) ≫
        (BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom = qR.comp gR := by
      rw [Scheme.Hom.comp_appTop]; rfl
    have h2 : ((BigFppfOver.toScheme B S hS).map (residueFibreChartSnd f s c.U) ≫
        c.residuePoint s hs).appTop.hom = rR.comp ℓR := by
      rw [Scheme.Hom.comp_appTop]; rfl
    rw [← h1, ← h2, hsq.w]
  have : IsScalarTower Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hw x)
  have : Algebra.IsPushout Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    (CommRingCat.isPushout_iff_isPushout).1 (isPushout_appTop_of_isPullback hsq)
  let W := residueFibreChart f s c.U
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) :=
    c.isAffine_residueFibreChart s hs
  have hW := modulePullbackInvertible
    (chartToSpace B S hS (residueFibre f s) W) _ (hfib s)
  have hPq : ((modulePullback B S hS (chartToSpace B S hS X c.U)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F hFq
  have := isIso_representedAffineAssociatedAdjunction_counit_app B S hS
    (U := (SmallEtale.toOver B S hS X.1).obj c.U) _ hPq
  let e₁ : (modulePullback B S hS (chartToSpace B S hS (residueFibre f s) W)).obj
        ((modulePullback B S hS (residueFibreι f s)).obj F) ≅
      (modulePullback B S hS (representedSpaceMap B S hS (residueFibreChartFst f s c.U))).obj
        ((modulePullback B S hS (chartToSpace B S hS X c.U)).obj F) :=
    (modulePullbackCompIso B S hS _ _).app F ≪≫
      eqToIso (congrArg (fun φ => (modulePullback B S hS φ).obj F)
        (chartToSpace_residueFibreChart_comp f s c.U)) ≪≫
      ((modulePullbackCompIso B S hS _ _).app F).symm
  let e₂ := (modulePullback B S hS
      (representedSpaceMap B S hS (residueFibreChartFst f s c.U))).mapIso
      (asIso ((representedAffineAssociatedAdjunction B S hS
        ((SmallEtale.toOver B S hS X.1).obj c.U)).counit.app
          ((modulePullback B S hS (chartToSpace B S hS X c.U)).obj F))).symm
  let e₃ := (representedAffineAssociatedModulePullbackIso B S hS
      (residueFibreChartFst f s c.U)).app M
  have : Module.Invertible Γ(chartScheme (residueFibreChart f s c.U), ⊤)
      (Γ(chartScheme (residueFibreChart f s c.U), ⊤) ⊗[Γ(chartScheme c.toChartDiagram.U, ⊤)] M) :=
    (isInvertibleModule_representedAffineAssociated_iff B S hS W.1.left _).1
      (isInvertibleModule_of_iso (e₁ ≪≫ e₂ ≪≫ e₃) hW)
  exact Module.nonempty_linearEquiv_localizedModule_of_invertible_baseChange
    (R := Γ(chartScheme c.toChartDiagram.V, ⊤)) (k := Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤))
    (A' := Γ(chartScheme (residueFibreChart f s c.U), ⊤)) M q hker.symm

end OpenAffineChartSquare

/-- **A module whose fibres are invertible is invertible.** Let `f : X ⟶ T` be a morphism from an
algebraic space to a scheme and `𝓕` a quasi-coherent `𝒪_X`-module, flat over `T`, whose sections
over the affine étale charts of `X` over affine opens of `T` are finitely presented. If the
pullback of `𝓕` to every fibre `X_s` is invertible, then `𝓕` is invertible. -/
theorem isInvertibleModule_of_isInvertibleModule_residueFibre (F : Modules.{u, u} B S hS X.1 X.2)
    (hFq : F.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS X.2 f.hom F)
    (hfp : ∀ c : OpenAffineChartSquare f,
      Module.FinitePresentation Γ(chartScheme c.toChartDiagram.U, ⊤) (c.chartSections F))
    (hfib : ∀ s, IsInvertibleModule (residueFibre f s)
      ((modulePullback B S hS (residueFibreι f s)).obj F)) :
    IsInvertibleModule X F := by
  refine isInvertibleModule_of_pullback_isFpqcCovering B S hS
    (fun c : OpenAffineChartSquare f => chartToSpace B S hS X c.U) ?_ F hFq fun c => ?_
  · refine isFpqcCovering_of_isEtaleCovering B S hS _ _
      ⟨X.2, fun c => (chartSpace B S hS X c.U).2, fun c => isEtale_chartToSpace B S hS X c.U, ?_⟩
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨O, hO, hxO, -⟩ := exists_isAffineOpen_mem_and_subset
      (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens))
      (x := pointsToScheme B S hS T (pointsMap B S hS _ f.hom x)) trivial
    obtain ⟨c, -, hxc⟩ := OpenAffineChartSquare.exists_of_mem x O hO hxO
    exact Set.mem_iUnion.2 ⟨c, hxc⟩
  · have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj c.U)) := c.isAffine_U
    have hPq : ((modulePullback B S hS (chartToSpace B S hS X c.U)).obj F).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F hFq
    have hI := isIso_representedAffineAssociatedAdjunction_counit_app B S hS
      (U := (SmallEtale.toOver B S hS X.1).obj c.U) _ hPq
    exact isInvertibleModule_of_iso (@asIso _ _ _ _ _ hI)
      ((isInvertibleModule_representedAffineAssociated_iff B S hS _ _).2
        (c.module_invertible_chartSections F hFq hflat (hfp c) hfib))

end AlgebraicGeometry.Space
