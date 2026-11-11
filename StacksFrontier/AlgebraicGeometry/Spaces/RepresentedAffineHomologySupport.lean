module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsAnnihilatorSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealQuotientSpecClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport

/-!
# Supports of the cohomology sheaves of an object of `D_QCoh` on an affine scheme

Let `U` be an object of the big fppf site over `S` with affine underlying scheme, `R = Γ(U, 𝒪)`,
and `E ∈ D_QCoh(𝒪_{h_U})`, so that `Hⁱ(RΓ(E)) = Γ(h_U, Hⁱ(E))`. This file compares the supports
of the cohomology sheaves `Hⁱ(E)` with the supports of the `R`-modules `Hⁱ(RΓ(E))`:

* if an ideal `J ⊆ R` kills every `Hⁱ(RΓ(E))`, then `E` is supported on the image of
  `Spec (R ⧸ J) ⟶ h_U`;
* if `E` is supported on a set `T` of points of `h_U`, then every prime of the support of the
  `R`-module `Hⁱ(RΓ(E))` comes from a point of `T`.

## Main results

* `AlgebraicGeometry.Space.cohomologySupportedOn_range_idealQuotientSpecMap`
* `AlgebraicGeometry.Space.pointsEquivScheme_symm_mem_of_mem_support_homology`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] pointTopology
attribute [local instance] HasDerivedCategory.standard

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- A point of an affine chart whose prime lies in the support of a module linearly isomorphic to
the sections over the chart of a quasi-coherent module lies in the support of its restriction. -/
theorem mem_supp_restrictToChart_of_linearEquiv (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) [IsAffine (chartScheme A)]
    {N : Type u} [AddCommGroup N] {_ : Module Γ(chartScheme A, ⊤) N}
    (ψ : M.val.obj (op A) ≃ₗ[Γ(chartScheme A, ⊤)] N) (x : chartScheme A)
    (hx : (chartScheme A).isoSpec.hom x ∈ Module.support Γ(chartScheme A, ⊤) N) :
    x ∈ SheafOfModules.supp (restrictToChart B S hS X.2 M A) := by
  let G : (chartScheme A).Modules := @id (chartScheme A).Modules (restrictToChart B S hS X.2 M A)
  have : G.IsQuasicoherent := isQuasicoherent_restrictToChart B S hS X M hM A
  let φ : (Γ(G, ⊤) : Type u) ≃ₗ[Γ(chartScheme A, ⊤)] (M.val.obj (op A) : Type u) :=
    ((moduleGlobalSections (chartScheme A)).mapIso
        (restrictToChartIsoChartRestrictionSheaf B S hS X M A)).toLinearEquiv.trans
      (chartRestrictionSheafTopEquiv B S hS X M A).symm
  have hxG : x ∈ SheafOfModules.supp G := by
    rw [← mem_support_sections_iff_mem_supp_top, (φ.trans ψ).support_eq]
    exact hx
  exact hxG

/-- Sections over a chart linearly isomorphic to a module killed by `J` are killed by `J`. -/
theorem smul_eq_zero_of_linearEquiv (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) {N : Type u} [AddCommGroup N] {_ : Module Γ(chartScheme A, ⊤) N}
    (ψ : M.val.obj (op A) ≃ₗ[Γ(chartScheme A, ⊤)] N) (J : Ideal Γ(chartScheme A, ⊤))
    (hN : ∀ r ∈ J, ∀ n : N, r • n = 0) : ∀ r ∈ J, ∀ s : M.val.obj (op A), r • s = 0 := by
  intro r hr s
  apply ψ.injective
  rw [map_smul, hN r hr, map_zero]

end Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The sections over the self chart of `Hⁱ(E)` are `Hⁱ(RΓ(E))`, linearly over `Γ(U, 𝒪)`. -/
def selfChartHomologyIso
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E) (i : ℤ) :
    selfChartSections B S hS U ((DerivedCategory.homologyFunctor _ i).obj E) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
        i).obj ((representedAffineDerivedSections B S hS U).obj E) :=
  (selfChartSectionsIso B S hS U).app _ ≪≫
    (representedAffineDerivedSectionsHomologyIso B S hS U E hE i).symm

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- On the self chart, `pointsMap` of the chart morphism is the identification of points. -/
theorem pointsMap_selfChart (y : (BigFppfOver.toScheme B S hS).obj U) :
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS (yoneda.obj U)).obj
        (selfChart B S hS U))) (selfChart B S hS U).obj.hom
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS (yoneda.obj U)).obj
        (selfChart B S hS U))).symm y) = (pointsEquivScheme B S hS U).symm y := by
  change pointsMap B S hS _ (𝟙 _) ((pointsEquivScheme B S hS U).symm y) = _
  rw [pointsMap_id, id_eq]

/-- **An ideal killing the cohomology of `RΓ(E)` cuts out a support of `E`.** If `J ⊆ Γ(U, 𝒪)`
kills every `Hⁱ(RΓ(E))`, then every cohomology sheaf of `E` is supported on the image of
`Spec (Γ(U, 𝒪) ⧸ J) ⟶ h_U`. -/
theorem cohomologySupportedOn_range_idealQuotientSpecMap
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E)
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (hJ : ∀ i : ℤ, ∀ r ∈ J, ∀ s : (DerivedCategory.homologyFunctor
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) i).obj
      ((representedAffineDerivedSections B S hS U).obj E), r • s = 0) :
    CohomologySupportedOn B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (Set.range (pointsMap B S hS _ (yoneda.map (idealQuotientSpecMap B S hS J)))) E := by
  intro i p hp
  let X : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let F := (DerivedCategory.homologyFunctor _ i).obj E
  have hFq : F.IsQuasicoherentOnSite := hE i
  have : IsAffine (chartScheme (selfChart B S hS U)) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  let y := pointsEquivScheme B S hS U p
  have hpy := pointsMap_selfChart B S hS U y
  rw [Equiv.symm_apply_apply] at hpy
  have hy : y ∈ SheafOfModules.supp (restrictToChart B S hS X.2 F (selfChart B S hS U)) := by
    rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X
      (selfChart B S hS U) F]
    change pointsMap B S hS _ _ _ ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)
    rw [hpy]
    exact hp
  obtain ⟨z, hz⟩ := pointsEquivScheme_symm_mem_range_idealQuotientSpecMap B S hS J y
    (isoSpec_mem_zeroLocus_of_mem_supp_restrictToChart B S hS X F hFq (selfChart B S hS U) J
      (smul_eq_zero_of_linearEquiv B S hS X F (selfChart B S hS U)
        (selfChartHomologyIso B S hS U E hE i).toLinearEquiv J (hJ i)) y hy)
  exact ⟨z, hz.trans (Equiv.symm_apply_apply _ _)⟩

/-- **A support of `E` contains the supports of the cohomology of `RΓ(E)`.** If every cohomology
sheaf of `E` is supported on `T`, then every point `x` of `U` whose prime lies in the support of
the `Γ(U, 𝒪)`-module `Hⁱ(RΓ(E))` is, as a point of `h_U`, in `T`. -/
theorem pointsEquivScheme_symm_mem_of_mem_support_homology
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E)
    (T : Set (points B S hS (yoneda.obj U)))
    (hT : CohomologySupportedOn B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) T E)
    (i : ℤ) (x : (BigFppfOver.toScheme B S hS).obj U)
    (hx : ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom x ∈
      Module.support Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) i).obj
          ((representedAffineDerivedSections B S hS U).obj E))) :
    (pointsEquivScheme B S hS U).symm x ∈ T := by
  let X : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let M := (DerivedCategory.homologyFunctor _ i).obj E
  have hMq : M.IsQuasicoherentOnSite := hE i
  have : IsAffine (chartScheme (selfChart B S hS U)) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  have hxM : x ∈ SheafOfModules.supp (restrictToChart B S hS X.2 M (selfChart B S hS U)) :=
    mem_supp_restrictToChart_of_linearEquiv B S hS X M hMq (selfChart B S hS U)
      (selfChartHomologyIso B S hS U E hE i).toLinearEquiv x hx
  rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X
    (selfChart B S hS U) M] at hxM
  rw [← pointsMap_selfChart B S hS U x]
  exact hT i hxM

end AlgebraicGeometry.Space

end
