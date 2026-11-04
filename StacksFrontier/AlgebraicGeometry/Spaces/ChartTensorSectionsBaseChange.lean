module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTensorSectionsTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsSingle
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTopDegreeUnit
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingEquivTransport
public import StacksFrontier.Algebra.Category.ModuleCat.SurjectiveKerSmulTop

/-!
# The base change of derived sections over an affine étale chart

Let `X` be an algebraic space over an affine `T` (ring `R`), `i : X₀ ⟶ X` an affine morphism over
an affine `T₀ ⟶ T` (ring map `R ⟶ R₀`), `F` a quasi-coherent `𝒪_{X₀}`-module with `i_*F`
quasi-coherent, and `φ : K ⟶ (i_*F)[0]`. Let `U` be an affine étale chart of `X`, with ring of
functions `Γ(U)` and ring map `ρ : R ⟶ Γ(U)`, and `U₀ = U ×_X X₀`. Suppose that the identification
`ψ_U` (`etaleTensorSectionsIdentification`) and the base change map
`c_U : RΓ_R(U, Lu^*K) ⊗^𝐋_R R₀ ⟶ RΓ_{R₀}(U₀, Lu₀^*(F[0]))` of [Stacks, Tag 0CX8]
(`etaleTensorSectionsBaseChangeMap`) are isomorphisms. Then, with `E = RΓ(U, K)` the derived
sections over the chart:

* (a) `Hⁱ(E|_R ⊗^𝐋_R R₀) = 0` for `i ≠ 0`: it is `Hⁱ(RΓ_{R₀}(U₀, Lu₀^*(F[0])))`, which is
  `Hⁱ(RΓ(U, (i_*F)[0]))` through the identification `ψ_U`, and that vanishes for `i ≠ 0`;
* (b) if moreover `Hⁱ(E) = 0` for `i > 0` and `R ⟶ R₀` is surjective, the map
  `H⁰(E) ⟶ H⁰(RΓ(U, (i_*F)[0]))` induced by `φ` is surjective with kernel
  `(ker(R → R₀) Γ(U)) • H⁰(E)`: up to isomorphisms it is the map induced on `H⁰` by the unit
  `E|_R ⟶ (E|_R ⊗^𝐋_R R₀)|_R`, which in the top degree is `m ↦ m ⊗ 1`
  (`StacksDraft.TopDegreeExtendScalars.ker_homology_unit`). The kernel is stated for the map read
  over `R`, as `ker(R → R₀) • H⁰(E)`.

These are the chart statements of [Stacks, Tag 0CX9], over variable spaces.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_extendScalars_derivedSections_of_isIso`: (a).
* `AlgebraicGeometry.Space.surjective_and_ker_homology_derivedSections_map_of_isIso`: (b).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasRightDerivedFunctor_chartSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T T₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
  {X X₀ U₀ : AlgebraicSpaces B S hS}
  (h : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
  (h₀ : X₀ ⟶ ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩)
  (g₀ : T₀ ⟶ T) (i₀ : X₀ ⟶ X) (w₀ : i₀ ≫ h = h₀ ≫ representedSpaceMap B S hS g₀)
  (hi₀ : IsAffineHom B S hS i₀.hom)
  (F : Modules.{u, u} B S hS X₀.1 X₀.2) (hF : F.IsQuasicoherentOnSite)
  (hFqc : ((modulePushforward B S hS i₀).obj F).IsQuasicoherentOnSite)
  (Uc : SmallEtale B S hS X.1)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Uc))]
  (g : (SmallEtale.toOver B S hS X.1).obj Uc ⟶ T)
  (wg : representedChartToSpace X Uc ≫ h = representedSpaceMap B S hS g)
  (j₀ : U₀ ⟶ X₀)
  (i' : U₀ ⟶ ⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj Uc),
    isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj Uc)⟩)
  (sq : IsPullback i' j₀ (representedChartToSpace X Uc) i₀)
  (hjqc : IsQuasiCompact B S hS (representedChartToSpace X Uc).hom)
  (hjqs : IsQuasiSeparated B S hS (representedChartToSpace X Uc).hom)
  {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  (φ : K ⟶ (DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F))

include wg in
/-- **(a): `Hⁱ(RΓ(U, K)|_R ⊗^𝐋_R R₀) = 0` for `i ≠ 0`**, when the base change map `c_U` of
[Stacks, Tag 0CX8] is an isomorphism. -/
theorem isZero_homology_extendScalars_derivedSections_of_isIso
    (hc : IsIso (etaleTensorSectionsBaseChangeMap B S hS h h₀ g₀ i₀ w₀ hi₀ F hF
      (representedChartToSpace X Uc) j₀ i' sq.w hjqc hjqs
      (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS _ hFqc) φ))
    (hψ : IsIso (etaleTensorSectionsIdentification B S hS h h₀ g₀ i₀ w₀ hi₀ F hF
      (representedChartToSpace X Uc) j₀ i' sq.w hjqc hjqs
      (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS _ hFqc)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).functor.obj
        ((ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.obj
          ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) Uc).obj
              K)))) := by
  have hG := StacksDraft.isZero_homology_restrictScalars
    (representedAffineCommRingCatHom B S hS g).hom _ i
    (isZero_homology_derivedSections_single X Uc _ hFqc i hi)
  have hN := IsZero.of_iso hG ((DerivedCategory.homologyFunctor _ i).mapIso
    ((chartDerivedSectionsPushforwardIso X Uc h g wg).app
      ((DerivedCategory.singleFunctor _ 0).obj ((modulePushforward B S hS i₀).obj F)))).symm
  have hP := StacksDraft.isZero_homology_of_isZero_homology_restrictScalars
    (representedAffineCommRingCatHom B S hS g₀).hom _ i
    (IsZero.of_iso hN ((DerivedCategory.homologyFunctor _ i).mapIso (@asIso _ _ _ _ _ hψ)).symm)
  exact IsZero.of_iso hP ((DerivedCategory.homologyFunctor _ i).mapIso
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS g₀).hom).functor.mapIso
        ((chartDerivedSectionsPushforwardIso X Uc h g wg).app K) ≪≫ @asIso _ _ _ _ _ hc))

include wg in
/-- **(b): `H⁰(RΓ(U, K)) ⟶ H⁰(RΓ(U, (i_*F)[0]))` is surjective with kernel
`(ker(R → R₀) Γ(U)) • ⊤`**, when the base change map `c_U` of [Stacks, Tag 0CX8] is an isomorphism,
`R ⟶ R₀` is surjective and `RΓ(U, K)` has no cohomology in positive degrees: up to isomorphisms of
the source and the target, the map is `H⁰` of the unit `M ⟶ (M ⊗^𝐋_R R₀)|_R` at `M = RΓ(U, K)|_R`.
-/
theorem surjective_and_ker_homology_derivedSections_map_of_isIso
    (hc : IsIso (etaleTensorSectionsBaseChangeMap B S hS h h₀ g₀ i₀ w₀ hi₀ F hF
      (representedChartToSpace X Uc) j₀ i' sq.w hjqc hjqs
      (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS _ hFqc) φ))
    (hψ : IsIso (etaleTensorSectionsIdentification B S hS h h₀ g₀ i₀ w₀ hi₀ F hF
      (representedChartToSpace X Uc) j₀ i' sq.w hjqc hjqs
      (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS _ hFqc)))
    (hg₀ : Function.Surjective (representedAffineCommRingCatHom B S hS g₀).hom)
    (hle : ∀ i > 0, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) Uc).obj
          K))) :
    Function.Surjective ((DerivedCategory.homologyFunctor _ 0).map
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) Uc).map
            φ)) ∧
      LinearMap.ker ((ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS g).hom).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structurePresheaf B S hS X.1).obj (op Uc))) 0).map
          ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) Uc).map
              φ))).hom =
        RingHom.ker (representedAffineCommRingCatHom B S hS g₀).hom • ⊤ := by
  let ρ := (representedAffineCommRingCatHom B S hS g).hom
  let g₀' := (representedAffineCommRingCatHom B S hS g₀).hom
  let α := chartDerivedSectionsPushforwardIso X Uc h g wg
  let x := (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) Uc).map φ
  let ψU := @asIso _ _ _ _ _ hψ
  let cU := @asIso _ _ _ _ _ hc
  let adj := RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction g₀'
  let resD := (ModuleCat.restrictScalars g₀').mapDerivedCategory
  let M := (smallEtaleDerivedModulePullback B S hS (representedChartToSpace X Uc) ⋙
    derivedModulePushforward B S hS (representedChartToSpace X Uc ≫ h) ⋙
      representedAffineDerivedSections B S hS T).obj K
  have htr := etaleTensorSectionsBaseChangeMap_transpose B S hS h h₀ g₀ i₀ w₀ hi₀ F hF
    (representedChartToSpace X Uc) j₀ i' sq.w hjqc hjqs
    (qcohDerived_singleFunctor_of_isQuasicoherentOnSite B S hS _ hFqc) φ
  have key : (ModuleCat.restrictScalars ρ).mapDerivedCategory.map x ≫
      (α.app _ ≪≫ ψU).hom = (α.app K).hom ≫ (adj.unit.app M ≫ resD.map cU.hom) := by
    have h₀' := congrArg (· ≫ ψU.hom) (α.hom.naturality φ)
    simp only [Category.assoc] at h₀'
    exact h₀'.trans (congrArg ((α.app K).hom ≫ ·) htr)
  have : M.IsLE 0 := (DerivedCategory.isLE_iff M 0).2 fun i hi =>
    IsZero.of_iso (StacksDraft.isZero_homology_restrictScalars ρ _ i (hle i hi))
      ((DerivedCategory.homologyFunctor _ i).mapIso (α.app K)).symm
  have h₁ := ModuleCat.surjective_and_ker_eq_comp_iso
    ((DerivedCategory.homologyFunctor _ 0).map (adj.unit.app M))
    ((DerivedCategory.homologyFunctor _ 0).mapIso (resD.mapIso cU)) _
    (StacksDraft.TopDegreeExtendScalars.surjective_homology_unit g₀' M hg₀)
    (StacksDraft.TopDegreeExtendScalars.ker_homology_unit g₀' M hg₀)
  have h₂ := ModuleCat.surjective_and_ker_eq_of_comm
    ((DerivedCategory.homologyFunctor _ 0).map
      ((ModuleCat.restrictScalars ρ).mapDerivedCategory.map x))
    ((DerivedCategory.homologyFunctor _ 0).map (adj.unit.app M) ≫
      ((DerivedCategory.homologyFunctor _ 0).mapIso (resD.mapIso cU)).hom)
    ((DerivedCategory.homologyFunctor _ 0).mapIso (α.app K))
    ((DerivedCategory.homologyFunctor _ 0).mapIso (α.app _ ≪≫ ψU))
    (((DerivedCategory.homologyFunctor _ 0).map_comp _ _).symm.trans
      ((congrArg (DerivedCategory.homologyFunctor _ 0).map key).trans
        (((DerivedCategory.homologyFunctor _ 0).map_comp _ _).trans
          (congrArg (_ ≫ ·) ((DerivedCategory.homologyFunctor _ 0).map_comp _ _)))))
    _ h₁.1 h₁.2
  exact ModuleCat.surjective_and_ker_eq_of_comm
    ((ModuleCat.restrictScalars ρ).map ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structurePresheaf B S hS X.1).obj (op Uc))) 0).map x))
    ((DerivedCategory.homologyFunctor _ 0).map
      ((ModuleCat.restrictScalars ρ).mapDerivedCategory.map x))
    (((ModuleCat.restrictScalars ρ).mapDerivedCategoryHomologyIso 0).app _).symm
    (((ModuleCat.restrictScalars ρ).mapDerivedCategoryHomologyIso 0).app _).symm
    (((ModuleCat.restrictScalars ρ).mapDerivedCategoryHomologyIso 0).inv.naturality x) _ h₂.1 h₂.2

end AlgebraicGeometry.Space

end
