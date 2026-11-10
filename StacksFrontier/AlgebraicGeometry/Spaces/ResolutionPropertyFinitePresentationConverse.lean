module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealComplementSectionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyIdealDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardIdealPowSmulQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertySurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyTraceFiniteType

/-!
# The resolution property from a finite locally free cover of `π_*ℐ`, without Noetherian hypotheses

In the situation of [Stacks, Tag 0GUY] — a quasi-compact and quasi-separated algebraic space `X`,
a surjective étale `φ = π ∘ j : V ⟶ X` from an affine scheme with `j` an open immersion and `π`
finite, and a finite type quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y` with `V(ℐ) = Y ∖ j(V)` —
assume that `π_*𝒪_Y` is of finite presentation and that `π_*ℐ` is a quotient of a finite locally
free `𝒪_X`-module.  Then `X` has the resolution property.

## Main results

* `hasResolutionProperty_of_epi_idealDirectImage_of_isFinitePresentationOnSite`: if `π_*𝒪_Y` is of
  finite presentation and `π_*ℐ` is a quotient of a finite locally free module, then `X` has the
  resolution property.

## References

* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 01PN](https://stacks.math.columbia.edu/tag/01PN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

/-- The abelian category of modules over an algebraic space, at the universes `u, u`. -/
noncomputable local instance (priority := high) abelianModules_finitePresentationConverse
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- In the situation of Stacks 0GUY the algebraic space `Y` is quasi-compact: `π` is finite. -/
theorem isQuasiCompactSpace_Y_of_resolutionSituation : IsQuasiCompactSpace B S hS D.Y.1 :=
  have hπ := ((isFinite_iff_isAffineHom_and_isProper B S hS D.Y.2 X.2 D.π).1 D.isFinite_π).2
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hqc hπ.2.1.2

/-- In the situation of Stacks 0GUY the algebraic space `Y` is quasi-separated: `π` is
separated. -/
theorem isAbsolutelyQuasiSeparated_Y_of_resolutionSituation :
    IsAbsolutelyQuasiSeparated B S hS hZ D.Y.1 :=
  have hπ := ((isFinite_iff_isAffineHom_and_isProper B S hS D.Y.2 X.2 D.π).1 D.isFinite_π).2
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ D.Y.2 hqs
    (isQuasiSeparated_of_isSeparated B S hS hπ.1)

/-- In the situation of Stacks 0GUY the open complement `Y ∖ V(ℐ)` is quasi-compact: it is the
affine scheme `V`. -/
theorem isQuasiCompactSpace_idealComplement_of_resolutionSituation :
    IsQuasiCompactSpace B S hS (idealComplement B S hS D.Y D.I).1 := by
  obtain ⟨e, -⟩ := exists_iso_idealComplement_comp_eq B S hS hZ X hqc hqs D
  have hV := (isQuasiCompactSpace_iff_compactSpace_points B S hS _
    (isAlgebraicSpace_yoneda B S hS D.V)).mp
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS D.V D.isAffine_V)
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS _
    (idealComplement B S hS D.Y D.I).2).mpr ⟨?_⟩
  have hr : Set.range (pointsMap B S hS _ e.hom) = Set.univ :=
    Set.eq_univ_of_forall fun y => ⟨pointsMap B S hS _ e.inv y, by
      rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id]; rfl⟩
  rw [← hr]
  exact isCompact_range (continuous_pointsMap B S hS e.hom)

/-- In the situation of Stacks 0GUY, for a finite type quasi-coherent `𝒪_Y`-module `𝒢` there are
finitely many quasi-coherent `𝒬_l`, epimorphisms `ρ_l : 𝒬_l ⟶ ℐ^{n_l+1}` with kernel killed by
`ℐ^{a_l+1}`, and maps `q_l : 𝒬_l ⟶ 𝒢` such that the maps `ℐ^{a_l+1}𝒬_l ⟶ 𝒢` are jointly
epimorphic over `U = Y ∖ V(ℐ)`. -/
theorem exists_idealPowModule_extensions_eq_zero_of_restrict (G : Modules.{u, u} B S hS D.Y.1 D.Y.2)
    (hGq : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G) :
    ∃ (r : ℕ) (Q : Fin r → Modules.{u, u} B S hS D.Y.1 D.Y.2)
      (_ : ∀ l, (Q l).IsQuasicoherentOnSite) (n a : Fin r → ℕ)
      (ρ : ∀ l, Q l ⟶ idealSheafPowModule B S hS D.Y D.I (n l + 1)) (_ : ∀ l, Epi (ρ l))
      (_ : ∀ l (W : (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).Cᵒᵖ)
        (c : (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj.obj W),
        c ∈ (SheafOfModules.idealSheafPow D.I (a l + 1)).obj W →
          ∀ k : (Q l).val.obj W, ((ρ l).val.app W).hom k = 0 → c • k = 0)
      (q : ∀ l, Q l ⟶ G),
      ∀ ⦃Z : Modules.{u, u} B S hS (idealComplement B S hS D.Y D.I).1
          (idealComplement B S hS D.Y D.I).2⦄
        (d : (restrictToIdealComplement B S hS D.Y D.I).obj G ⟶ Z),
        (∀ l, (restrictToIdealComplement B S hS D.Y D.I).map
          (idealPowModuleι D.I (a l + 1) (Q l) ≫ q l) ≫ d = 0) → d = 0 := by
  obtain ⟨e, -⟩ := exists_iso_idealComplement_comp_eq B S hS hZ X hqc hqs D
  have hι := isEtale_idealComplementι B S hS D.Y D.I
  have hGUq : ((restrictToIdealComplement B S hS D.Y D.I).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS _ hι G hGq
  have hGUft : SheafOfModules.IsFiniteTypeOnSite
      ((restrictToIdealComplement B S hS D.Y D.I).obj G) :=
    isFiniteTypeOnSite_etaleModulePullback B S hS _ hι G hGft
  obtain ⟨r, θ, hθ⟩ := exists_unit_homs_of_isTerminal_of_isFiniteTypeOnSite B S hS
    (idealComplement B S hS D.Y D.I) (isTerminal_isoChart B S hS e) D.isAffine_V _ hGUq hGUft
  choose Q hQ n a ρ hρ hkill q hext using fun l => exists_idealPowModule_extension_of_section
    B S hS D.Y D.I hZ (isQuasiCompactSpace_Y_of_resolutionSituation B S hS hZ X hqc hqs D)
    (isAbsolutelyQuasiSeparated_Y_of_resolutionSituation B S hS hZ X hqc hqs D)
    (isQuasiCompactSpace_idealComplement_of_resolutionSituation B S hS hZ X hqc hqs D)
    D.isFiniteTypeQuasicoherent_I G hGq (θ l)
  exact ⟨r, Q, hQ, n, a, ρ, hρ, hkill, q, fun Z d hd => hθ d fun l => hext l d (hd l)⟩

/-- A finite direct sum of quasi-coherent modules on an algebraic space is quasi-coherent. -/
theorem isQuasicoherentOnSite_biproduct {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {r : ℕ} (N : Fin r → Modules.{u, u} B S hS F hF)
    [HasBiproduct N] (hN : ∀ l, (N l).IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, u} (⨁ N) := by
  have h1 : HasColimitsOfShape (Discrete (Fin r)) (Modules.{u, u} B S hS F hF) :=
    @HasFiniteCoproducts.out _ _ (@hasFiniteCoproducts_of_hasFiniteBiproducts _ _ _ inferInstance) r
  have h2 := @isClosedUnderColimitsOfShape_discrete_quasicoherentSheaves.{u, 0} B S hS F hF (Fin r)
    h1
  exact ObjectProperty.prop_of_isColimit _ (biproduct.isColimit N) fun j => hN j.as

/-- **The cokernel of finitely many maps into a finite type module, jointly epimorphic over
`Y ∖ V(ℐ)`, is killed by a power of `ℐ`**, section by section (Stacks 07UK without Noetherian
hypotheses, `AlgebraicGeometry.Space.exists_smul_eq_zero_of_isZero_restrictToIdealComplement`). -/
theorem exists_smul_cokernel_eq_zero_of_restrict {r : ℕ}
    (N : Fin r → Modules.{u, u} B S hS D.Y.1 D.Y.2) [HasBiproduct N]
    (hN : ∀ l, (N l).IsQuasicoherentOnSite) (G : Modules.{u, u} B S hS D.Y.1 D.Y.2)
    (hGq : G.IsQuasicoherentOnSite)
    (hGft : SheafOfModules.IsFiniteTypeOnSite G) (lam : ∀ l, N l ⟶ G)
    (hgen : ∀ ⦃Z : Modules.{u, u} B S hS (idealComplement B S hS D.Y D.I).1
        (idealComplement B S hS D.Y D.I).2⦄
      (d : (restrictToIdealComplement B S hS D.Y D.I).obj G ⟶ Z),
      (∀ l, (restrictToIdealComplement B S hS D.Y D.I).map (lam l) ≫ d = 0) → d = 0) :
    ∃ m : ℕ, ∀ (W : (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).Cᵒᵖ)
      (c : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj.obj W),
      c ∈ (SheafOfModules.idealSheafPow D.I m).obj W →
        ∀ x : (cokernel (biproduct.desc lam)).val.obj W, c • x = 0 := by
  have hι := isEtale_idealComplementι B S hS D.Y D.I
  have : PreservesColimits (restrictToIdealComplement B S hS D.Y D.I) :=
    (etaleModulePullbackAdjunction B S hS (idealComplementι B S hS D.Y D.I)
      hι).leftAdjoint_preservesColimits
  have hepi : Epi ((restrictToIdealComplement B S hS D.Y D.I).map (biproduct.desc lam)) := by
    refine Preadditive.epi_of_cancel_zero _ fun {Z} d hd => hgen d fun l => ?_
    have h := congrArg (fun k => (restrictToIdealComplement B S hS D.Y D.I).map
      (biproduct.ι N l) ≫ k) hd
    simpa only [comp_zero, ← Category.assoc, ← Functor.map_comp, biproduct.ι_desc] using h
  have hz : IsZero
      ((restrictToIdealComplement B S hS D.Y D.I).obj (cokernel (biproduct.desc lam))) :=
    IsZero.of_iso (isZero_cokernel_of_epi _)
      (PreservesCokernel.iso (restrictToIdealComplement B S hS D.Y D.I) _)
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS D.Y.1 D.Y.2
  have hCq : (cokernel (biproduct.desc lam)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_cokernel _ _ (isQuasicoherentOnSite_biproduct B S hS N hN) hGq
  have hCft : SheafOfModules.IsFiniteTypeOnSite (cokernel (biproduct.desc lam)) :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi (cokernel.π _) hGft
  exact exists_smul_eq_zero_of_isZero_restrictToIdealComplement B S hS D.Y
    (isQuasiCompactSpace_Y_of_resolutionSituation B S hS hZ X hqc hqs D) D.I
    D.isFiniteTypeQuasicoherent_I _ hCq hCft hz

/-- **Surjectivity descends from the chart.**  In the situation of Stacks 0GUY the étale
`φ = π ∘ j : V ⟶ X` is surjective, so a map of `𝒪_X`-modules which is an epimorphism after
restriction to `V` is an epimorphism. -/
theorem epi_of_epi_etaleModulePullback_chartHom_map {M N : Modules.{u, u} B S hS X.1 X.2}
    (σ : M ⟶ N) (h : Epi ((etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
      (D.isEtale_chartHom B S hS hZ X hqc hqs)).map σ)) : Epi σ := by
  let g := D.chartHom B S hS hZ X hqc hqs
  have hg := D.isEtale_chartHom B S hS hZ X hqc hqs
  refine epi_of_forall_epi_modulePullback_map_of_isFlat B S hS (fun _ : Unit => g)
    (fun _ => isFlat_of_isEtale B S hS hg) ?_ σ fun _ => ?_
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨v, hv⟩ := D.isSurjective_φ x
    refine Set.mem_iUnion.2 ⟨(), v, ?_⟩
    change pointsMap B S hS _ (D.j ≫ D.π) v = x
    rw [D.comp_eq]
    exact hv
  · rw [← NatIso.naturality_2 (modulePullbackIsoEtaleModulePullback B S hS g hg)]
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom
      ((modulePullbackIsoEtaleModulePullback B S hS g hg).app _))) _
      (@epi_comp _ _ _ _ _ _ h _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv
        ((modulePullbackIsoEtaleModulePullback B S hS g hg).app _))))

/-- **The trace on the image of `⨁ π_*(λ_l)` is surjective over the chart**, once the cokernel of
`⨁ λ_l : ⨁ 𝒩_l ⟶ 𝒢'` is killed by `ℐ^m` and the trace through `θ : 𝒢' ⟶ π^!ℱ`, cut down by the
split section `ε` (which lies in `(π_*ℐ^m)|_V`), is surjective over `V`. -/
theorem epi_etaleModulePullback_map_biproduct_comp_trace
    (hfp : (pushforwardStructureModule B S hS
      (D.piHom B S hS hZ X hqc hqs)).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    {G' : Modules.{u, u} B S hS D.Y.1 D.Y.2} (hG'q : G'.IsQuasicoherentOnSite)
    (θ : G' ⟶ (affinePushforwardRightAdjoint B S hS (D.piHom B S hS hZ X hqc hqs)).obj F)
    {r : ℕ} (N : Fin r → Modules.{u, u} B S hS D.Y.1 D.Y.2) [HasBiproduct N]
    [HasBiproduct fun l => (modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).obj (N l)]
    (hN : ∀ l, (N l).IsQuasicoherentOnSite) (lam : ∀ l, N l ⟶ G') (m : ℕ)
    (hK : ∀ (W : (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).Cᵒᵖ)
      (c : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj.obj W),
      c ∈ (SheafOfModules.idealSheafPow D.I m).obj W →
        ∀ x : (cokernel (biproduct.desc lam)).val.obj W, c • x = 0)
    (ε : SheafOfModules.unit (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)) ⟶
      (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
        (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
        (directImageAlgebraUnitModule B S hS (D.piHom B S hS hZ X hqc hqs)))
    (εK : SheafOfModules.unit
        (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)) ⟶
      (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
        (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
        ((modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).obj
          (SheafOfModules.idealSheafPow D.I m).toSheafOfModules))
    (hfac : (εK ≫ (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
        (D.isEtale_chartHom B S hS hZ X hqc hqs)).map
        ((modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).map
          (SheafOfModules.idealSheafPow D.I m).ι) :
      SheafOfModules.unit (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)) ⟶
        (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
          (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
          (pushforwardStructureModule B S hS (D.piHom B S hS hZ X hqc hqs))) = ε)
    (hepi : Epi (etaleSectionAction B S hS (D.piHom B S hS hZ X hqc hqs)
          (D.chartHom B S hS hZ X hqc hqs) (D.isEtale_chartHom B S hS hZ X hqc hqs) ε
          ((moduleDirectImage B S hS (D.piHom B S hS hZ X hqc hqs)).obj G') ≫
        (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
          (D.isEtale_chartHom B S hS hZ X hqc hqs)).map
          ((directImageAlgebraRestrictScalars B S hS (D.piHom B S hS hZ X hqc hqs)).map
              ((moduleDirectImage B S hS (D.piHom B S hS hZ X hqc hqs)).map θ) ≫
            (directImageAlgebraRestrictScalars B S hS (D.piHom B S hS hZ X hqc hqs)).map
              (moduleDirectImage_affinePushforwardRightAdjointIso B S hS
                (D.piHom B S hS hZ X hqc hqs) D.isFinite_π.isAffineHom hfp F hFq).inv ≫
            (directImageAlgebraRestrictCoextendAdjunction B S hS
              (D.piHom B S hS hZ X hqc hqs)).counit.app F))) :
    Epi ((etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
          (D.isEtale_chartHom B S hS hZ X hqc hqs)).map
      ((biproduct.desc fun l => (modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).map
          (lam l) : _ ⟶ (directImageAlgebraRestrictScalars B S hS (D.piHom B S hS hZ X hqc hqs)).obj
            ((moduleDirectImage B S hS (D.piHom B S hS hZ X hqc hqs)).obj G')) ≫
        (directImageAlgebraRestrictScalars B S hS (D.piHom B S hS hZ X hqc hqs)).map
            ((moduleDirectImage B S hS (D.piHom B S hS hZ X hqc hqs)).map θ) ≫
          (directImageAlgebraRestrictScalars B S hS (D.piHom B S hS hZ X hqc hqs)).map
            (moduleDirectImage_affinePushforwardRightAdjointIso B S hS
              (D.piHom B S hS hZ X hqc hqs) D.isFinite_π.isAffineHom hfp F hFq).inv ≫
          (directImageAlgebraRestrictCoextendAdjunction B S hS
            (D.piHom B S hS hZ X hqc hqs)).counit.app F)) := by
  let π := D.piHom B S hS hZ X hqc hqs
  let g := D.chartHom B S hS hZ X hqc hqs
  have hg := D.isEtale_chartHom B S hS hZ X hqc hqs
  have hπA : IsAffineHom B S hS π.hom := D.isFinite_π.isAffineHom
  let Ψ := biproduct.desc lam
  let ψ₀ : (⨁ fun l => (modulePushforward B S hS π).obj (N l)) ⟶
      (modulePushforward B S hS π).obj G' :=
    biproduct.desc fun l => (modulePushforward B S hS π).map (lam l)
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS D.Y.1 D.Y.2
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS D.Y.1 D.Y.2
  have hA := isQuasicoherentOnSite_biproduct B S hS N hN
  have hQ : (cokernel Ψ).IsQuasicoherentOnSite := ObjectProperty.prop_cokernel _ _ hA hG'q
  have hKer : (kernel (cokernel.π Ψ)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_kernel _ _ hG'q hQ
  have hcokX : ∀ ⦃T : Modules.{u, u} B S hS X.1 X.2⦄
      (d : (modulePushforward B S hS π).obj G' ⟶ T),
      ψ₀ ≫ d = 0 → ∃ d₀ : (modulePushforward B S hS π).obj (cokernel Ψ) ⟶ T,
        d = (modulePushforward B S hS π).map (cokernel.π Ψ) ≫ d₀ := by
    intro T d hd
    have h1 : ∀ l, (modulePushforward B S hS π).map (lam l) ≫ d = 0 := fun l => by
      have h := congrArg (fun k => biproduct.ι _ l ≫ k) hd
      simpa only [ψ₀, biproduct.ι_desc_assoc, comp_zero] using h
    have h2 : (modulePushforward B S hS π).map Ψ ≫ d = 0 :=
      map_biproduct_desc_comp_eq_zero (modulePushforward B S hS π) lam d h1
    exact exists_factor_modulePushforward_map_cokernelπ B S hS π hπA Ψ hA hG'q hKer hQ d h2
  have hcok := exists_factor_etaleModulePullback_map B S hS g hg ψ₀ _ hcokX
  rw [Functor.map_comp]
  refine CategoryTheory.epi_comp_of_epi_comp_of_forall_comp_eq_zero _ _ _ hepi fun Z d hd => ?_
  obtain ⟨d'', rfl⟩ := hcok d hd
  exact etaleSectionAction_comp_eq_zero_of_factorsThrough B S hS π g hg (cokernel.π Ψ)
    (SheafOfModules.idealSheafPow D.I m) hK εK ε hfac d''

/-- In the situation of Stacks 0GUY, if `π_*ℐ` is a quotient of a finite locally free module, then
so is `π_*(ℐ^{a+1}𝒬)` for every epimorphism `𝒬 ⟶ ℐ^{n+1}` of quasi-coherent modules whose kernel
is killed by `ℐ^{a+1}`. -/
theorem exists_isFiniteLocallyFreeOnSite_epi_modulePushforward_idealPowModule
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (f : E ⟶ ResolutionPropertyDescentSituation.idealDirectImage B S hS hZ D) (hf : Epi f)
    (n a : ℕ)
    {Q : Modules.{u, u} B S hS D.Y.1 D.Y.2} (hQ : Q.IsQuasicoherentOnSite)
    (ρ : Q ⟶ idealSheafPowModule B S hS D.Y D.I (n + 1)) [Epi ρ]
    (hkill : ∀ (W : (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).Cᵒᵖ)
      (c : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj.obj W),
      c ∈ (SheafOfModules.idealSheafPow D.I (a + 1)).obj W →
        ∀ k : Q.val.obj W, (ρ.val.app W).hom k = 0 → c • k = 0) :
    ∃ (P : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite P)
      (p : P ⟶ (modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).obj
        (idealPowModule D.I (a + 1) Q)), Epi p := by
  let π := D.piHom B S hS hZ X hqc hqs
  have hrep := relativelyRepresentable_hom_of_isFinite B S hS π D.isFinite_π
  obtain ⟨P, hP, p, hp⟩ := @exists_isFiniteLocallyFreeOnSite_epi_bcPushforward_idealPowModule
    B S hS X D.Y π hrep D.I D.isFinite_π.isAffineHom D.isFiniteTypeQuasicoherent_I.1 E hE f hf n a
    Q hQ ρ ‹Epi ρ› hkill
  exact ⟨P, hP, p ≫ ((modulePushforwardChartIso B S hS π hrep).app _).inv,
    @epi_comp _ _ _ _ _ _ hp _ (@IsIso.epi_of_iso _ _ _ _ _
      (Iso.isIso_inv ((modulePushforwardChartIso B S hS π hrep).app _)))⟩

/-- **The resolution property from a finite locally free cover of `π_*ℐ`, without Noetherian
hypotheses.**  In the situation of Stacks 0GUY, if `π_*𝒪_Y` is of finite presentation and
`π_*ℐ` is a quotient of a finite locally free `𝒪_X`-module `ℰ`, then `X` has the resolution
property. Here `π_*𝒪_Y` is `pushforwardStructureModule B S hS D.πHom` and `π_*ℐ` is
`AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.idealDirectImage`. -/
theorem hasResolutionProperty_of_epi_idealDirectImage_of_isFinitePresentationOnSite
    (hfp : (pushforwardStructureModule B S hS D.πHom).IsFinitePresentationOnSite)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (f : E ⟶ D.idealDirectImage B S hS hZ) (hf : Epi f) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 := by
  refine (hasResolutionProperty_iff B S hS X.1 X.2).2 fun M hMft => ?_
  let π := D.piHom B S hS hZ X hqc hqs
  have hfp' : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite := hfp
  obtain ⟨ε, pr, hε, hεK⟩ :=
    exists_chart_split_section_factorsThrough_idealSheafPow B S hS hZ X hqc hqs D
  obtain ⟨M', hM'q, hM'ft, θ, hepi⟩ := exists_finiteType_modulePullback_epi_traceAction
    B S hS hZ X hqc hqs D hfp' M.obj M.property hMft ε pr hε
  have hG'q := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS π M' hM'q
  have hG'ft := isFiniteTypeOnSite_modulePullback B S hS π M' hM'ft
  obtain ⟨r, Q, hQ, n, a, ρ, hρ, hkill, q, hgen⟩ :=
    exists_idealPowModule_extensions_eq_zero_of_restrict B S hS hZ X hqc hqs D _ hG'q hG'ft
  let N : Fin r → Modules.{u, u} B S hS D.Y.1 D.Y.2 := fun l => idealPowModule D.I (a l + 1) (Q l)
  have hN : ∀ l, (N l).IsQuasicoherentOnSite := fun l =>
    isQuasicoherentOnSite_idealPowSubmodule B S hS _ _ D.I (Q l) (hQ l)
      D.isFiniteTypeQuasicoherent_I.1 (a l + 1)
  have hB : HasBiproduct N := HasBiproduct.of_hasProduct _
  have hB' : HasBiproduct fun l => (modulePushforward B S hS π).obj (N l) :=
    HasBiproduct.of_hasProduct _
  let lam : ∀ l, N l ⟶ (modulePullback B S hS π).obj M' := fun l =>
    idealPowModuleι D.I (a l + 1) (Q l) ≫ q l
  obtain ⟨m, hm⟩ := exists_smul_cokernel_eq_zero_of_restrict B S hS hZ X hqc hqs D N hN _ hG'q
    hG'ft lam hgen
  obtain ⟨εK, hfac⟩ := hεK m
  have hσ := epi_etaleModulePullback_map_biproduct_comp_trace B S hS hZ X hqc hqs D hfp' M.obj
    M.property hG'q θ N hN lam m hm ε εK hfac hepi
  exact exists_isFiniteLocallyFreeOnSite_epi_of_epi_biproduct B S hS X
    (fun l => (modulePushforward B S hS π).obj (N l))
    (fun l => by
      have := hρ l
      exact exists_isFiniteLocallyFreeOnSite_epi_modulePushforward_idealPowModule B S hS hZ X hqc
        hqs D E hE f hf (n l) (a l) (hQ l) (ρ l) (hkill l))
    _ (epi_of_epi_etaleModulePullback_chartHom_map B S hS hZ X hqc hqs D _ hσ)

end AlgebraicGeometry.Space

end
