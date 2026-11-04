module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.RingTheory.LocalProperties.StandardCover
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover

/-!
# Finiteness of a module and of its associated sheaf

On the spectrum of a commutative ring `R`, the quasi-coherent sheaf `M̃` attached to an
`R`-module `M` is of finite type exactly when `M` is a finite module, and of finite presentation
exactly when `M` is a finitely presented module.

## Main results

* `AlgebraicGeometry.tilde_isFiniteType_iff`: finite type of `M̃` is finiteness of `M`
  (Tag 01PB).
* `AlgebraicGeometry.tilde_isFinitePresentation_iff`: finite presentation of `M̃` is finite
  presentation of `M` (Tag 01PC).

## Implementation notes

Finite type and finite presentation of a sheaf of modules are `SheafOfModules.IsFiniteType` and
`SheafOfModules.IsFinitePresentation`, both of which are witnessed by *local* generating sections
or presentations over a covering.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If the restriction of `M̃` to an open `U` containing a standard open `D(f)` has finitely many
generating sections, then the localization `M_f` is a finite `R_f`-module. -/
private theorem module_finite_localization_of_localGenerators
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R)
    (U : (Spec R).Opens)
    (G : ((tilde M).over U).GeneratingSections) (hG : G.IsFiniteType)
    (hU : PrimeSpectrum.basicOpen f ≤ U) :
    Module.Finite (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M) := by
  classical
  let F := tilde M
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let i := (Spec R).homOfLE hU
  have : IsOpenImmersion i := AlgebraicGeometry.instIsOpenImmersionHomOfLE (Spec R) hU
  let j := U.ι
  let eU := U.sheafOfModulesEquivOver ((Spec R).ringCatSheaf)
  let hpresU := eU.toAdjunction.leftAdjoint_preservesColimits
  let etaU := TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U ((Spec R).ringCatSheaf)
  let GU := @SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _
    G eU.functor hpresU etaU
  let GU' := GU.equivOfIso ((Scheme.Modules.overFunctorEquiv U).app F)
  let hpresI := (Scheme.Modules.restrictAdjunction i).leftAdjoint_preservesColimits
  let GV := @SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _
    GU' (Scheme.Modules.restrictFunctor i) hpresI (Scheme.Modules.restrictUnitIso i).symm
  let e := AlgebraicGeometry.basicOpenIsoSpecAway f
  have : IsOpenImmersion e.inv := inferInstance
  let hpresE := (Scheme.Modules.restrictAdjunction e.inv).leftAdjoint_preservesColimits
  let GS := @SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _
    GV (Scheme.Modules.restrictFunctor e.inv) hpresE (Scheme.Modules.restrictUnitIso e.inv).symm
  let a : R ⟶ CommRingCat.of (Localization.Away f) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away f))
  let ψ := Spec.map a
  have hij : i ≫ j = V.ι := by
    dsimp [i, j, V]
    exact Scheme.homOfLE_ι (Spec R) hU
  have hi : e.inv ≫ i ≫ j = ψ := by
    have hm : e.hom ≫ ψ = V.ι := by simp [e, ψ, a, V]
    rw [hij, ← hm]
    simp [e]
  let ecomp : (Scheme.Modules.restrictFunctor ψ).obj F ≅
      (((Scheme.Modules.restrictFunctor e.inv).obj
        ((Scheme.Modules.restrictFunctor i).obj
          ((Scheme.Modules.restrictFunctor j).obj F)))) :=
    (Scheme.Modules.restrictFunctorCongr hi.symm).app F ≪≫
      (Scheme.Modules.restrictFunctorComp (e.inv ≫ i) j).app F ≪≫
      (Scheme.Modules.restrictFunctorComp e.inv i).app ((Scheme.Modules.restrictFunctor j).obj F)
  let GN := GS.equivOfIso ecomp.symm
  let N := (Scheme.Modules.restrictFunctor ψ).obj F
  have : N.IsQuasicoherent := inferInstance
  have hGN : Finite GN.I := hG.finite
  have hN := @Stacks.AlgebraicGeometry.CoherentTFAE.finite_moduleSpecΓ_of_generatingSections
    _ N ‹N.IsQuasicoherent› GN hGN
  let secIso : Γ(N, ⊤) ≅ Γ(F, PrimeSpectrum.basicOpen f) :=
    F.restrictAppIso ψ ⊤ ≪≫
      F.presheaf.mapIso (eqToIso (by simp [ψ, a]; rfl)).op
  let qS := (AlgebraicGeometry.modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let : Module R qS := Module.compHom qS (algebraMap R (Localization.Away f))
  let p := (AlgebraicGeometry.modulesSpecToSheaf.obj F).presheaf.obj
    (.op (PrimeSpectrum.basicOpen f))
  let secMap : qS →ₗ[R] p := {
    toFun := secIso.hom
    map_add' := by intro x y; exact secIso.hom.hom.map_add x y
    map_smul' := by
      intro r x
      have h1 : (F.restrictAppIso ψ ⊤).hom
          ((algebraMap R (Localization.Away f) r) • x) =
          r • (F.restrictAppIso ψ ⊤).hom x :=
        Scheme.Modules.restrictAppIso_smul_Spec (f := a) r x
      show F.presheaf.map (eqToHom (by simp [ψ, a]; rfl)).op
          ((F.restrictAppIso ψ ⊤).hom ((algebraMap R (Localization.Away f) r) • x)) =
        r • F.presheaf.map (eqToHom (by simp [ψ, a]; rfl)).op
          ((F.restrictAppIso ψ ⊤).hom x)
      rw [h1]
      exact Scheme.Modules.map_smul_Spec
        (hUV := (eqToHom (by simp [ψ, a]; rfl)).op) r
        ((F.restrictAppIso ψ ⊤).hom x) }
  let secLin : qS ≃ₗ[R] p := LinearEquiv.ofBijective secMap
    (ConcreteCategory.bijective_of_isIso secIso.hom)
  let eLoc : LocalizedModule (Submonoid.powers f) M ≃ₗ[
        Localization.Away f] qS := by
    let φ := secLin.symm.toLinearMap.comp
      (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
    have : IsLocalizedModule (Submonoid.powers f) φ :=
      IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
        (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom secLin.symm
    let : IsScalarTower (↑R) (Localization.Away f) qS :=
      IsScalarTower.of_compHom (↑R) (Localization.Away f) qS
    exact LinearEquiv.extendScalarsOfIsLocalization
      (S := Submonoid.powers f) (A := Localization.Away f)
      (IsLocalizedModule.iso (Submonoid.powers f) φ)
  let : Module.Finite (Localization.Away f) qS := hN
  exact Module.Finite.of_surjective eLoc.symm.toLinearMap eLoc.symm.surjective

/-- An associated sheaf on `Spec R` is of finite type precisely when its module of global
sections is finite over `R`. -/
@[stacks 01PB, ega "II 1.4.5" "affine base, B = O_Y"]
theorem tilde_isFiniteType_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsFiniteType ↔ Module.Finite R M := by
  constructor
  · intro h
    classical
    obtain ⟨q, hq⟩ := h.exists_localGeneratorsData
    let : q.IsFiniteType := hq
    have hcoverPS : (⨆ i, q.X i) =
        (⊤ : TopologicalSpace.Opens (PrimeSpectrum (↑R))) := by
      show (⨆ i, q.X i) = (⊤ : (Spec R).Opens)
      exact (Opens.coversTop_iff (Spec R) q.X).mp q.coversTop
    obtain ⟨n, g, a, hgcover, hgle⟩ :=
        PrimeSpectrum.exists_finite_basicOpen_refinement
        (R := (↑R)) (f := (1 : ↑R)) q.X (by
          rw [PrimeSpectrum.basicOpen_one, ← hcoverPS]
          exact le_rfl)
    have hgspan : Ideal.span (Set.range g) = ⊤ := by
      apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
      simpa using hgcover.symm
    apply Module.Finite.of_localizationSpan_range (R := (↑R)) (M := (↑M)) (ι := Fin n) g hgspan
    intro j
    exact module_finite_localization_of_localGenerators M (g j) (q.X (a j))
      (q.generators (a j)) (hq.isFiniteType (a j)) (hgle j)
  · intro hM
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
    let S : Set M := Set.range s
    have hS : Submodule.span R S = ⊤ := hs
    let L : (S →₀ R) →ₗ[R] M := Finsupp.linearCombination R fun x : S => x.1
    let P : (tilde M).Presentation :=
      presentationTilde M S hS (LinearMap.ker L) (Submodule.span_eq _)
    let G := P.generators
    have hG : Finite G.I := (Set.finite_range s).to_subtype
    let : G.IsFiniteType := ⟨hG⟩
    let Q : (tilde M).LocalGeneratorsData.{u} := G.localGeneratorsData
    show SheafOfModules.IsFiniteType (M := tilde M)
    refine SheafOfModules.IsFiniteType.mk (M := tilde M) ⟨Q, ?_⟩
    constructor
    intro i
    exact ⟨by change Finite G.I; exact hG⟩


/-- A finite presentation of `M̃` makes `M̃` a sheaf of finite presentation. -/
private lemma finitePresentation_of_presentation {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (p : (tilde M).Presentation) [p.IsFinite] :
    (tilde M).IsFinitePresentation := by
  refine SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨p.quasicoherentData, ?_⟩
  constructor
  intro i
  exact ⟨⟨by
      show Finite p.generators.I
      exact (inferInstance : p.IsFinite).isFiniteType_generators.finite⟩,
    ⟨by
      show Finite p.relations.I
      exact (inferInstance : p.IsFinite).isFiniteType_relations.finite⟩⟩

/-- The quasi-coherent sheaf on `Spec R` associated to an `R`-module `M` is of finite
presentation if and only if `M` is a finitely presented module. -/
@[stacks 01PC]
theorem tilde_isFinitePresentation_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsFinitePresentation ↔ Module.FinitePresentation R M := by
  constructor
  · intro h
    have hft : SheafOfModules.IsFiniteType.{u, u, u} (tilde M) := by
      obtain ⟨q, hq⟩ := h.exists_quasicoherentData
      let : q.IsFinitePresentation.{u, u, u, u} := hq
      have hdata : q.localGeneratorsData.IsFiniteType.{u, u, u, u} := by
        constructor
        intro i
        show (q.presentation i).generators.IsFiniteType
        exact (hq.isFinite_presentation i).isFiniteType_generators
      exact SheafOfModules.IsFiniteType.mk.{u, u, u}
        (show ∃ σ : SheafOfModules.LocalGeneratorsData.{u, u, u, u} (tilde M),
          σ.IsFiniteType from ⟨q.localGeneratorsData, hdata⟩)
    have hM : Module.Finite R M :=
      (tilde_isFiniteType_iff M).mp hft
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
    let f : (Fin n →₀ R) →ₗ[R] M := Finsupp.linearCombination R g
    have hf : Function.Surjective f := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hg]
    have : SheafOfModules.IsFinitePresentation.{u, u, u} (tilde M) := h
    have : SheafOfModules.IsFinitePresentation.{u, u, u}
        ((tilde.functor R).obj M) := by simpa using h
    have hsource : SheafOfModules.IsFiniteType.{u, u, u}
        (tilde (ModuleCat.of R (Fin n →₀ R))) :=
      (tilde_isFiniteType_iff (ModuleCat.of R (Fin n →₀ R))).2 inferInstance
    have : SheafOfModules.IsFiniteType.{u, u, u}
        ((tilde.functor R).obj (ModuleCat.of R (Fin n →₀ R))) := by simpa using hsource
    have : Functor.PreservesEpimorphisms (tilde.functor R) :=
      Functor.preservesEpimorphisms_of_adjunction (tilde.adjunction (R := R))
    have : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
    let fc := ModuleCat.ofHom f
    let φ := (tilde.functor R).map fc
    have hφ : Epi φ := Functor.map_epi (tilde.functor R) fc
    have hker : SheafOfModules.IsFiniteType.{u, u, u} (kernel φ) :=
      @Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› φ hφ
    let : (kernel φ).IsFiniteType := hker
    have htildeKer : (tilde (ModuleCat.of R (LinearMap.ker f))).IsFiniteType := by
      let e : tilde (ModuleCat.of R (LinearMap.ker f)) ≅ kernel φ :=
        ((tilde.functor R).mapIso (ModuleCat.kernelIsoKer fc)).symm ≪≫
          PreservesKernel.iso (tilde.functor R) fc
      rcases hker.exists_localGeneratorsData with ⟨σ, hσ⟩
      let : σ.IsFiniteType.{u, u, u, u} := hσ
      let data : SheafOfModules.LocalGeneratorsData.{u, u, u, u}
          (tilde (ModuleCat.of R (LinearMap.ker f))) := {
        I := σ.I
        X := σ.X
        coversTop := σ.coversTop
        generators i := by
          let F := SheafOfModules.overFunctor (Spec R).ringCatSheaf (σ.X i)
          exact (σ.generators i).equivOfIso (F.mapIso e.symm)
      }
      have hdata : data.IsFiniteType.{u, u, u, u} := by
        constructor
        intro i
        show ((σ.generators i).equivOfIso
          ((SheafOfModules.overFunctor (Spec R).ringCatSheaf (σ.X i)).mapIso e.symm)).IsFiniteType
        exact ⟨(hσ.isFiniteType i).finite⟩
      exact SheafOfModules.IsFiniteType.mk.{u, u, u}
        (show ∃ σ : SheafOfModules.LocalGeneratorsData.{u, u, u, u}
          (tilde (ModuleCat.of R (LinearMap.ker f))), σ.IsFiniteType from ⟨data, hdata⟩)
    have hK : Module.Finite R (LinearMap.ker f) :=
      (tilde_isFiniteType_iff
        (ModuleCat.of R (LinearMap.ker f))).mp htildeKer
    exact Module.finitePresentation_of_free_of_surjective f hf
      ((Module.Finite.iff_fg).mp hK)
  · intro h
    classical
    obtain ⟨s, hs, hsK⟩ := (inferInstance : Module.FinitePresentation R M).out
    rcases Submodule.fg_def.mp hsK with ⟨t, htfinite, htK⟩
    let p := AlgebraicGeometry.presentationTilde (R := R) (M := M)
      (s : Set M) hs (t : Set (s →₀ R)) htK
    have : Finite {x // x ∈ (s : Set M)} := Set.finite_coe_iff.mpr s.finite_toSet
    have : Finite {x // x ∈ t} := Set.finite_coe_iff.mpr htfinite
    have hp : p.IsFinite.{u, u, u} :=
      ⟨⟨by change Finite {x // x ∈ (s : Set M)}; infer_instance⟩,
       ⟨by change Finite {x // x ∈ t}; infer_instance⟩⟩
    let : p.IsFinite.{u, u, u} := hp
    exact finitePresentation_of_presentation M p

/-- The global sections of a finitely presented quasi-coherent module on an affine scheme form
a finitely presented module. -/
public theorem finitePresentation_sections_of_affine
    {R : CommRingCat.{u}} (F : (Spec R).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] :
    Module.FinitePresentation R ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)) :=
  (AlgebraicGeometry.tilde_isFinitePresentation_iff _).mp
    ((SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
      (asIso F.fromTildeΓ).symm inferInstance)

/-- The associated sheaf of a finitely presented module admits a finite global presentation. -/
public theorem tilde_has_finite_presentation
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    ∃ P : (tilde M).Presentation, P.IsFinite := by
  obtain ⟨s, hs, hker⟩ := Module.FinitePresentation.out (R := R) (M := M)
  obtain ⟨t, ht⟩ := hker
  let P := presentationTilde M (s : Set M) hs (t : Set (s →₀ R)) ht
  exact ⟨P, ⟨⟨by change Finite s; infer_instance⟩, ⟨by change Finite t; infer_instance⟩⟩⟩

end AlgebraicGeometry
