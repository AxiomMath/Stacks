module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SectionsLiftFibreIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleVanishingAboveTheDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FormalFunctionsFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFiniteAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent

/-!
# First cohomology on the fibre, and sections over the fibre

Let `q : W ⟶ X` present the fibre of `f : X ⟶ V` over a closed subscheme `p : T ⟶ V` of an
affine scheme, with ideal `𝔪 ⊆ Γ(V, 𝒪_V)`, and suppose the scheme `W` has a Noetherian underlying
space of dimension at most one.

## Main results

* `AlgebraicGeometry.C1590Private.isZero_rightDerived_schemeSpace_of_topologicalKrullDim_le_one`:
  the cohomology of a quasi-coherent module on `W` vanishes above degree one.
* `AlgebraicGeometry.C1590Private.isZero_cohomology_one_of_isFiniteQuotient`: `H¹(W, −)` kills
  every quasi-coherent quotient of a finite sum of copies of a quasi-coherent module it kills.
* `AlgebraicGeometry.C1590Private.isIso_unit_of_isKilledBy`: a module killed by `𝔪` is a direct
  image from the fibre.
* `AlgebraicGeometry.C1590Private.isZero_cohomology_one_of_isKilledBy_fibreIdeal`: `H¹(X, G) = 0`
  for a quasi-coherent quotient `G` of a finite sum of copies of `F` killed by `𝔪`, when
  `H¹(W, q^* F) = 0`.
* `AlgebraicGeometry.C1590Private.surjective_globalSectionsPullbackMap_of_isZero_fibre`: for a
  proper `f` over an affine Noetherian base and a coherent `F` with `H¹(W, q^* F) = 0`, every
  section of `q^* F` over `W` is the restriction of a global section of `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Space.hasInjectiveResolutions_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A module is zero if its underlying abelian group is. -/
private theorem isZero_of_isZero_forget₂ {R : Type*} [Ring R] (M : ModuleCat.{u + 1} R)
    (h : IsZero ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj M)) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 h

/-- **Cohomology on a scheme of dimension at most one vanishes above degree one.**  For a scheme
`W` of the site whose underlying space is Noetherian of dimension at most one and a
quasi-coherent module `K` on the small étale site of `W`, `Hⁿ(W, K) = 0` for `n ≥ 2`. -/
theorem isZero_rightDerived_schemeSpace_of_topologicalKrullDim_le_one (W : BigFppfOver B S hS)
    [NoetherianSpace ((BigFppfOver.toScheme B S hS).obj W)]
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj W) ≤ 1)
    (K : Space.Modules.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2)
    (hK : K.IsQuasicoherentOnSite) (n : ℕ) (hn : 1 < n) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS (schemeSpace W).1
        (schemeSpace W).2).O)).rightDerived n).obj K) := by
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS
    (schemeSpace W).1 (schemeSpace W).2).O
  let A := Space.idEtaleChart B S hS W
  let X : (Space.SmallEtale B S hS (schemeSpace W).1)ᵒᵖ := op A
  have : NoetherianSpace (Space.chartScheme A) :=
    inferInstanceAs (NoetherianSpace ((BigFppfOver.toScheme B S hS).obj W))
  have := Space.isContinuous_chartComparisonFunctor B S hS (schemeSpace W) A
  have hdim' : topologicalKrullDim (Space.chartScheme A) ≤ ((1 : ℕ) : WithBot ℕ∞) := hdim
  have hZar :=
    Stacks.CohomologyVanishing.isZero_rightDerived_moduleGlobalSections_of_noetherianSpace_of_dim_le
      (Space.chartScheme A) hdim' hn
    ((SheafOfModules.pushforward.{u} (Space.chartComparisonRingMap B S hS (schemeSpace W) A)).obj K)
  have hHg := (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    (Space.chartScheme A).ringCatSheaf ⊤ n _).1 hZar
  have : (SheafOfModules.evaluation O X).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have h0 : IsZero (((SheafOfModules.evaluation O X).rightDerived n).obj K) :=
    Space.isZero_rightDerived_evaluation_of_isZero_hgroup B S hS (schemeSpace W) A K hK n
      (by omega) hHg
  have h1 : IsZero ((forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}).obj
      (((globalSectionsFunctor.{u + 1, u, u, u} O).rightDerived n).obj K)) :=
    IsZero.of_iso (Functor.map_isZero (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) h0)
      (((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u} O)
          (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}) n).app K).symm
              ≪≫
        (ModuleSheafCohomology.rightDerivedIso
          (globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O X
            (Space.isTerminalIdEtaleChart B S hS W).op) n).app K ≪≫
          (Functor.rightDerivedCompIso (SheafOfModules.evaluation O X)
            (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}) n).app K)
  exact isZero_of_isZero_forget₂ _ h1

/-- An additive functor kills a finite direct sum of copies of an object it kills. -/
theorem isZero_obj_sigma_of_isZero {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] (Φ : C ⥤ D) [Φ.Additive] (ι : Type) [Finite ι] (N : C) (h : IsZero (Φ.obj N)) :
    IsZero (Φ.obj (∐ fun _ : ι => N)) := by
  have := Abelian.hasFiniteBiproducts (C := C)
  have := Abelian.hasFiniteBiproducts (C := D)
  have hz : IsZero (⨁ fun _ : ι => Φ.obj N) := by
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun j => h.eq_of_tgt _ _
  exact hz.of_iso (Φ.mapIso (biproduct.isoCoproduct fun _ : ι => N).symm ≪≫
    Φ.mapBiproduct fun _ : ι => N)

/-- **`H¹` on a scheme of dimension at most one kills quotients.**  If `H¹(W, N₀) = 0`, then
`H¹(W, G) = 0` for every quasi-coherent quotient `G` of a finite sum of copies of the
quasi-coherent `N₀`. -/
theorem isZero_cohomology_one_of_isFiniteQuotient (W : BigFppfOver B S hS)
    [NoetherianSpace ((BigFppfOver.toScheme B S hS).obj W)]
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj W) ≤ 1)
    (N₀ G : Space.Modules.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2)
    (hN₀ : N₀.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite)
    (h₀ : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS (schemeSpace W).1
        (schemeSpace W).2).O)).rightDerived 1).obj N₀))
    (hq : IsFiniteQuotient N₀ G) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS (schemeSpace W).1
        (schemeSpace W).2).O)).rightDerived 1).obj G) := by
  obtain ⟨ι, hι, π, hπ⟩ := hq
  have := Space.enoughInjectives_modules B S hS (schemeSpace W).1 (schemeSpace W).2
  have : (∐ fun _ : ι => N₀).IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_of_isColimit_cofan B S hS _ _ _
      (coproductIsCoproduct fun _ : ι => N₀) fun _ => hN₀
  have hK : (kernel π).IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_kernel_of_quasicoherent B S hS _ _ π
  let T := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)
      mono_f := inferInstanceAs (Mono (kernel.ι π))
      epi_g := hπ }
  exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hT _ 1
    (isZero_obj_sigma_of_isZero _ ι N₀ h₀)
    (isZero_rightDerived_schemeSpace_of_topologicalKrullDim_le_one W hdim _ hK 2 (by omega))

section Fibre

variable (Vb : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj Vb)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace Vb)
  {T W : BigFppfOver B S hS} (p : T ⟶ Vb) (v : W ⟶ T) (q : yoneda.obj W ⟶ X.1)
  (hpb : IsPullback q (yoneda.map v) f.hom (yoneda.map p))

include hpb in
/-- **A module killed by the ideal of the point is a direct image from the fibre**: the unit
`G ⟶ q_* q^* G` is an isomorphism. -/
theorem isIso_unit_of_isKilledBy
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    (G : Space.Modules.{u, u} B S hS X.1 X.2)
    (hG : IsKilledBy (Space.pullbackRingHom B Vb f) (fibreIdeal Vb p) G) :
    IsIso ((Space.modulePullbackAdjunction B S hS (fibrePresentationMap q)).unit.app G) :=
  have hq := isClosedImmersion_fibre Vb f p v q hpb hp
  (Space.essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS
    (fibrePresentationMap q) hq G).1
      ((Space.essImage_modulePushforward_iff B S hS (fibrePresentationMap q) hq G).2
        (annihilatedByKerIdeal_of_isKilledBy Vb f p v q hpb hp G hG))

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through module sheaves on the small étale ringed site of a space is heavy
include hpb in
/-- **`H¹` of a module killed by the ideal of the point.**  Let `F` be quasi-coherent with
`H¹(W, q^* F) = 0`, the fibre `W` having Noetherian underlying space of dimension at most one.
Then `H¹(X, G) = 0` for every quasi-coherent quotient `G` of a finite sum of copies of `F` killed
by the ideal of the point. -/
theorem isZero_cohomology_one_of_isKilledBy_fibreIdeal
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    [NoetherianSpace ((BigFppfOver.toScheme B S hS).obj W)]
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj W) ≤ 1)
    (F : Space.Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hF₁ : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS (schemeSpace W).1
        (schemeSpace W).2).O)).rightDerived 1).obj
          ((Space.modulePullback B S hS (fibrePresentationMap q)).obj F)))
    (G : Space.Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    (hGq : IsFiniteQuotient F G)
    (hGk : IsKilledBy (Space.pullbackRingHom B Vb f) (fibreIdeal Vb p) G) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1
        X.2).O)).rightDerived 1).obj G) := by
  have hq := isClosedImmersion_fibre Vb f p v q hpb hp
  let adj := Space.modulePullbackAdjunction B S hS (fibrePresentationMap q)
  have := isIso_unit_of_isKilledBy Vb f p v q hpb hp G hGk
  have := adj.isLeftAdjoint
  have := adj.leftAdjoint_preservesColimits.{0, 0}
  let L := Space.modulePullback B S hS (fibrePresentationMap q)
  have hqc := fun M => Space.isQuasicoherentOnSite_modulePullback_of_isClosedImmersion B S hS
    (fibrePresentationMap q) hq M
  have hNqc := hqc G hG
  have hNq : IsFiniteQuotient (L.obj F) (L.obj G) := by
    obtain ⟨ι, hι, π, hπ⟩ := hGq
    exact ⟨ι, hι, (PreservesCoproduct.iso L _).inv ≫ L.map π, epi_comp _ _⟩
  have hN := isZero_cohomology_one_of_isFiniteQuotient W hdim _ _ (hqc F hF) hNqc hF₁ hNq
  have e := Space.cohomologyIsoOfIsAffineHom B S hS (fibrePresentationMap q)
    (Space.isAffineHom_of_isClosedImmersion B S hS _ hq) (L.obj G) hNqc 1
  have h1 := (Functor.map_isZero (forget₂ _ AddCommGrpCat.{u + 1}) hN).of_iso e.symm
  exact IsZero.of_iso (isZero_of_isZero_forget₂ _ h1) (Functor.mapIso _ (asIso (adj.unit.app G)))

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through module sheaves on the small étale ringed site of a space is heavy
include hpb in
/-- **Sections over the fibre are sections of `F / 𝔪 F`.**  If `H⁰(X, F) ⟶ H⁰(X, F / 𝔪 F)` is
onto, so is restriction of global sections `Γ(X, F) ⟶ Γ(W, q^* F)`. -/
theorem surjective_globalSectionsPullbackMap_of_epi
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    (F : Space.Modules.{u, u} B S hS X.1 X.2)
    (hepi : Epi (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1
        X.2).O)).rightDerived 0).map
          (Space.idealQuotientπ (Space.pullbackRingHom B Vb f) F (fibreIdeal Vb p ^ 1)))) :
    Function.Surjective
      (Space.globalSectionsPullbackMap B S hS (fibrePresentationMap q) F).hom := by
  let φ := Space.pullbackRingHom B Vb f
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O
  let Γ := globalSectionsFunctor.{u + 1, u, u, u} O
  let m := fibreIdeal Vb p
  let πm := Space.idealQuotientπ φ F (m ^ 1)
  let adj := Space.modulePullbackAdjunction B S hS (fibrePresentationMap q)
  let L := Space.modulePullback B S hS (fibrePresentationMap q)
  let R := Space.modulePushforward B S hS (fibrePresentationMap q)
  have := adj.leftAdjoint_preservesColimits
  have hQk : IsKilledBy φ m (Space.idealQuotient φ F (m ^ 1)) := fun a ha =>
    Space.globalSmul_idealQuotient_eq_zero φ F (m ^ 1) (by rwa [pow_one])
  have hQiso := isIso_unit_of_isKilledBy Vb f p v q hpb hp _ hQk
  have hι : Space.idealMultipleι φ F (m ^ 1) ≫ adj.unit.app F = 0 := by
    refine Space.idealMultiple_hom_ext φ F (m ^ 1) fun a ha => ?_
    rw [comp_zero, ← Category.assoc, Space.idealMultipleFactor_ι, ← comp_globalSmul]
    rw [pow_one] at ha
    change adj.unit.app F ≫ globalSmul O (φ a) (R.obj (L.obj F)) = 0
    rw [isKilledBy_modulePushforward_fibre Vb f p v q hpb (L.obj F) a ha, comp_zero]
  have hLι : L.map (Space.idealMultipleι φ F (m ^ 1)) = 0 := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
    exact (adj.unit.naturality (Space.idealMultipleι φ F (m ^ 1))).symm.trans hι
  have : IsIso (L.map πm) := by
    have := cokernel.π_of_zero hLι
    have : IsIso (L.map πm ≫ (PreservesCokernel.iso L (Space.idealMultipleι φ F (m ^ 1))).hom) := by
      rw [PreservesCokernel.π_iso_hom]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso L _).hom
  have hnat : πm ≫ adj.unit.app (Space.idealQuotient φ F (m ^ 1)) =
      adj.unit.app F ≫ R.map (L.map πm) := adj.unit.naturality πm
  have hη : adj.unit.app F = πm ≫ adj.unit.app (Space.idealQuotient φ F (m ^ 1)) ≫
      inv (R.map (L.map πm)) := by
    rw [← Category.assoc, hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  let iso0 := Space.rightDerivedZeroIsoGlobalSections X
  have hΓπ : Epi (Γ.map πm) := by
    have h := iso0.hom.naturality πm
    have e : Γ.map πm = iso0.inv.app F ≫ (Γ.rightDerived 0).map πm ≫
        iso0.hom.app (Space.idealQuotient φ F (m ^ 1)) := by
      rw [h, Iso.inv_hom_id_app_assoc]
    rw [e]
    exact epi_comp _ _
  have hΓη : Epi (Γ.map (adj.unit.app F)) := by
    rw [hη, Functor.map_comp]
    exact epi_comp _ _
  have hfinal : Epi (Space.globalSectionsPullbackMap B S hS (fibrePresentationMap q) F) := by
    rw [← Space.globalSectionsPullbackMap_eq]
    exact epi_comp _ _
  exact (ModuleCat.epi_iff_surjective _).1 hfinal

include hpb in
/-- **Sections lift from a fibre with vanishing `H¹`, over an affine Noetherian base.**  Let
`f : X ⟶ V` be a proper morphism from a locally Noetherian algebraic space to an affine locally
Noetherian scheme of the site, `F` a coherent `𝒪_X`-module, and `q : W ⟶ X` a presentation of
the fibre over a closed subscheme `p : T ⟶ V` whose underlying space is Noetherian of dimension at
most one.  If `H¹(W, q^* F) = 0`, every section of `q^* F` over `W` is the restriction of a global
section of `F`. -/
theorem surjective_globalSectionsPullbackMap_of_isZero_fibre
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Vb)]
    (hf : Space.IsProper B S hS f.hom)
    [Fact (Space.HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    [NoetherianSpace ((BigFppfOver.toScheme B S hS).obj W)]
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj W) ≤ 1)
    (F : Space.Modules.{u, u} B S hS X.1 X.2) [hF : Space.IsCoherent B S hS X.1 X.2 F]
    (hF₁ : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS (schemeSpace W).1
        (schemeSpace W).2).O)).rightDerived 1).obj
          ((Space.modulePullback B S hS (fibrePresentationMap q)).obj F))) :
    Function.Surjective
      (Space.globalSectionsPullbackMap B S hS (fibrePresentationMap q) F).hom := by
  let φ := Space.pullbackRingHom B Vb f
  let m := fibreIdeal Vb p
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Vb, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hFqc : F.IsQuasicoherentOnSite := hF.toIsQuasicoherentOnSite
  have hm : m.FG := IsNoetherian.noetherian m
  have : Space.IsCoherent B S hS X.1 X.2 (Space.idealMultiple φ F (m ^ 1)) :=
    Space.isCoherent_idealMultiple φ F (m ^ 1) hF
  have hfin : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj Vb, ⊤)
      (Space.cohomologyRes φ 1 (Space.idealMultiple φ F (m ^ 1))) :=
    Space.moduleFinite_cohomology_of_isProper_of_isAffine B Vb f hf _ 1
  have hRees := Space.isReesFinite_cohomologyIdealPowerSystem_of_isAffine (RingEquiv.refl _) f hf φ
    (fun _ => rfl) F m 1
  obtain ⟨c, -, hc⟩ :=
    Space.exists_surjective_cohomologyIdealPowerMul_and_range_le_of_isReesFinite φ F m 1 hRees
  have hvan := isZero_cohomology_one_of_isKilledBy_pow (φ := φ) F m hm fun G hG hGq hGk =>
    isZero_cohomology_one_of_isKilledBy_fibreIdeal Vb f p v q hpb hp hdim F hFqc hF₁ G hG hGq hGk
  exact surjective_globalSectionsPullbackMap_of_epi Vb f p v q hpb hp F
    (epi_rightDerived_zero_map_idealQuotientπ F hFqc m hm hfin c (hc 1 (c + 1) (by omega)) hvan)

end Fibre

end AlgebraicGeometry.C1590Private

end
