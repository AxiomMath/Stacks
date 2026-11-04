module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AdicQuotientSystem

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Completion along `I 𝒪_X` on coherent modules with proper support

Let `A` be a Noetherian ring, complete with respect to an ideal `I`, and let `X` be an algebraic
space locally of finite type over `Spec A`. As a consequence of Stacks 08B9, on coherent modules
whose support is proper over `Spec A`, completion along `I 𝒪_X` is injective and surjective on
morphisms, reflects isomorphisms, and detects the vanishing of a map. Annihilation of a kernel or
cokernel by a power of a quasi-coherent ideal can likewise be checked on the reductions modulo all
powers of `I 𝒪_X`.

## Main definitions

* `C1573.baseCompletion`: Completion along `I 𝒪_X` on coherent modules.
* `C1573.HasProperSupportOverBase`: A coherent module has proper support over `Spec A`.

## Main results

* `C1573.bijective_baseCompletion_map`: Completion is bijective on maps out of a module with
  proper support.
* `C1573.isIso_of_isIso_baseCompletion_map`: Completion reflects isomorphisms between modules
  with proper support.
* `C1573.eq_zero_of_comp_projection_eq_zero`: A map out of a module with proper support vanishes
  once all its reductions modulo powers of `I 𝒪_X` vanish.
* `C1573.isPowAnnihilated_kernel_of_reductions`,
  `C1573.isPowAnnihilated_cokernel_of_reductions`: Annihilation of a kernel or cokernel by `𝓚^s`
  is detected on the reductions modulo all powers of `I 𝒪_X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]

/-- Completion along `I 𝒪_X`. -/
abbrev C1573.baseCompletion :
    CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 ⥤
      CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) :=
  completionFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
    (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)

variable [IsNoetherianRing A] [IsAdicComplete I A] (f : X ⟶ schemeSpace (baseObject A B hA))
  (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)

/-- A coherent module has proper support over `Spec A`. -/
abbrev C1573.HasProperSupportOverBase (M : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    Prop :=
  HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
    ((SheafOfModules.toSheaf _).obj M.obj)

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] [IsNoetherianRing A] in
/-- The support of a coherent module is closed. -/
theorem C1573.isClosed_supportOfSheaf_coherent
    (M : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    IsClosed (supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj M.obj)) :=
  have := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X M.obj
  isClosed_supportOfSheaf_of_isFiniteTypeOnSite B (Spec (.of A)) hA X.1 X.2 M.obj

/-- **Completion is bijective on maps out of a module with proper support.** -/
theorem C1573.bijective_baseCompletion_map
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hM : HasProperSupportOverBase X f hf M) :
    Function.Bijective ((baseCompletion X I).map (X := M) (Y := N)) := by
  obtain ⟨hMcl, hMp⟩ := hM
  have hcl := hMcl.inter (isClosed_supportOfSheaf_coherent X N)
  exact bijective_completionFunctor_map_of_isProperOver X I f hf M N hcl
    (isProperOver_of_subset B (Spec (.of A)) hA X.2 _ f.hom hf _ _ hcl hMcl
      Set.inter_subset_left hMp)

/-- **Completion reflects isomorphisms between modules with proper support.** -/
theorem C1573.isIso_of_isIso_baseCompletion_map
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hM : HasProperSupportOverBase X f hf M) (hN : HasProperSupportOverBase X f hf N)
    (φ : M ⟶ N) [IsIso ((baseCompletion X I).map φ)] : IsIso φ := by
  obtain ⟨ψ, hψ⟩ := (bijective_baseCompletion_map X I f hf (N := M) hN).2
    (inv ((baseCompletion X I).map φ))
  refine ⟨ψ, (bijective_baseCompletion_map X I f hf (N := M) hM).1 ?_,
    (bijective_baseCompletion_map X I f hf (N := N) hN).1 ?_⟩
  · rw [Functor.map_comp, hψ, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, hψ, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **A map out of a module with proper support vanishes once its reductions modulo all powers of
`I 𝒪_X` vanish.** -/
theorem C1573.eq_zero_of_comp_projection_eq_zero
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hM : HasProperSupportOverBase X f hf M) (φ : M ⟶ N)
    (h : ∀ n : ℕ, φ.hom ≫ smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) N.obj = 0) : φ = 0 := by
  refine (bijective_baseCompletion_map X I f hf hM).1 ?_
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  obtain ⟨n⟩ := n
  refine (cancel_epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
    (baseIdealSubmodule X.1 X.2 I) (n + 1) M.obj)).1 ?_
  show smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 _ (n + 1) M.obj ≫
      idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 _ (n + 1) φ.hom =
    smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 _ (n + 1) M.obj ≫
      idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 _ (n + 1) (0 : M ⟶ N).hom
  rw [← smallEtaleAdicQuotientMapOfHom_eq, ← smallEtaleAdicQuotientMapOfHom_eq]
  refine (smallEtaleAdicQuotientProjection_mapOfHom B (Spec (.of A)) hA X.1 X.2 _ (n + 1)
    φ.hom).trans ?_
  refine (h n).trans ?_
  refine Eq.trans ?_ (smallEtaleAdicQuotientProjection_mapOfHom B (Spec (.of A)) hA X.1 X.2 _
    (n + 1) (0 : M ⟶ N).hom).symm
  exact zero_comp.symm

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] [IsNoetherianRing A] in
/-- If the inclusion of `𝓚^s M` vanishes, `𝓚^s` annihilates `M`. -/
theorem C1573.isPowAnnihilated_of_ι_eq_zero (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule) (s : ℕ) (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (h : (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K s M).ι = 0) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K s M := by
  intro U r hr x
  have hmem : r • x ∈ (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K s M).obj (op U) :=
    le_idealPowerSubsheaf_obj B (Spec (.of A)) hA X.1 X.2 K s M U
      (Submodule.smul_mem_smul hr Submodule.mem_top)
  exact congrArg (fun k => k.val.app (op U) ⟨r • x, hmem⟩) h

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] [IsNoetherianRing A] in
/-- The inclusion of the kernel of `g` is injective on sections over every object `U` of the
small étale site. -/
theorem C1573.injective_kernel_ι_app_baseCompletion
    {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N)
    (U : SmallEtale B (Spec (.of A)) hA X.1) :
    Function.Injective ((kernel.ι g).val.app (op U)) :=
  (ModuleCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono ((SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
      (op (U : (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).C))).map (kernel.ι g))))

variable (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule)
  (hK : K.toSheafOfModules.IsQuasicoherentOnSite)

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] [IsNoetherianRing A] in
/-- If `φ : M ⟶ N` is injective on sections over every object of the small étale site and `N`
has proper support over `Spec A`, then so does `M`. -/
theorem C1573.hasProperSupportOverBase_of_injective
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2} (φ : M.obj ⟶ N.obj)
    (hφ : ∀ U : SmallEtale B (Spec (.of A)) hA X.1, Function.Injective (φ.val.app (op U)))
    (hN : HasProperSupportOverBase X f hf N) : HasProperSupportOverBase X f hf M :=
  hasProperSupport_of_subset B (Spec (.of A)) hA X.2 _ f.hom hf
    (isClosed_supportOfSheaf_coherent X M)
    (supportOfSheaf_subset_of_injective B (Spec (.of A)) hA X.1 X.2
      ((SheafOfModules.toSheaf _).map φ) hφ) hN

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] [IsNoetherianRing A] [IsAdicComplete I A] in
/-- If `𝓚^s` annihilates the kernel of the reduction of `g` modulo `𝓘^(n+1)`, where
`𝓘 = I 𝒪_X`, then the composite `𝓚^s (ker g) ⟶ ker g ⟶ M ⟶ M / 𝓘^(n+1) M` vanishes. -/
theorem C1573.kernel_ι_comp_projection_eq_zero (s : ℕ)
    {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N) (n : ℕ)
    (h : IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K s
      (kernel (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) g))) :
    (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K s (kernel g)).ι ≫ kernel.ι g ≫
      smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) M = 0 := by
  have hc : (kernel.ι g ≫ smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) M) ≫ smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA
        X.1 X.2 (baseIdealSubmodule X.1 X.2 I) (n + 1) g = 0 :=
    (Category.assoc _ _ _).trans ((congrArg (kernel.ι g ≫ ·)
      (smallEtaleAdicQuotientProjection_mapOfHom B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) g)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (kernel.condition g)).trans
        zero_comp)))
  have h0 := idealPowerSubsheaf_ι_comp_eq_zero B (Spec (.of A)) hA X.1 X.2 K s _ _ h
    (kernel.lift _ _ hc)
  exact (congrArg (_ ≫ ·) (kernel.lift_ι _ _ hc).symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h0).trans zero_comp))

/-- A coherent module `P` mapping injectively (on sections) to a module `M` with proper support is
annihilated by `𝓚^s` once the composites `𝓚^s P ⟶ P ⟶ M ⟶ M / 𝓘^(n+1) M` vanish. -/
private theorem isPowAnnihilated_of_comp_projection_eq_zero
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite)
    {P M : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hM : HasProperSupportOverBase X f hf M) (ψ : P.obj ⟶ M.obj) [Mono ψ]
    (hψ : ∀ U : SmallEtale B (Spec (.of A)) hA X.1, Function.Injective (ψ.val.app (op U)))
    (s : ℕ) (h : ∀ n : ℕ, (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K s P.obj).ι ≫ ψ ≫
      smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) M.obj = 0) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K s P.obj := by
  let Q := idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K s P.obj
  let Qc : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
    ⟨Q.toSheafOfModules,
      isCoherent_idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K hK _ P.property s⟩
  let φ : Qc ⟶ M := ObjectProperty.homMk (Q.ι ≫ ψ)
  have hQ : HasProperSupportOverBase X f hf Qc :=
    hasProperSupportOverBase_of_injective X f hf φ.hom
      (fun U => (hψ U).comp Subtype.val_injective) hM
  have hφ : φ = 0 :=
    eq_zero_of_comp_projection_eq_zero X I f hf hQ φ fun n => (Category.assoc _ _ _).trans (h n)
  exact isPowAnnihilated_of_ι_eq_zero X K s _
    ((cancel_mono ψ).1 ((congrArg (·.hom) hφ).trans zero_comp.symm))

include hK in
/-- **The kernel of a map out of a module with proper support is annihilated by `𝓚^s` as soon
as the kernels of its reductions modulo all powers of `I 𝒪_X` are.** -/
theorem C1573.isPowAnnihilated_kernel_of_reductions
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hM : HasProperSupportOverBase X f hf M) (γ : M ⟶ N) (s : ℕ)
    (h : ∀ n : ℕ, IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K s
      (kernel (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) γ.hom))) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K s (kernel γ.hom) :=
  isPowAnnihilated_of_comp_projection_eq_zero X I f hf K hK (P := ⟨kernel γ.hom,
    isCoherent_kernel B (Spec (.of A)) hA X.1 X.2 M.property N.property γ.hom⟩) hM (kernel.ι γ.hom)
    (injective_kernel_ι_app_baseCompletion X γ.hom) s
    (fun n => kernel_ι_comp_projection_eq_zero X I K s γ.hom n (h n))

/-- The reduction modulo `𝓘^(n+1)` of the cokernel of `g` is a quotient of the cokernel of the
reduction of `g`. -/
def C1573.cokernelReductionMap {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N)
    (n : ℕ) :
    cokernel (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) g) ⟶
      smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) (n + 1)
        (cokernel g) :=
  cokernel.desc _ (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) (cokernel.π g)) (by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) M)).1 ?_
    rw [comp_zero, ← Category.assoc, smallEtaleAdicQuotientProjection_mapOfHom, Category.assoc,
      smallEtaleAdicQuotientProjection_mapOfHom, ← Category.assoc, cokernel.condition, zero_comp])

/-- The comparison map `cokernelReductionMap X I g n` is an epimorphism. -/
instance C1573.epi_cokernelReductionMap {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (g : M ⟶ N) (n : ℕ) : Epi (cokernelReductionMap X I g n) := by
  have h : smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) N ≫ cokernel.π _ ≫ cokernelReductionMap X I g n =
      cokernel.π g ≫ smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) (cokernel g) := by
    rw [cokernelReductionMap, cokernel.π_desc, smallEtaleAdicQuotientProjection_mapOfHom]
  have : Epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) N ≫ cokernel.π _ ≫
          cokernelReductionMap X I g n) := by
    rw [h]
    exact @epi_comp _ _ _ _ _ _ inferInstance _
      (inferInstanceAs (Epi (cokernel.π (idealPowerSubsheaf B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) (cokernel g)).ι)))
  exact epi_of_epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
    (baseIdealSubmodule X.1 X.2 I) (n + 1) N ≫ cokernel.π _) _

include hK in
/-- **The cokernel of a map into a module with proper support is annihilated by `𝓚^s` as soon
as the cokernels of its reductions modulo all powers of `I 𝒪_X` are.** -/
theorem C1573.isPowAnnihilated_cokernel_of_reductions
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hN : HasProperSupportOverBase X f hf N) (γ : M ⟶ N) (s : ℕ)
    (h : ∀ n : ℕ, IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K s
      (cokernel (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) γ.hom))) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K s (cokernel γ.hom) :=
  isPowAnnihilated_of_comp_projection_eq_zero X I f hf K hK
    (P := ⟨cokernel γ.hom,
      isCoherent_cokernel B (Spec (.of A)) hA X.1 X.2 M.property N.property γ.hom⟩)
    (hasProperSupport_of_epi B (Spec (.of A)) hA X.2 _ f.hom hf (cokernel.π γ.hom)
      (isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X N.obj) hN)
    (𝟙 _) (fun _ => Function.injective_id) s fun n => by
      rw [Category.id_comp]
      exact idealPowerSubsheaf_ι_comp_eq_zero B (Spec (.of A)) hA X.1 X.2 K s _ _
        (isPowAnnihilated_of_epi B (Spec (.of A)) hA X.1 X.2 K s (cokernelReductionMap X I γ.hom n)
          (h n)) _

end AlgebraicGeometry.Space

end
