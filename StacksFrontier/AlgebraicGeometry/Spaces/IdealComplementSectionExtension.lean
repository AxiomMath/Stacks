module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupportFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardTensorPairing
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealFiniteTypeOfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentExtension

/-!
# Extending a section over the complement of `V(ℐ)` across `V(ℐ)`, up to a power of `ℐ`

Let `Y` be a quasi-compact and quasi-separated algebraic space, `ℐ ⊆ 𝒪_Y` a finite type
quasi-coherent sheaf of ideals with quasi-compact open complement `j : U = Y ∖ V(ℐ) ⟶ Y`, and `𝒢`
a quasi-coherent `𝒪_Y`-module.  A section `s` of `𝒢` over `U` need not extend to a map
`ℐⁿ ⟶ 𝒢` for any `n` when `Y` is not Noetherian (Stacks 01PN); what does extend is the
following.  There are a quasi-coherent module `𝒬`, an epimorphism `ρ : 𝒬 ⟶ ℐⁿ⁺¹` whose kernel is
killed by `ℐᵃ⁺¹`, and a map `q : 𝒬 ⟶ 𝒢` which on `U` — where `ρ` is an isomorphism onto
`ℐⁿ⁺¹|_U = 𝒪_U` — is `s`.  So `ℐᵃ⁺¹𝒬 ⟶ 𝒢` extends `s` up to the factor `ℐᵃ⁺¹`, and its direct
image along an affine morphism is a quotient of `π_*ℐᵃ⁺¹ ⊗ π_*ℐⁿ⁺¹`
(`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardIdealPowSmulQuotient.lean`).

## The construction

Write `η : 𝒢 ⟶ j_*j^*𝒢` for the unit, `s̃ : 𝒪_Y ⟶ j_*j^*𝒢` for the adjoint of `s`, and `𝒞` for
the cokernel of `η`; `j_*j^*𝒢` is quasi-coherent because `j` is quasi-compact and
quasi-separated (Stacks 03M9).

1. `𝒞` restricts to zero on `U`, so the image of `𝒪_Y ⟶ 𝒞` — a finite type quasi-coherent
   module — is killed by some `ℐⁿ⁺¹`
   (`AlgebraicGeometry.Space.exists_smul_eq_zero_of_isZero_restrictToIdealComplement`); hence
   `s̃` maps `ℐⁿ⁺¹` into the image of `η`.
2. `𝒫` is the pullback of the epimorphism `𝒢 ⟶ im η` along `ℐⁿ⁺¹ ⟶ im η`; its projection to
   `ℐⁿ⁺¹` is an epimorphism with kernel the kernel of `η`, which vanishes on `U`.
3. `𝒬 ⊆ 𝒫` is a finite type quasi-coherent submodule (Stacks 0829) containing lifts of
   generators of `ℐⁿ⁺¹` over one surjective affine chart `W`, so that `𝒬 ⟶ ℐⁿ⁺¹` is still an
   epimorphism.
4. Over `W` the kernel of `𝒬(W) ⟶ ℐⁿ⁺¹(W)` is killed by a power of `ℐ(W)`: for generators
   `q_i` of `𝒬(W)` with images `d_i`, a kernel element `k` satisfies
   `d_j k = ∑ αᵢ (d_j q_i - d_i q_j)`, the finitely many `d_j q_i - d_i q_j` are kernel elements,
   each killed by a power of `ℐ(W)` because it vanishes on `U`, and the `d_j` generate
   `ℐ(W)ⁿ⁺¹`.  Quasi-coherence carries this to every chart.

## Main results

* `AlgebraicGeometry.Space.exists_pow_comp_cokernel_eq_zero`: step 1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

variable (Y : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)

/-- The `n`-th power `ℐⁿ`, as an `𝒪_Y`-module. -/
abbrev idealSheafPowModule (n : ℕ) : Modules.{u, u} B S hS Y.1 Y.2 :=
  (SheafOfModules.idealSheafPow I n).toSheafOfModules

/-- The structure sheaf `𝒪_Y`, as an `𝒪_Y`-module. -/
abbrev unitSheafModule : Modules.{u, u} B S hS Y.1 Y.2 :=
  SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)

/-- The inclusion `ℐⁿ ⟶ 𝒪_Y`. -/
abbrev idealSheafPowModuleι (n : ℕ) : idealSheafPowModule B S hS Y I n ⟶ unitSheafModule B S hS Y :=
  (SheafOfModules.idealSheafPow I n).ι

/-- A regular function over a chart, read as a section of the unit module. -/
abbrev ringToUnitSection {W : SmallEtale B S hS Y.1} (c : chartRing B S hS Y.1 Y.2 W) :
    (unitSheafModule B S hS Y).val.obj (op W) :=
  c

/-- `j_*j^*𝒢` for the open immersion `j : Y ∖ V(ℐ) ⟶ Y`. -/
abbrev complementPushPull (G : Modules.{u, u} B S hS Y.1 Y.2) : Modules.{u, u} B S hS Y.1 Y.2 :=
  (modulePushforward B S hS (idealComplementι B S hS Y I)).obj
    ((modulePullback B S hS (idealComplementι B S hS Y I)).obj G)

/-- The unit `η : 𝒢 ⟶ j_*j^*𝒢`. -/
abbrev complementUnit (G : Modules.{u, u} B S hS Y.1 Y.2) : G ⟶ complementPushPull B S hS Y I G :=
  (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).unit.app G

/-- The adjoint `s̃ : 𝒪_Y ⟶ j_*j^*𝒢` of a section `s` of `𝒢` over `Y ∖ V(ℐ)`. -/
def complementSection (G : Modules.{u, u} B S hS Y.1 Y.2)
    (s : SheafOfModules.unit (structureRingSheaf B S hS (idealComplement B S hS Y I)) ⟶
      (restrictToIdealComplement B S hS Y I).obj G) :
    unitSheafModule B S hS Y ⟶ complementPushPull B S hS Y I G :=
  (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).homEquiv _ _
    ((modulePullbackUnitIso B S hS (idealComplementι B S hS Y I)).hom ≫ s ≫
      ((modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS Y I)
        (isEtale_idealComplementι B S hS Y I)).app G).inv)

/-- The pullback of the unit `η` to the open complement is an isomorphism: the counit along an
open immersion is invertible, and the triangle identity makes the pulled-back unit its
section. -/
theorem isIso_modulePullback_map_complementUnit (G : Modules.{u, u} B S hS Y.1 Y.2) :
    IsIso ((modulePullback B S hS (idealComplementι B S hS Y I)).map
      (complementUnit B S hS Y I G)) := by
  have hc := isIso_modulePullbackAdjunction_counit_of_isOpenImmersion B S hS
    (idealComplementι B S hS Y I) (isOpenSubspace_idealComplementSubfunctor B S hS Y I).2
    ((modulePullback B S hS (idealComplementι B S hS Y I)).obj G)
  have htri :=
    (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).left_triangle_components G
  have : IsIso ((modulePullback B S hS (idealComplementι B S hS Y I)).map
      (complementUnit B S hS Y I G) ≫
      (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).counit.app
        ((modulePullback B S hS (idealComplementι B S hS Y I)).obj G)) := by
    rw [htri]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).counit.app
      ((modulePullback B S hS (idealComplementι B S hS Y I)).obj G))

/-- The cokernel of `η` restricts to zero on the open complement. -/
theorem isZero_modulePullback_cokernel_complementUnit (G : Modules.{u, u} B S hS Y.1 Y.2) :
    IsZero ((modulePullback B S hS (idealComplementι B S hS Y I)).obj
      (cokernel (complementUnit B S hS Y I G))) := by
  have := isIso_modulePullback_map_complementUnit B S hS Y I G
  have : PreservesColimits (modulePullback B S hS (idealComplementι B S hS Y I)) :=
    (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).leftAdjoint_preservesColimits
  have hepi : Epi ((modulePullback B S hS (idealComplementι B S hS Y I)).map
      (complementUnit B S hS Y I G)) := IsIso.epi_of_iso _
  exact IsZero.of_iso (isZero_cokernel_of_epi ((modulePullback B S hS
    (idealComplementι B S hS Y I)).map (complementUnit B S hS Y I G)))
    (PreservesCokernel.iso (modulePullback B S hS (idealComplementι B S hS Y I)) _)

variable (hZ : B.Contains (⊤_ Scheme.{u})) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hUqc : IsQuasiCompactSpace B S hS (idealComplement B S hS Y I).1)

/-- `ℐⁿ` is the `n`-th ideal power submodule of `𝒪_Y`. -/
private theorem idealSheafPow_eq_idealPowSubmodule (n : ℕ) :
    SheafOfModules.idealSheafPow I n = idealPowSubmodule I n (unitSheafModule B S hS Y) :=
  Eq.trans (idealSheafPow_eq_idealPow B S hS Y I n)
    (Stacks.Sites.idealSmul_top_eq.{u, u + 1, u} _).symm

/-- Restriction to the open complement preserves finite limits. -/
private theorem preservesFiniteLimits_restrictToIdealComplement :
    PreservesFiniteLimits (restrictToIdealComplement B S hS Y I) :=
  preservesFiniteLimits_etaleModulePullback B S hS (idealComplementι B S hS Y I)
    (isEtale_idealComplementι B S hS Y I)

/-- Restriction to the open complement preserves monomorphisms. -/
private theorem preservesMonomorphisms_restrictToIdealComplement :
    (restrictToIdealComplement B S hS Y I).PreservesMonomorphisms :=
  have := preservesFiniteLimits_restrictToIdealComplement B S hS Y I
  preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **A map out of `𝒪_Y` into a module killed by `ℐⁿ` vanishes on `ℐⁿ⁺¹`.** -/
theorem idealSheafPowModuleι_succ_comp_eq_zero (n : ℕ) {M : Modules.{u, u} B S hS Y.1 Y.2}
    (f : unitSheafModule B S hS Y ⟶ M)
    (hn : ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W),
      a ∈ (SheafOfModules.idealSheafPow I n).obj W → ∀ q : M.val.obj W, a • q = 0) :
    idealSheafPowModuleι B S hS Y I (n + 1) ≫ f = 0 := by
  refine Stacks.SheafOfModules.hom_ext_val_app_apply fun W x => ?_
  have hle : SheafOfModules.idealSheafPow I (n + 1) ≤ SheafOfModules.idealSheafPow I n := by
    rw [idealSheafPow_eq_idealPow B S hS Y I (n + 1), idealSheafPow_eq_idealPow B S hS Y I n]
    exact Stacks.Sites.idealPow_succ_le I n
  have hx : idealPowSectionVal B S hS I (n + 1) x ∈ (SheafOfModules.idealSheafPow I n).obj W :=
    SheafOfModules.Submodule.le_iff.1 hle W (submoduleSection B S hS x).2
  have key := hn W _ hx ((f.val.app W).hom
    (show (unitSheafModule B S hS Y).val.obj W from
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W)))
  have e1 : ((idealSheafPowModuleι B S hS Y I (n + 1)).val.app W).hom x =
      idealPowSectionVal B S hS I (n + 1) x •
        (show (unitSheafModule B S hS Y).val.obj W from
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W)) :=
    (mul_one (idealPowSectionVal B S hS I (n + 1) x)).symm
  rw [Stacks.SheafOfModules.comp_val_app_hom_apply, e1, map_smul, key]
  rfl

include hYqs hUqc in
/-- `j_*j^*𝒢` is quasi-coherent: the open immersion `j` is quasi-compact, its source being
quasi-compact and `Y` quasi-separated (Stacks 073B), and quasi-separated, being a monomorphism;
so Stacks 03M9 applies. -/
theorem isQuasicoherentOnSite_complementPushPull (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite) :
    (complementPushPull B S hS Y I G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS (idealComplementι B S hS Y I)
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hUqc
      (idealComplementι B S hS Y I).hom)
    (isQuasiSeparated_of_mono B S hS (idealComplementι B S hS Y I).hom
      (show Mono (idealComplementSubfunctor B S hS Y I).ι from inferInstance)) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hG)

include hZ hYqc hYqs hUqc in
/-- **Step 1: `s̃` maps a power `ℐⁿ⁺¹` into the image of `η`.**  The image of
`𝒪_Y ⟶ coker η` is a finite type quasi-coherent module vanishing on the open complement, hence
killed by a power of `ℐ`. -/
theorem exists_pow_comp_cokernel_eq_zero (hI : IsFiniteTypeQuasicoherentIdeal B S hS Y I)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite)
    (s : SheafOfModules.unit (structureRingSheaf B S hS (idealComplement B S hS Y I)) ⟶
      (restrictToIdealComplement B S hS Y I).obj G) :
    ∃ n : ℕ, idealSheafPowModuleι B S hS Y I (n + 1) ≫ complementSection B S hS Y I G s ≫
      cokernel.π (complementUnit B S hS Y I G) = 0 := by
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS Y.1 Y.2
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS Y.1 Y.2
  let c := complementSection B S hS Y I G s ≫ cokernel.π (complementUnit B S hS Y I G)
  have hH := isQuasicoherentOnSite_complementPushPull B S hS Y I hZ hYqs hUqc G hG
  have hC : (cokernel (complementUnit B S hS Y I G)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_cokernel _ _ hG hH
  have hunit : (unitSheafModule B S hS Y).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  have hM₀q : (Abelian.image c).IsQuasicoherentOnSite :=
    ObjectProperty.prop_kernel _ _ hC (ObjectProperty.prop_cokernel _ c hunit hC)
  have hM₀ft : SheafOfModules.IsFiniteTypeOnSite (Abelian.image c) :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi (Abelian.factorThruImage c)
      (isFiniteTypeOnSite_unit_structureRingSheaf B S hS Y)
  have hι := isEtale_idealComplementι B S hS Y I
  have hRC : IsZero ((restrictToIdealComplement B S hS Y I).obj
      (cokernel (complementUnit B S hS Y I G))) :=
    IsZero.of_iso (isZero_modulePullback_cokernel_complementUnit B S hS Y I G)
      ((modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS Y I) hι).app _).symm
  have := preservesFiniteLimits_restrictToIdealComplement B S hS Y I
  have := preservesMonomorphisms_restrictToIdealComplement B S hS Y I
  have hRM : IsZero ((restrictToIdealComplement B S hS Y I).obj (Abelian.image c)) :=
    IsZero.of_mono ((restrictToIdealComplement B S hS Y I).map (Abelian.image.ι c)) hRC
  obtain ⟨n, hn⟩ := exists_smul_eq_zero_of_isZero_restrictToIdealComplement B S hS Y hYqc I hI
    (Abelian.image c) hM₀q hM₀ft hRM
  refine ⟨n, ?_⟩
  have h0 : idealSheafPowModuleι B S hS Y I (n + 1) ≫ Abelian.factorThruImage c = 0 :=
    idealSheafPowModuleι_succ_comp_eq_zero B S hS Y I n _ hn
  show idealSheafPowModuleι B S hS Y I (n + 1) ≫ c = 0
  rw [← Abelian.image.fac c, ← Category.assoc, h0, zero_comp]


/-- In a pullback of `e` along `t'`, with `e ≫ m = η` and `t' ≫ m = t`, the two composites to
the common target agree. -/
theorem pullback_fst_comp_eq_snd_comp_of_fac {C : Type*} [Category C] {G H D I' : C}
    (η : G ⟶ H) (e : G ⟶ I') (m : I' ⟶ H) (hη : e ≫ m = η) (t' : D ⟶ I') (t : D ⟶ H)
    (ht : t' ≫ m = t) [HasPullback e t'] :
    pullback.fst e t' ≫ η = pullback.snd e t' ≫ t := by
  rw [← hη, ← ht, ← Category.assoc, pullback.condition, Category.assoc]

/-- **Step 2: the pullback.**  For `η : 𝒢 ⟶ ℋ` invertible on the open complement and
`t : 𝒟 ⟶ ℋ` landing in the image of `η`, the pullback `𝒫` of `𝒢 ⟶ im η` along the
factorization of `t` is quasi-coherent (for quasi-coherent `𝒢`, `ℋ`, `𝒟`), its projection to `𝒟`
is an epimorphism which becomes an isomorphism on the open complement, and its projection to `𝒢`
followed by `η` is its projection to `𝒟` followed by `t`. -/
theorem exists_pullback_stage {G H D : Modules.{u, u} B S hS Y.1 Y.2}
    (hG : G.IsQuasicoherentOnSite) (hH : H.IsQuasicoherentOnSite) (hD : D.IsQuasicoherentOnSite)
    (η : G ⟶ H) (hRη : IsIso ((restrictToIdealComplement B S hS Y I).map η))
    (t : D ⟶ H) (ht : t ≫ cokernel.π η = 0) :
    ∃ (P : Modules.{u, u} B S hS Y.1 Y.2) (_ : P.IsQuasicoherentOnSite)
      (q : P ⟶ G) (ρ : P ⟶ D),
      Epi ρ ∧ IsIso ((restrictToIdealComplement B S hS Y I).map ρ) ∧ q ≫ η = ρ ≫ t := by
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS Y.1 Y.2
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS Y.1 Y.2
  have := isClosedUnderExtensions_quasicoherentSheaves_schemeUniverse B S hS Y.1 Y.2
  obtain ⟨e, he⟩ : ∃ e : G ⟶ Abelian.image η, e = Abelian.factorThruImage η := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : D ⟶ Abelian.image η, t' = kernel.lift (cokernel.π η) t ht := ⟨_, rfl⟩
  have hefac : e ≫ Abelian.image.ι η = η := by rw [he]; exact Abelian.image.fac η
  have htfac : t' ≫ Abelian.image.ι η = t := by rw [ht']; exact kernel.lift_ι (cokernel.π η) t ht
  have : Epi e := by rw [he]; infer_instance
  have hIm : (Abelian.image η).IsQuasicoherentOnSite :=
    ObjectProperty.prop_kernel _ _ hH (ObjectProperty.prop_cokernel _ η hG hH)
  have hP : (pullback e t').IsQuasicoherentOnSite :=
    ObjectProperty.prop_of_isLimit_kernelFork _
      (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct e t')
      (ObjectProperty.prop_biprod _ hG hD) hIm
  have hι := isEtale_idealComplementι B S hS Y I
  have := preservesFiniteLimits_restrictToIdealComplement B S hS Y I
  have := preservesMonomorphisms_restrictToIdealComplement B S hS Y I
  have : (restrictToIdealComplement B S hS Y I).IsLeftAdjoint :=
    (etaleModulePullbackAdjunction B S hS (idealComplementι B S hS Y I) hι).isLeftAdjoint
  have : (restrictToIdealComplement B S hS Y I).PreservesEpimorphisms := inferInstance
  have hRe : IsIso ((restrictToIdealComplement B S hS Y I).map e) := by
    have hfac : (restrictToIdealComplement B S hS Y I).map e ≫
        (restrictToIdealComplement B S hS Y I).map (Abelian.image.ι η) =
          (restrictToIdealComplement B S hS Y I).map η := by
      rw [← Functor.map_comp, hefac]
    have : Mono ((restrictToIdealComplement B S hS Y I).map e) := by
      have : Mono ((restrictToIdealComplement B S hS Y I).map e ≫
          (restrictToIdealComplement B S hS Y I).map (Abelian.image.ι η)) := by
        rw [hfac]; infer_instance
      exact mono_of_mono _ ((restrictToIdealComplement B S hS Y I).map (Abelian.image.ι η))
    exact isIso_of_mono_of_epi _
  refine ⟨pullback e t', hP, pullback.fst e t', pullback.snd e t',
    Abelian.epi_pullback_of_epi_f e t', ?_, ?_⟩
  · have h1 := PreservesPullback.iso_hom_snd (restrictToIdealComplement B S hS Y I) e t'
    rw [← h1]
    infer_instance
  · exact pullback_fst_comp_eq_snd_comp_of_fac η e (Abelian.image.ι η) hefac t' t htfac

/-- **A map of sheaves of modules killing a generating family of sections over `W` kills every
section over an object mapping to `W`.**  This is
`Stacks.SheafOfModules.eq_zero_of_generates` with the morphism to `W` given rather than produced
by terminality. -/
theorem val_app_eq_zero_of_generates {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M Z : SheafOfModules.{u} R} {W V : C} (f : V ⟶ W)
    {n : ℕ} (s : Fin n → M.val.obj (op W)) (hs : PresheafOfModules.Generates J M.val s)
    (d : M ⟶ Z) (hd : ∀ i, (d.val.app (op W)).hom (s i) = 0) (z : M.val.obj (op V)) :
    (d.val.app (op V)).hom z = 0 := by
  obtain ⟨T', hT', h⟩ := hs V f z
  have hsep := Stacks.SheafOfModules.val_app_eq_of_isSeparated d 0 z hT' fun Y g hg => by
    obtain ⟨a, ha⟩ := h Y g hg
    have hz : (M.val.map g.op).hom z =
        ∑ i, a i • M.val.restrictₛₗ (g ≫ f).op (s i) := ha.symm
    have hi : ∀ i, (d.val.app (op Y)).hom (M.val.restrictₛₗ (g ≫ f).op (s i)) = 0 :=
      fun i => by
        show (d.val.app (op Y)).hom ((M.val.map (g ≫ f).op).hom (s i)) = 0
        rw [PresheafOfModules.naturality_apply, hd i]
        exact map_zero _
    rw [hz, map_sum]
    refine (Finset.sum_eq_zero fun i _ => ?_).trans rfl
    rw [map_smul, hi i, smul_zero]
  exact hsep.trans rfl

/-- **A map of `𝒪_Y`-modules killing a generating family of sections over a surjective chart
vanishes**: every chart is covered by charts mapping to the surjective one
(`AlgebraicGeometry.Space.exists_covering_through_affine_over`). -/
theorem eq_zero_of_generates_of_surjective {M Z : Modules.{u, u} B S hS Y.1 Y.2}
    {W : SmallEtale B S hS Y.1}
    (hW : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf W.1.hom)
    {n : ℕ} (s : Fin n → M.val.obj (op W))
    (hs : PresheafOfModules.Generates (SmallEtale.topology B S hS Y.1) M.val s)
    (d : M ⟶ Z) (hd : ∀ i, (d.val.app (op W)).hom (s i) = 0) : d = 0 := by
  refine Stacks.SheafOfModules.hom_ext_val_app_apply fun V z => ?_
  obtain ⟨Sv, hSv, hSvW⟩ := exists_covering_through_affine_over B S hS Y.1 W hW V.unop
  refine (Stacks.SheafOfModules.val_app_eq_of_isSeparated d 0 z hSv fun T h hh => ?_).trans rfl
  obtain ⟨A, l, m, e, -, -⟩ := hSvW h hh
  exact (val_app_eq_zero_of_generates (l ≫ e) s hs d hd _).trans rfl

include hZ hYqc hYqs in
/-- **Step 3: a finite type quasi-coherent submodule which still surjects.**  An epimorphism
`ρ : 𝒫 ⟶ 𝒟` of quasi-coherent `𝒪_Y`-modules onto a module of finite type restricts to an
epimorphism on a finite type quasi-coherent submodule of `𝒫`: lift finitely many generators of
`𝒟` over a surjective affine chart and enclose the lifts (Stacks 0829). -/
theorem exists_finiteType_submodule_epi {P D : Modules.{u, u} B S hS Y.1 Y.2}
    (hP : P.IsQuasicoherentOnSite) (hD : D.IsQuasicoherentOnSite)
    (hDft : SheafOfModules.IsFiniteTypeOnSite D) (ρ : P ⟶ D) [Epi ρ] :
    ∃ Q : P.Submodule, Q.toSheafOfModules.IsQuasicoherentOnSite ∧
      SheafOfModules.IsFiniteTypeOnSite Q.toSheafOfModules ∧ Epi (Q.ι ≫ ρ) := by
  obtain ⟨W, hWa, hWs, -⟩ := exists_surjective_affineChart_of_isQuasiCompactSpace B S hS Y hYqc
  have hDcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 D hD
  have hPcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 P hP
  have hfin := module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite D hDcart
    hDft W hWa
  obtain ⟨r, g, hg⟩ := @Module.Finite.exists_fin (chartRing B S hS Y.1 Y.2 W)
    (D.val.obj (op W)) _ _ _ hfin
  have hgen := generates_of_span_eq_top D hDcart hWa g hg
  have hsurj := surjective_val_app_of_epi_of_isQuasicoherentOnSite ρ inferInstance hP hD W hWa
  choose p hp using fun i => hsurj (g i)
  obtain ⟨Dsub, hDsub⟩ := (chartExtensionProperty_id hZ hYqc hYqs hPcart).exists_forall_mem hPcart
    (Finset.univ : Finset (Fin r)) (fun _ => W) (fun _ => W.1.hom) (fun _ => Category.comp_id _)
    (fun _ => hWa) p
  refine ⟨Dsub.toSubmodule _,
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS Y.1 Y.2 _).2
      (Dsub.isCartesianOnAffineCharts_toSubmodule hPcart),
    Dsub.isFiniteTypeOnSite_toSubmodule hPcart, ?_⟩
  refine Preadditive.epi_of_cancel_zero _ fun {Z} d hd => ?_
  refine eq_zero_of_generates_of_surjective B S hS Y hWs g hgen d fun i => ?_
  have hmem : p i ∈ (Dsub.toSubmodule _).obj (op W) := hDsub i (Finset.mem_univ i)
  have h1 := congrArg (fun φ => (φ.val.app (op W)).hom
    (⟨p i, hmem⟩ : (Dsub.toSubmodule _).toSheafOfModules.val.obj (op W))) hd
  rw [← hp i]
  exact h1.trans rfl

include hZ hYqc hYqs in
/-- **Step 4: the kernel of `𝒬 ⟶ ℐⁿ⁺¹` is killed by a power of `ℐ`**, when `𝒬` is of finite type
and quasi-coherent and `𝒬 ⟶ ℐⁿ⁺¹` is an epimorphism which is a monomorphism on the open
complement.

Over a surjective affine chart `W`, with generators `q_i` of `𝒬(W)` and `d_i ∈ ℐ(W)ⁿ⁺¹` their
images, a kernel element `k = ∑ αᵢ qᵢ` satisfies `d_j k = ∑ αᵢ τᵢⱼ` with
`τᵢⱼ = d_j qᵢ - dᵢ qⱼ` in the kernel.  The `τᵢⱼ` lie in a finite type quasi-coherent submodule of
the kernel (Stacks 0829), which vanishes on the complement and so is killed by some `ℐᴺ`; the
`d_j` generate `ℐ(W)ⁿ⁺¹`, so `ℐ(W)ᴺ⁺ⁿ⁺¹` kills the kernel over `W`, hence everywhere by
quasi-coherence. -/
theorem exists_smul_eq_zero_of_mem_ker (hI : IsFiniteTypeQuasicoherentIdeal B S hS Y I) (n : ℕ)
    {Q : Modules.{u, u} B S hS Y.1 Y.2} (hQ : Q.IsQuasicoherentOnSite)
    (hQft : SheafOfModules.IsFiniteTypeOnSite Q)
    (ρ : Q ⟶ idealSheafPowModule B S hS Y I (n + 1)) [Epi ρ]
    (hR : Mono ((restrictToIdealComplement B S hS Y I).map ρ)) :
    ∃ a : ℕ, ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
        W), r ∈ (SheafOfModules.idealSheafPow I (a + 1)).obj W →
        ∀ k : Q.val.obj W, (ρ.val.app W).hom k = 0 → r • k = 0 := by
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS Y.1 Y.2
  have hι := isEtale_idealComplementι B S hS Y I
  have := preservesFiniteLimits_restrictToIdealComplement B S hS Y I
  have := preservesMonomorphisms_restrictToIdealComplement B S hS Y I
  have : (restrictToIdealComplement B S hS Y I).Additive :=
    etaleModulePullback_additive B S hS (idealComplementι B S hS Y I) hι
  -- the sectionwise kernel, its quasi-coherence and its vanishing on the complement
  let K := homKernelSubmodule B S hS Y ρ
  have hD : (idealSheafPowModule B S hS Y I (n + 1)).IsQuasicoherentOnSite := by
    show ((SheafOfModules.idealSheafPow I (n + 1)).toSheafOfModules).IsQuasicoherentOnSite
    rw [idealSheafPow_eq_idealPowSubmodule B S hS Y I]
    exact isQuasicoherentOnSite_idealPowSubmodule B S hS Y.1 Y.2 I _
      (SheafOfModules.isQuasicoherentOnSite_unit _) hI.1 (n + 1)
  have hKq : K.toSheafOfModules.IsQuasicoherentOnSite :=
    (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      (homKernelSubmoduleIso B S hS Y ρ).symm (ObjectProperty.prop_kernel _ ρ hQ hD)
  have hRK : IsZero ((restrictToIdealComplement B S hS Y I).obj K.toSheafOfModules) := by
    have h0 : (restrictToIdealComplement B S hS Y I).map K.ι = 0 := by
      rw [← cancel_mono ((restrictToIdealComplement B S hS Y I).map ρ), ← Functor.map_comp,
        homKernelSubmodule_ι_comp, Functor.map_zero, zero_comp]
    exact IsZero.of_mono_eq_zero _ h0
  -- a surjective affine chart and generators of `𝒬` over it
  obtain ⟨W, hWa, hWs, hWp⟩ := exists_surjective_affineChart_of_isQuasiCompactSpace B S hS Y hYqc
  have hQcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 Q hQ
  have hfin := module_finite_sections_of_isCartesianOnAffineCharts_of_isFiniteTypeOnSite Q hQcart
    hQft W hWa
  obtain ⟨r, q, hq⟩ := @Module.Finite.exists_fin (chartRing B S hS Y.1 Y.2 W)
    (Q.val.obj (op W)) _ _ _ hfin
  let dd : Fin r → chartRing B S hS Y.1 Y.2 W := fun i =>
    idealPowSectionVal B S hS I (n + 1) ((ρ.val.app (op W)).hom (q i))
  let τ : Fin r × Fin r → Q.val.obj (op W) := fun ij =>
    dd ij.2 • q ij.1 - dd ij.1 • q ij.2
  have hτ : ∀ ij, (ρ.val.app (op W)).hom (τ ij) = 0 := by
    intro ij
    show (ρ.val.app (op W)).hom (dd ij.2 • q ij.1 - dd ij.1 • q ij.2) = 0
    rw [map_sub, map_smul, map_smul]
    refine idealSheafPowSection_ext B S hS ?_
    show dd ij.2 * dd ij.1 - dd ij.1 * dd ij.2 = 0
    rw [mul_comm, sub_self]
  -- the `τᵢⱼ` in a finite type quasi-coherent submodule of the kernel, killed by some `ℐᴺ`
  have hKcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hKq
  let σ : Fin r × Fin r → K.toSheafOfModules.val.obj (op W) := fun ij => ⟨τ ij, hτ ij⟩
  obtain ⟨Dsub, hDsub⟩ := (chartExtensionProperty_id hZ hYqc hYqs hKcart).exists_forall_mem hKcart
    (Finset.univ : Finset (Fin r × Fin r)) (fun _ => W) (fun _ => W.1.hom)
    (fun _ => Category.comp_id _) (fun _ => hWa) σ
  let T := Dsub.toSubmodule _
  have hTq : T.toSheafOfModules.IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS Y.1 Y.2 _).2
      (Dsub.isCartesianOnAffineCharts_toSubmodule hKcart)
  have hTft : SheafOfModules.IsFiniteTypeOnSite T.toSheafOfModules :=
    Dsub.isFiniteTypeOnSite_toSubmodule hKcart
  have hRT : IsZero ((restrictToIdealComplement B S hS Y I).obj T.toSheafOfModules) :=
    IsZero.of_mono ((restrictToIdealComplement B S hS Y I).map T.ι) hRK
  obtain ⟨N, hN⟩ := exists_smul_eq_zero_of_isZero_restrictToIdealComplement B S hS Y hYqc I hI
    T.toSheafOfModules hTq hTft hRT
  have hkillτ : ∀ b : chartRing B S hS Y.1 Y.2 W,
      b ∈ (SheafOfModules.idealSheafPow I N).obj (op W) → ∀ ij, b • τ ij = 0 := by
    intro b hb ij
    have hmem : σ ij ∈ T.obj (op W) := hDsub ij (Finset.mem_univ ij)
    have h1 := hN (op W) b hb (⟨σ ij, hmem⟩ : T.toSheafOfModules.val.obj (op W))
    exact congrArg (fun x : T.toSheafOfModules.val.obj (op W) =>
      (submoduleSection B S hS (submoduleSection B S hS x).1).1) h1
  -- `d_j k` is a combination of the `τᵢⱼ` for a kernel element `k`
  let φ := ((ρ ≫ idealSheafPowModuleι B S hS Y I (n + 1)).val.app (op W)).hom
  have hspan : ∀ k : Q.val.obj (op W), ∃ α : Fin r → chartRing B S hS Y.1 Y.2 W,
      k = ∑ i, α i • q i := fun k =>
    (Submodule.mem_span_range_iff_exists_fun _).1 (by rw [hq]; exact Submodule.mem_top) |>.imp
      fun _ h => h.symm
  have hφ : ∀ α : Fin r → chartRing B S hS Y.1 Y.2 W, φ (∑ i, α i • q i) = ∑ i, α i * dd i :=
    fun α => by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  have hd : ∀ k : Q.val.obj (op W), (ρ.val.app (op W)).hom k = 0 →
      ∀ b : chartRing B S hS Y.1 Y.2 W, b ∈ (SheafOfModules.idealSheafPow I N).obj (op W) →
        ∀ j, b • dd j • k = 0 := by
    intro k hk b hb j
    obtain ⟨α, rfl⟩ := hspan k
    have hsum : ∑ i, α i * dd i = 0 := by
      rw [← hφ]
      show ((idealSheafPowModuleι B S hS Y I (n + 1)).val.app (op W)).hom
        ((ρ.val.app (op W)).hom (∑ i, α i • q i)) = 0
      rw [hk, map_zero]
    have hexp : dd j • ∑ i, α i • q i =
        ∑ i, α i • τ (i, j) + (∑ i, α i * dd i) • q j := by
      simp only [τ, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [sub_add_cancel]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    rw [hexp, hsum, zero_smul, add_zero, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_comm, hkillτ b hb (i, j), smul_zero]
  -- the images `d_j` generate `ℐ(W)ⁿ⁺¹`
  have hc : ∀ c ∈ chartSectionIdeal B S hS Y.1 Y.2 I W ^ (n + 1),
      ∃ γ : Fin r → chartRing B S hS Y.1 Y.2 W, c = ∑ j, γ j * dd j := by
    intro c hc
    have hc1 : ringToUnitSection B S hS Y c ∈
        (SheafOfModules.idealSheafPow I (n + 1)).obj (op W) := by
      have h3 := Submodule.smul_mem_smul hc (Submodule.mem_top (R := chartRing B S hS Y.1 Y.2 W)
        (x := ringToUnitSection B S hS Y (1 : chartRing B S hS Y.1 Y.2 W)))
      have h4 : (c • ringToUnitSection B S hS Y (1 : chartRing B S hS Y.1 Y.2 W) :
          (unitSheafModule B S hS Y).val.obj (op W)) = ringToUnitSection B S hS Y c :=
        mul_one c
      rw [h4] at h3
      exact (SetLike.ext_iff.1 (idealSheafPow_obj_eq_pow_smul_top_of_isAffine B S hS I hI.1 (n + 1)
        hWa) _).2 h3
    obtain ⟨q', hq'⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite ρ inferInstance hQ hD W
      hWa ⟨_, hc1⟩
    obtain ⟨γ, rfl⟩ := hspan q'
    refine ⟨γ, ?_⟩
    rw [← hφ]
    show c = ((idealSheafPowModuleι B S hS Y I (n + 1)).val.app (op W)).hom
      ((ρ.val.app (op W)).hom (∑ j, γ j • q j))
    rw [hq']
    rfl
  -- `ℐ(W)ᴺ⁺ⁿ⁺¹` kills the kernel over `W`, hence everywhere
  have hW : chartSectionIdeal B S hS Y.1 Y.2 I W ^ (N + (n + 1)) •
      (⊤ : Submodule (chartRing B S hS Y.1 Y.2 W) (K.toSheafOfModules.val.obj (op W))) = ⊥ := by
    refine le_bot_iff.1 (Submodule.smul_le.2 fun t ht x _ => ?_)
    rw [Submodule.mem_bot]
    rw [pow_add] at ht
    refine Submodule.mul_induction_on' (fun b hb c hc' => ?_) (fun t₁ _ t₂ _ h₁ h₂ => ?_) ht
    · have hb' : b ∈ (SheafOfModules.idealSheafPow I N).obj (op W) := by
        have h := idealSheafPow_eq_idealPow B S hS Y I N
        have h' := pow_chartSectionIdeal_le_chartIdealPow B S hS Y.1 Y.2 I N W hb
        exact h ▸ h'
      obtain ⟨γ, rfl⟩ := hc c hc'
      refine Subtype.ext ?_
      show (b * ∑ j, γ j * dd j) • (submoduleSection B S hS x).1 = 0
      rw [mul_smul, Finset.sum_smul, Finset.smul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [mul_smul, smul_comm, hd _ (submoduleSection B S hS x).2 b hb' j, smul_zero]
    · rw [add_smul, h₁, h₂, add_zero]
  have hglob := sectionIdeal_pow_smul_top_eq_bot_of_surjective_affine_chart B S hS Y.1 Y.2
    K.toSheafOfModules hKq I hI.1 W hWa hWp (N + (n + 1)) hW
  have hzero := (idealSmul_idealPow_top_eq_bot_iff B S hS Y.1 Y.2 I K.toSheafOfModules
    (N + (n + 1))).2 hglob
  refine ⟨N + n, fun W' r hr k hk => ?_⟩
  have h6 := smul_eq_zero_of_idealSmul_idealPow_top_eq_bot B S hS Y I (N + (n + 1))
    K.toSheafOfModules hzero W' r hr (⟨k, hk⟩ : K.toSheafOfModules.val.obj W')
  exact congrArg (fun x : K.toSheafOfModules.val.obj W' => (submoduleSection B S hS x).1) h6

/-- `ℐⁿ` is quasi-coherent, for a quasi-coherent sheaf of ideals `ℐ`. -/
theorem isQuasicoherentOnSite_idealSheafPowModule (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (n : ℕ) : (idealSheafPowModule B S hS Y I n).IsQuasicoherentOnSite := by
  show ((SheafOfModules.idealSheafPow I n).toSheafOfModules).IsQuasicoherentOnSite
  rw [idealSheafPow_eq_idealPowSubmodule B S hS Y I]
  exact isQuasicoherentOnSite_idealPowSubmodule B S hS Y.1 Y.2 I _
    (SheafOfModules.isQuasicoherentOnSite_unit _) hI n

/-- `ℐⁿ` is of finite type, for a sheaf of ideals `ℐ` of finite type. -/
theorem isFiniteTypeOnSite_idealSheafPowModule
    (hI : SheafOfModules.IsFiniteTypeOnSite I.toSheafOfModules) (n : ℕ) :
    SheafOfModules.IsFiniteTypeOnSite (idealSheafPowModule B S hS Y I n) := by
  have hI' : PresheafOfModules.IsFiniteType (SmallEtale.topology B S hS Y.1)
      I.toSheafOfModules.val :=
    Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _ hI
  have hunit : PresheafOfModules.IsFiniteType (SmallEtale.topology B S hS Y.1)
      (SheafOfModules.unit (structureRingSheaf B S hS Y)).val :=
    PresheafOfModules.isFiniteType_unit _
  have h := Stacks.Sites.isFiniteType_idealPowSmul
    (M := SheafOfModules.unit (structureRingSheaf B S hS Y)) I hI' n ⊤
    (Stacks.Sites.isFiniteType_top (M := SheafOfModules.unit (structureRingSheaf B S hS Y)) hunit)
  have key : SheafOfModules.idealSheafPow I n =
      Stacks.Sites.idealPowSmul (M := SheafOfModules.unit (structureRingSheaf B S hS Y)) I n ⊤ :=
    idealSheafPow_eq_idealPowSubmodule B S hS Y I n
  show SheafOfModules.IsFiniteTypeOnSite (SheafOfModules.idealSheafPow I n).toSheafOfModules
  rw [key]
  exact Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType _ h

/-- The inclusion `ℐⁿ ⟶ 𝒪_Y` becomes an isomorphism on the open complement. -/
theorem isIso_restrictToIdealComplement_map_idealSheafPowModuleι (n : ℕ) :
    IsIso ((restrictToIdealComplement B S hS Y I).map (idealSheafPowModuleι B S hS Y I n)) := by
  show IsIso ((restrictToIdealComplement B S hS Y I).map (SheafOfModules.idealSheafPow I n).ι)
  rw [idealSheafPow_eq_idealPowSubmodule B S hS Y I]
  exact isIso_restrictToIdealComplement_map_idealPowModuleι B S hS Y I n (unitSheafModule B S hS Y)

/-- For an adjunction `L ⊣ R`, applying `L` to the adjoint of `σ` and composing with the counit
gives back `σ`. -/
theorem map_homEquiv_comp_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B₀ : D} (σ : L.obj A ⟶ B₀) :
    L.map (adj.homEquiv A B₀ σ) ≫ adj.counit.app B₀ = σ := by
  conv_rhs => rw [← (adj.homEquiv A B₀).symm_apply_apply σ]
  rw [Adjunction.homEquiv_counit]

/-- Applying `j^*` to the adjoint `s̃` of `s` and composing with the counit recovers `s`. -/
theorem map_complementSection_comp_counit (G : Modules.{u, u} B S hS Y.1 Y.2)
    (s : unitSheafModule B S hS (idealComplement B S hS Y I) ⟶
      (restrictToIdealComplement B S hS Y I).obj G) :
    (modulePullback B S hS (idealComplementι B S hS Y I)).map (complementSection B S hS Y I G s) ≫
      (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).counit.app
        ((modulePullback B S hS (idealComplementι B S hS Y I)).obj G) =
      (modulePullbackUnitIso B S hS (idealComplementι B S hS Y I)).hom ≫ s ≫
        ((modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS Y I)
          (isEtale_idealComplementι B S hS Y I)).app G).inv :=
  map_homEquiv_comp_counit _ _

/-- Composing with an isomorphism after a factorization through its inverse. -/
theorem comp_comp_hom_eq_of_comp_eq_comp_inv {C : Type*} [Category C] {A₀ B₁ C₁ C₂ H₀ : C}
    (f : A₀ ⟶ H₀) (c : H₀ ⟶ C₁) (w : A₀ ⟶ B₁) (s : B₁ ⟶ C₂) (e : C₁ ≅ C₂)
    (h : f ≫ c = w ≫ s ≫ e.inv) : f ≫ c ≫ e.hom = w ≫ s := by
  rw [← Category.assoc, h]
  simp

/-- `j^*s̃ ≫ counit ≫ (j^* ≅ j^{-1})` recovers `s` after the identification `j^*𝒪_Y ≅ 𝒪_U`. -/
theorem map_complementSection_comp_counit_comp_hom (G : Modules.{u, u} B S hS Y.1 Y.2)
    (s : unitSheafModule B S hS (idealComplement B S hS Y I) ⟶
      (restrictToIdealComplement B S hS Y I).obj G) :
    (modulePullback B S hS (idealComplementι B S hS Y I)).map (complementSection B S hS Y I G s) ≫
      (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).counit.app
        ((modulePullback B S hS (idealComplementι B S hS Y I)).obj G) ≫
      ((modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS Y I)
          (isEtale_idealComplementι B S hS Y I)).app G).hom =
      (modulePullbackUnitIso B S hS (idealComplementι B S hS Y I)).hom ≫ s :=
  comp_comp_hom_eq_of_comp_eq_comp_inv _ _ _ _ _ (map_complementSection_comp_counit B S hS Y I G s)

/-- The category-theoretic core of the last step of
`AlgebraicGeometry.Space.exists_idealPowModule_extension_of_section`. -/
theorem comp_eq_zero_of_map_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] (L : C ⥤ D) {Q G H D₀ O : C} (q : Q ⟶ G) (η : G ⟶ H) (ρ : Q ⟶ D₀)
    (ι : D₀ ⟶ O) (st : O ⟶ H) (hcomm : q ≫ η = ρ ≫ ι ≫ st) (c : L.obj H ⟶ L.obj G)
    (hc : L.map η ≫ c = 𝟙 _) {E W Z : D} (φ : L.obj G ⟶ E) (w : L.obj O ⟶ W) (s : W ⟶ E)
    (d : E ⟶ Z) (hst : L.map st ≫ c ≫ φ = w ≫ s) (hd : L.map q ≫ φ ≫ d = 0)
    [Epi (L.map ρ)] [Epi (L.map ι)] [Epi w] : s ≫ d = 0 := by
  have h1 : L.map q = L.map ρ ≫ L.map ι ≫ L.map st ≫ c := by
    calc L.map q = L.map q ≫ L.map η ≫ c := by rw [hc, Category.comp_id]
      _ = L.map (q ≫ η) ≫ c := by rw [Functor.map_comp, Category.assoc]
      _ = _ := by rw [hcomm, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  have h2 : L.map ρ ≫ L.map ι ≫ w ≫ s ≫ d = 0 := by
    rw [← hd, h1]
    simp only [Category.assoc]
    rw [← Category.assoc c, ← Category.assoc (L.map st), hst, Category.assoc]
  refine (cancel_epi w).1 ?_
  refine (cancel_epi (L.map ι)).1 ?_
  refine (cancel_epi (L.map ρ)).1 ?_
  simpa using h2

/-- **The last step of `AlgebraicGeometry.Space.exists_idealPowModule_extension_of_section`.**
If `q : 𝒬 ⟶ 𝒢` and an epimorphism `ρ : 𝒬 ⟶ ℐⁿ⁺¹` satisfy `q ≫ η = ρ ≫ ι ≫ s̃`, then every map out
of `𝒢|_U` killing the restriction of `ℐᵃ⁺¹𝒬 ⟶ 𝒬 ⟶ 𝒢` kills `s`. -/
theorem comp_eq_zero_of_comp_complementUnit_eq (G : Modules.{u, u} B S hS Y.1 Y.2)
    (s : unitSheafModule B S hS (idealComplement B S hS Y I) ⟶
      (restrictToIdealComplement B S hS Y I).obj G)
    {n : ℕ} {Q : Modules.{u, u} B S hS Y.1 Y.2} (ρ : Q ⟶ idealSheafPowModule B S hS Y I (n + 1))
    [Epi ρ] (q : Q ⟶ G)
    (hcomm : q ≫ complementUnit B S hS Y I G =
      ρ ≫ idealSheafPowModuleι B S hS Y I (n + 1) ≫ complementSection B S hS Y I G s)
    (a : ℕ) ⦃Z : Modules.{u, u} B S hS (idealComplement B S hS Y I).1
      (idealComplement B S hS Y I).2⦄
    (d : (restrictToIdealComplement B S hS Y I).obj G ⟶ Z)
    (hd : (restrictToIdealComplement B S hS Y I).map (idealPowModuleι I (a + 1) Q ≫ q) ≫ d = 0) :
    s ≫ d = 0 := by
  have := isIso_restrictToIdealComplement_map_idealPowModuleι B S hS Y I (a + 1) Q
  have hd1 : (restrictToIdealComplement B S hS Y I).map q ≫ d = 0 := by
    rw [Functor.map_comp, Category.assoc] at hd
    exact (cancel_epi _).1 (hd.trans comp_zero.symm)
  have hnat := (modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS Y I)
    (isEtale_idealComplementι B S hS Y I)).hom.naturality q
  have hL : (modulePullback B S hS (idealComplementι B S hS Y I)).map q ≫
      ((modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS Y I)
        (isEtale_idealComplementι B S hS Y I)).app G).hom ≫ d = 0 := by
    have e1 := congrArg (· ≫ d) hnat
    refine (Category.assoc _ _ _).symm.trans (e1.trans ?_)
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (_ ≫ ·) hd1).trans comp_zero
  have : (modulePullback B S hS (idealComplementι B S hS Y I)).IsLeftAdjoint :=
    (modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).isLeftAdjoint
  have : IsIso ((modulePullback B S hS (idealComplementι B S hS Y I)).map
      (idealSheafPowModuleι B S hS Y I (n + 1))) :=
    (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS
      (idealComplementι B S hS Y I) (isEtale_idealComplementι B S hS Y I)) _).2
      (isIso_restrictToIdealComplement_map_idealSheafPowModuleι B S hS Y I (n + 1))
  exact comp_eq_zero_of_map_comp_eq_zero (modulePullback B S hS (idealComplementι B S hS Y I)) q
    (complementUnit B S hS Y I G) ρ (idealSheafPowModuleι B S hS Y I (n + 1))
    (complementSection B S hS Y I G s) hcomm
    ((modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).counit.app
      ((modulePullback B S hS (idealComplementι B S hS Y I)).obj G))
    ((modulePullbackAdjunction B S hS (idealComplementι B S hS Y I)).left_triangle_components G)
    _ _ s d (map_complementSection_comp_counit_comp_hom B S hS Y I G s) hL

include hZ hYqc hYqs hUqc in
/-- **A section of a quasi-coherent module over `Y ∖ V(ℐ)` extends across `V(ℐ)` up to a power of
`ℐ`.**  Let `Y` be quasi-compact and quasi-separated, `ℐ` a finite type quasi-coherent sheaf of
ideals with quasi-compact complement `U = Y ∖ V(ℐ)`, `𝒢` quasi-coherent and `s` a section of `𝒢`
over `U`.  Then there are a quasi-coherent module `𝒬`, an epimorphism `ρ : 𝒬 ⟶ ℐⁿ⁺¹` whose kernel
is killed by `ℐᵃ⁺¹`, and a map `q : 𝒬 ⟶ 𝒢` such that the restriction of `ℐᵃ⁺¹𝒬 ⟶ 𝒬 ⟶ 𝒢` to `U`
hits `s`: every map out of `𝒢|_U` killing it kills `s`.

When `Y` is Noetherian one can take `𝒬 = ℐⁿ⁺¹` (Stacks 07UM); in general no map `ℐᵐ ⟶ 𝒢` need
extend `s` (Stacks 01PN), and the kernel of `ρ` is what absorbs the obstruction. -/
theorem exists_idealPowModule_extension_of_section (hI : IsFiniteTypeQuasicoherentIdeal B S hS Y I)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite)
    (s : unitSheafModule B S hS (idealComplement B S hS Y I) ⟶
      (restrictToIdealComplement B S hS Y I).obj G) :
    ∃ (Q : Modules.{u, u} B S hS Y.1 Y.2) (_ : Q.IsQuasicoherentOnSite) (n a : ℕ)
      (ρ : Q ⟶ idealSheafPowModule B S hS Y I (n + 1)) (_ : Epi ρ)
      (_ : ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
        (r : (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W),
        r ∈ (SheafOfModules.idealSheafPow I (a + 1)).obj W →
          ∀ k : Q.val.obj W, (ρ.val.app W).hom k = 0 → r • k = 0)
      (q : Q ⟶ G),
      ∀ ⦃Z : Modules.{u, u} B S hS (idealComplement B S hS Y I).1
          (idealComplement B S hS Y I).2⦄
        (d : (restrictToIdealComplement B S hS Y I).obj G ⟶ Z),
        (restrictToIdealComplement B S hS Y I).map (idealPowModuleι I (a + 1) Q ≫ q) ≫ d = 0 →
          s ≫ d = 0 := by
  have hι := isEtale_idealComplementι B S hS Y I
  let L := modulePullback B S hS (idealComplementι B S hS Y I)
  let φe := modulePullbackIsoEtaleModulePullback B S hS (idealComplementι B S hS Y I) hι
  obtain ⟨n, hn⟩ := exists_pow_comp_cokernel_eq_zero B S hS Y I hZ hYqc hYqs hUqc hI G hG s
  let η := complementUnit B S hS Y I G
  let t := idealSheafPowModuleι B S hS Y I (n + 1) ≫ complementSection B S hS Y I G s
  have ht : t ≫ cokernel.π η = 0 := (Category.assoc _ _ _).trans hn
  have hRη : IsIso ((restrictToIdealComplement B S hS Y I).map η) :=
    (NatIso.isIso_map_iff φe η).1 (isIso_modulePullback_map_complementUnit B S hS Y I G)
  have hD := isQuasicoherentOnSite_idealSheafPowModule B S hS Y I hI.1 (n + 1)
  have hDft := isFiniteTypeOnSite_idealSheafPowModule B S hS Y I hI.2 (n + 1)
  have hH := isQuasicoherentOnSite_complementPushPull B S hS Y I hZ hYqs hUqc G hG
  obtain ⟨P, hPq, q₀, ρ₀, hρ₀, hRρ₀, hcomm⟩ :=
    exists_pullback_stage B S hS Y I hG hH hD η hRη t ht
  obtain ⟨Qs, hQq, hQft, hQepi⟩ :=
    @exists_finiteType_submodule_epi B S hS Y hZ hYqc hYqs P _ hPq hD hDft ρ₀ hρ₀
  have := preservesFiniteLimits_restrictToIdealComplement B S hS Y I
  have := preservesMonomorphisms_restrictToIdealComplement B S hS Y I
  have hR : Mono ((restrictToIdealComplement B S hS Y I).map (Qs.ι ≫ ρ₀)) := by
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨a, ha⟩ := @exists_smul_eq_zero_of_mem_ker B S hS Y I hZ hYqc hYqs hI n _ hQq hQft
    (Qs.ι ≫ ρ₀) hQepi hR
  exact ⟨Qs.toSheafOfModules, hQq, n, a, Qs.ι ≫ ρ₀, hQepi, ha, Qs.ι ≫ q₀,
    fun Z d hd => comp_eq_zero_of_comp_complementUnit_eq B S hS Y I G s (Qs.ι ≫ ρ₀) (Qs.ι ≫ q₀)
      (by rw [Category.assoc, hcomm, ← Category.assoc]) a d hd⟩

end AlgebraicGeometry.Space

end
