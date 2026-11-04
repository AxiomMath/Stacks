module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Annihilator
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# The levelwise and the module form of annihilation of a kernel and a cokernel

Let `Y` be an affine Noetherian scheme, let `𝓘, 𝓚 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals and
let `α : (F_n) ⟶ (G_n)` be a morphism of `Coh(Y, 𝓘)`. Tag 087W identifies `Coh(Y, 𝓘)` with the
finite modules over the `I`-adic completion of `A = Γ(Y, ⊤)`, and under that identification `α`
becomes a map `α_Y : M → N` of such modules. This file proves the equivalence of the two
conditions of Tag 0888 which refer to the affine scheme `Y` itself:

* the *levelwise* condition, that one positive power of `𝓚` annihilates every `Ker(α_n)` and every
  `Coker(α_n)` — this is `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower`, condition (1)
  of the source;
* the *module* condition, that one positive power of `K = 𝓚(⊤)` annihilates `Ker(α_Y)` and
  `Coker(α_Y)` — condition (2) of the source, read at the affine open `Y` itself.

Both implications use the commutative-algebra fact of the source, which is
`Ideal.existsUnique_canonicalMap_of_smul_eq_bot`: along an exact sequence
`0 → T → M → N → Q → 0` whose end terms are killed by an ideal `J`, every pair `f, g ∈ J`
determines a map `"fg" : N → M` whose composites with `M → N` are multiplication by `f * g` on
both sides.

In the direction from the module condition to the levelwise one, `"fg"` carries `I ⁿ⁺¹ N` into
`I ⁿ⁺¹ M`, so it descends to the reductions, and the reduction of `α_Y` modulo `I ⁿ⁺¹` is the map
of global sections `Γ(α_n)`, because the projection of `M` onto `Γ(F_n, ⊤)` is surjective with
kernel `I ⁿ⁺¹ M`. Hence `K ^ (2t)` annihilates the kernel and the cokernel of each `Γ(α_n)`, and
on an affine scheme that is annihilation of the sheaf kernel and the sheaf cokernel, since
evaluation at `⊤` preserves both for quasi-coherent modules.

In the converse direction the same projections show that an element of `Ker(α_Y)` is killed by
`K ^ t` modulo every `I ⁿ⁺¹`, and `M` is `I`-adically separated; and that `K ^ t` carries every
element of `N` into the image of `α_Y` modulo every `I ⁿ⁺¹`, while `N / Im(α_Y)` is a finite
module over the completion and hence also separated.

The module condition is stated through the inverse limit `lim Γ(F_n, ⊤)` rather than through
`Stacks.Coherent.completedModuleAsBase`. The two are identified by the comparison isomorphism of
Tag 087W, but the limit mentions only the system and not the ideal sheaf `𝓘` along which it is
adic, so the condition may be stated for an arbitrary `𝓘 : Y.IdealSheafData` and not only for one
presented as `Scheme.IdealSheafData.ofIdealTop I`. That is what makes it usable on the affine
opens of a scheme, where the restricted ideal sheaf is not given in that presentation.

## Main definitions

* `Stacks.Algebraization.adicSystemLimitMap` — the map `α_Y` of Tag 087W, in its inverse-limit
  spelling.
* `Stacks.Algebraization.IsAffineKernelCokernelAnnihilated` — condition (2) of Tag 0888 at the
  affine open `Y`: a positive power of `𝓚(⊤)` annihilates `Ker(α_Y)` and `Coker(α_Y)`.

## Main results

* `Ideal.le_annihilator_ker_iff` and `Ideal.le_annihilator_coker_iff` — the elementwise form of
  annihilation of the kernel and of the cokernel of a linear map.
* `Stacks.Algebraization.isAffineKernelCokernelAnnihilated_iff` — the elementwise form of the
  module condition.
* `Stacks.Algebraization.adicSystemLimitMap_comparison` — the comparison isomorphism of Tag 087W
  intertwines `α_Y` with the map of completed modules.
* `Stacks.Algebraization.exists_apply_eq_smul_of_cokernel_eq_bot` — the levelwise annihilation of
  the cokernels carries a power of `K` into the image of the map of completed modules.
* `Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_eq_bot_of_sections` — on an affine
  scheme, annihilation of the kernel and the cokernel of a morphism *on global sections* by a
  fixed power of `K` is annihilation of its sheaf kernel and sheaf cokernel by that same power.
* `Stacks.Algebraization.sections_kernel_cokernel_annihilated_of_module` — the module condition
  gives the elementwise levelwise condition, with the exponent doubled.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_iff_affine` — **Tag 0888, the
  equivalence of conditions (1) and (2) on an affine Noetherian scheme.**

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules Y.ringCatSheaf`, and the two
presentations carry separately declared instances, so every categorical construction below names
its category explicitly as `(C := Y.Modules)` and the coherence of a kernel or a cokernel is
supplied by name rather than left to instance search.

The exponent is carried explicitly rather than hidden behind
`Stacks.Algebraization.IsPowerAnnihilated`: the levelwise condition demands one exponent valid at
every index at once, so a per-index exponent — which is what the existential conclusion of
`Stacks.Algebraization.isPowerAnnihilated_kernel_cokernel_of_sections` provides — is not enough.
This is why `Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_eq_bot_of_sections` is
stated at a fixed exponent.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Ideal

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- An ideal annihilates the kernel of a linear map exactly when each of its elements kills every
element that the map sends to zero. -/
public theorem le_annihilator_ker_iff (J : Ideal A) (φ : M →ₗ[A] N) :
    J ≤ Module.annihilator A ↥(LinearMap.ker φ) ↔
      ∀ r ∈ J, ∀ x : M, φ x = 0 → r • x = 0 := by
  constructor
  · intro h r hr x hx
    exact congrArg Subtype.val
      (Module.mem_annihilator.mp (h hr) ⟨x, LinearMap.mem_ker.mpr hx⟩)
  · intro h r hr
    rw [Module.mem_annihilator]
    exact fun z => Subtype.ext (h r hr z.1 (LinearMap.mem_ker.mp z.2))

/-- An ideal annihilates the cokernel of a linear map exactly when each of its elements carries
every element of the target into the image. -/
public theorem le_annihilator_coker_iff (J : Ideal A) (φ : M →ₗ[A] N) :
    J ≤ Module.annihilator A (N ⧸ LinearMap.range φ) ↔
      ∀ r ∈ J, ∀ y : N, ∃ x : M, φ x = r • y := by
  constructor
  · intro h r hr y
    have h0 := Module.mem_annihilator.mp (h hr)
      (Submodule.Quotient.mk (p := LinearMap.range φ) y)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact LinearMap.mem_range.mp h0
  · intro h r hr
    rw [Module.mem_annihilator]
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.2 (h r hr y)

variable {M₁ M₂ N₁ N₂ : Type*} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]

/-- Annihilation of the kernel transports along a commutative square whose vertical maps are
linear equivalences. -/
public theorem kernel_annihilation_congr (eM : M₁ ≃ₗ[A] M₂) (eN : N₁ ≃ₗ[A] N₂)
    (φ : M₁ →ₗ[A] N₁) (ψ : M₂ →ₗ[A] N₂) (hsq : ∀ x, ψ (eM x) = eN (φ x)) (J : Ideal A) :
    (∀ r ∈ J, ∀ x : M₂, ψ x = 0 → r • x = 0) ↔ ∀ r ∈ J, ∀ x : M₁, φ x = 0 → r • x = 0 := by
  constructor
  · intro h r hr x hx
    refine eM.injective ?_
    rw [eM.map_smul, h r hr (eM x) (by rw [hsq x, hx, map_zero]), map_zero]
  · intro h r hr x hx
    obtain ⟨m, rfl⟩ := eM.surjective x
    have hm : φ m = 0 := eN.injective (by rw [← hsq m, hx, map_zero])
    rw [← eM.map_smul, h r hr m hm, map_zero]

/-- Annihilation of the cokernel transports along a commutative square whose vertical maps are
linear equivalences. -/
public theorem cokernel_annihilation_congr (eM : M₁ ≃ₗ[A] M₂) (eN : N₁ ≃ₗ[A] N₂)
    (φ : M₁ →ₗ[A] N₁) (ψ : M₂ →ₗ[A] N₂) (hsq : ∀ x, ψ (eM x) = eN (φ x)) (J : Ideal A) :
    (∀ r ∈ J, ∀ y : N₂, ∃ x : M₂, ψ x = r • y) ↔
      ∀ r ∈ J, ∀ y : N₁, ∃ x : M₁, φ x = r • y := by
  constructor
  · intro h r hr y
    obtain ⟨z, hz⟩ := h r hr (eN y)
    obtain ⟨m, rfl⟩ := eM.surjective z
    exact ⟨m, eN.injective (by rw [← hsq m, hz, eN.map_smul])⟩
  · intro h r hr y
    obtain ⟨n, rfl⟩ := eN.surjective y
    obtain ⟨m, hm⟩ := h r hr n
    exact ⟨eM m, by rw [hsq m, hm, eN.map_smul]⟩

end Ideal

namespace Stacks.Algebraization

/-! ### The map of Tag 087W in its inverse-limit spelling -/

/-- **The map `α_Y` of Tag 0888.** The map of modules over the completion which Tag 087W attaches
to a morphism of coherent adic systems, written as the induced map of the inverse limits of the
systems of global sections.

Only the systems enter, not the ideal sheaf along which they are adic, so this is available for an
arbitrary `𝓘 : Y.IdealSheafData`. -/
public def adicSystemLimitMap {Y : Scheme.{u}} {ℐ : Y.IdealSheafData}
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (f : F ⟶ G) :
    (limit (Stacks.Coherent.globalSectionsSystem F) : ModuleCat.{u} Γ(Y, ⊤)) ⟶
      (limit (Stacks.Coherent.globalSectionsSystem G) : ModuleCat.{u} Γ(Y, ⊤)) :=
  limMap (F := Stacks.Coherent.globalSectionsSystem F)
    (G := Stacks.Coherent.globalSectionsSystem G)
    (Functor.whiskerRight f.hom (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)))

/-- **Tag 0888 (2), at the affine open `Y` itself.** A morphism of coherent adic systems on an
affine scheme has *kernel and cokernel annihilated by a power of the ideal `K ⊆ Γ(Y, ⊤)`* if one
positive power of `K` annihilates both `Ker(α_Y)` and `Coker(α_Y)`.

The annihilating ideal is taken as an ideal of `Γ(Y, ⊤)` rather than as an ideal sheaf; on an
affine scheme the two are interchangeable by
`AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`, and this is the form the source states
condition (2) in. -/
public def IsAffineKernelCokernelAnnihilated {Y : Scheme.{u}}
    (K : Ideal Γ(Y, ⊤)) {ℐ : Y.IdealSheafData}
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (f : F ⟶ G) : Prop :=
  ∃ t : ℕ, 0 < t ∧
    K ^ t ≤ Module.annihilator Γ(Y, ⊤) ↥(LinearMap.ker (adicSystemLimitMap f).hom) ∧
      K ^ t ≤ Module.annihilator Γ(Y, ⊤)
        (↥(limit (Stacks.Coherent.globalSectionsSystem G) : ModuleCat.{u} Γ(Y, ⊤)) ⧸
          LinearMap.range (adicSystemLimitMap f).hom)

/-- **The elementwise form of Tag 0888 (2).** The module condition says that for one positive
exponent `t` every element of `K ^ t` kills every element of the source killed by `α_Y`, and
carries every element of the target into the image of `α_Y`. -/
public theorem isAffineKernelCokernelAnnihilated_iff {Y : Scheme.{u}}
    (K : Ideal Γ(Y, ⊤)) {ℐ : Y.IdealSheafData}
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (f : F ⟶ G) :
    IsAffineKernelCokernelAnnihilated K f ↔
      ∃ t : ℕ, 0 < t ∧
        (∀ r ∈ K ^ t,
            ∀ x : (limit (Stacks.Coherent.globalSectionsSystem F) : ModuleCat.{u} Γ(Y, ⊤)),
              (adicSystemLimitMap f).hom x = 0 → r • x = 0) ∧
          ∀ r ∈ K ^ t,
            ∀ y : (limit (Stacks.Coherent.globalSectionsSystem G) : ModuleCat.{u} Γ(Y, ⊤)),
              ∃ x : (limit (Stacks.Coherent.globalSectionsSystem F) : ModuleCat.{u} Γ(Y, ⊤)),
                (adicSystemLimitMap f).hom x = r • y :=
  exists_congr fun _ => and_congr_right fun _ =>
    and_congr (Ideal.le_annihilator_ker_iff _ _) (Ideal.le_annihilator_coker_iff _ _)

/-! ### The comparison with the completed module -/

/-- The comparison isomorphism of Tag 087W intertwines the map of completed modules with
`Stacks.Algebraization.adicSystemLimitMap`. This is
`Stacks.Coherent.globalSectionsComparison_naturality` read on elements. -/
public theorem adicSystemLimitMap_comparison (Y : Scheme.{u}) [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (I : Ideal Γ(Y, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (x : Stacks.Coherent.completedModuleAsBase Y I F) :
    (adicSystemLimitMap f).hom
        ((Stacks.Coherent.globalSectionsComparison Y I F).toLinearEquiv x) =
      (Stacks.Coherent.globalSectionsComparison Y I G).toLinearEquiv
        ((completedModuleHomBase Y I f).hom x) :=
  (congrArg (fun k : Stacks.Coherent.completedModuleAsBase Y I F ⟶
      (limit (Stacks.Coherent.globalSectionsSystem G) : ModuleCat.{u} Γ(Y, ⊤)) => k.hom x)
    (Stacks.Coherent.globalSectionsComparison_naturality Y I f)).symm

/-! ### The module structures over the completed ring

`Stacks.Coherent.completedModuleAsBase` is a module over `Γ(Y, ⊤)` by construction, and its
structure as a finite module over the completion — the one Tag 087W produces — is reachable only
by unfolding the restriction of scalars. The three bridging instances of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine` restate it; they are declared
`local` there, so they are reactivated here. Together they are what makes
`Stacks.Coherent.finiteCompletionModule_isAdicComplete` applicable to a quotient of the completed
module. -/

attribute [local instance] Stacks.Algebraization.moduleCompletionCompletedModuleAsBase
  Stacks.Algebraization.finiteCompletedModuleAsBase
  Stacks.Algebraization.isScalarTowerCompletedModuleAsBase

/-! ### From the levelwise condition to the module condition -/

/-- **The cokernel half of Tag 0888 (1) ⟹ (2).** If one power of `𝓚` annihilates every levelwise
cokernel of a morphism of coherent adic systems, that power of `K` carries every element of the
target completed module into the image of the induced map.

The approximation `Stacks.Algebraization.completedModuleHom_exists_sub_mem` places `r • y` in the
image modulo every `I ⁿ⁺¹`, and the quotient of the target by that image is a finite module over
the completion, hence `I`-adically separated, so the class of `r • y` vanishes. -/
public theorem exists_apply_eq_smul_of_cokernel_eq_bot
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (I K : Ideal Γ(Y, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    {t : ℕ}
    (hcok : ∀ k : ℕ, idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop K) t
      (cokernel (C := Y.Modules) (f.hom.app (op k))) = ⊥)
    {r : Γ(Y, ⊤)} (hr : r ∈ K ^ t) (y : Stacks.Coherent.completedModuleAsBase Y I G) :
    ∃ x : Stacks.Coherent.completedModuleAsBase Y I F,
      (completedModuleHomBase Y I f).hom x = r • y := by
  let P := LinearMap.range (completedModuleMap Y I f)
  have : Module.Finite (AdicCompletion I Γ(Y, ⊤))
      (Stacks.Coherent.completedModuleAsBase Y I G ⧸ P) :=
    Module.Finite.of_surjective P.mkQ P.mkQ_surjective
  have hcomplete : IsAdicComplete I
      (Stacks.Coherent.completedModuleAsBase Y I G ⧸ P) :=
    Stacks.Coherent.finiteCompletionModule_isAdicComplete I I.fg_of_isNoetherianRing _
  have hq : ∀ z, (P.mkQ.restrictScalars Γ(Y, ⊤)) z = P.mkQ z := fun _ => rfl
  have hsmul : r • (P.mkQ y) = 0 := by
    refine eq_zero_of_mem_pow_succ_smul_top I fun k => ?_
    obtain ⟨x, hx⟩ := completedModuleHom_exists_sub_mem Y I K f hcok hr y k
    have hmem := Submodule.mem_map_of_mem (f := P.mkQ.restrictScalars Γ(Y, ⊤)) hx
    rw [Stacks.Coherent.map_smul_top_local (I ^ (k + 1)) (P.mkQ.restrictScalars Γ(Y, ⊤))
      P.mkQ_surjective] at hmem
    have hzero : P.mkQ ((completedModuleHomBase Y I f).hom x) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).2 (LinearMap.mem_range.2 ⟨x, rfl⟩)
    rwa [map_sub, map_smul, hq, hq, hzero, sub_zero] at hmem
  have hmk : P.mkQ (r • y) = 0 := by
    rwa [← hq, (P.mkQ.restrictScalars Γ(Y, ⊤)).map_smul, hq]
  exact LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero P).1 hmk)

/-! ### From annihilation on global sections to annihilation of the sheaves -/

/-- An ideal killing every element sent to zero by a linear map kills the kernel as a module. -/
private theorem smul_top_ker_eq_bot {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (J : Ideal A) (φ : M →ₗ[A] N)
    (h : ∀ r ∈ J, ∀ x : M, φ x = 0 → r • x = 0) :
    J • (⊤ : Submodule A ↥(LinearMap.ker φ)) = ⊥ :=
  (ideal_smul_top_eq_bot_iff _).2 fun r hr z => Subtype.ext (h r hr z.1 z.2)

/-- **Annihilation on global sections, at a fixed exponent.** On an affine scheme, if `K ^ n`
kills every global section of the source annihilated by `a` and carries every global section of
the target into the image of `a`, then `𝓚 ^ n` annihilates the sheaf kernel and the sheaf
cokernel of `a`.

This is the fixed-exponent form of
`Stacks.Algebraization.isPowerAnnihilated_kernel_cokernel_of_sections`, which the levelwise
condition of Tag 0888 needs because it demands one exponent valid at every index at once. -/
public theorem idealPowerMultiple_kernel_cokernel_eq_bot_of_sections {Y : Scheme.{u}} [IsAffine Y]
    (K : Ideal Γ(Y, ⊤)) (n : ℕ) {M N : Y.Modules} [M.IsCoherent] [N.IsCoherent] (a : M ⟶ N)
    (hker : ∀ r ∈ K ^ n, ∀ x : Γ(M, ⊤), a.app ⊤ x = 0 → r • x = 0)
    (hcok : ∀ r ∈ K ^ n, ∀ y : Γ(N, ⊤), ∃ x : Γ(M, ⊤), a.app ⊤ x = r • y) :
    idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop K) n
        (kernel (C := Y.Modules) a) = ⊥ ∧
      idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop K) n
        (cokernel (C := Y.Modules) a) = ⊥ := by
  let T : Y.Modules ⥤ ModuleCat Γ(Y, ⊤) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits Y.ringCatSheaf (op (⊤ : Y.Opens))
  have hMq : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  have hNq : N.IsQuasicoherent := isQuasicoherent_of_isCoherent N
  have hKcoh : (kernel (C := Y.Modules) a).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel a
  have hCcoh : (cokernel (C := Y.Modules) a).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel a
  have hKq : (kernel (C := Y.Modules) a).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have hCq : (cokernel (C := Y.Modules) a).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  constructor
  · have e : ModuleCat.of Γ(Y, ⊤) ↥(LinearMap.ker (T.map a).hom) ≅
        T.obj (kernel (C := Y.Modules) a) :=
      (ModuleCat.kernelIsoKer (T.map a)).symm ≪≫ (PreservesKernel.iso T a).symm
    exact Stacks.Coherent.affine_idealPowerMultiple_eq_bot K n (kernel (C := Y.Modules) a)
      (ideal_smul_top_eq_bot_of_linearEquiv (K ^ n) e.toLinearEquiv
        (smul_top_ker_eq_bot (K ^ n) (T.map a).hom hker))
  · refine Stacks.Coherent.affine_idealPowerMultiple_eq_bot K n (cokernel (C := Y.Modules) a) ?_
    rw [ideal_smul_top_eq_bot_iff]
    intro r hr y
    obtain ⟨z, hz⟩ := surjective_app_of_epi_of_isAffineOpen
      (cokernel.π (C := Y.Modules) a) ⟨⊤, isAffineOpen_top Y⟩ y
    obtain ⟨w, hw⟩ := hcok r hr z
    calc
      r • y = r • Scheme.Modules.Hom.app (cokernel.π (C := Y.Modules) a) ⊤ z :=
        congrArg (fun s => r • s) hz.symm
      _ = Scheme.Modules.Hom.app (cokernel.π (C := Y.Modules) a) ⊤ (r • z) :=
        (Scheme.Modules.Hom.app_smul _ r z).symm
      _ = Scheme.Modules.Hom.app (cokernel.π (C := Y.Modules) a) ⊤
            (Scheme.Modules.Hom.app a ⊤ w) :=
        congrArg (fun s => Scheme.Modules.Hom.app (cokernel.π (C := Y.Modules) a) ⊤ s) hw.symm
      _ = 0 := congrArg (fun k : M ⟶ cokernel (C := Y.Modules) a =>
        Scheme.Modules.Hom.app k ⊤ w) (cokernel.condition (C := Y.Modules) a)

/-! ### From the module condition to the levelwise condition -/

/-- **The commutative-algebra fact of Tag 0888, applied to `α_Y`.** If `K ^ t` annihilates the
kernel and the cokernel of the map `φ` of completed modules, then for `f, g ∈ K ^ t` the canonical
map `"fg"` of `Ideal.existsUnique_canonicalMap_of_smul_eq_bot` has both composites with `φ` equal
to multiplication by `f * g`. -/
public theorem exists_canonicalMap_completedModule
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (I K : Ideal Γ(Y, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    {t : ℕ}
    (hker : ∀ r ∈ K ^ t, ∀ x : Stacks.Coherent.completedModuleAsBase Y I F,
      (completedModuleHomBase Y I f).hom x = 0 → r • x = 0)
    (hcok : ∀ r ∈ K ^ t, ∀ y : Stacks.Coherent.completedModuleAsBase Y I G,
      ∃ x : Stacks.Coherent.completedModuleAsBase Y I F,
        (completedModuleHomBase Y I f).hom x = r • y)
    {c d : Γ(Y, ⊤)} (hc : c ∈ K ^ t) (hd : d ∈ K ^ t) :
    ∃ b : Stacks.Coherent.completedModuleAsBase Y I G →ₗ[Γ(Y, ⊤)]
        Stacks.Coherent.completedModuleAsBase Y I F,
      (∀ y, (completedModuleHomBase Y I f).hom (b y) = (c * d) • y) ∧
        ∀ x, b ((completedModuleHomBase Y I f).hom x) = (c * d) • x := by
  set φ := (completedModuleHomBase Y I f).hom
  have hT := smul_top_ker_eq_bot (K ^ t) φ hker
  have hQ : K ^ t • (⊤ : Submodule Γ(Y, ⊤)
      (Stacks.Coherent.completedModuleAsBase Y I G ⧸ LinearMap.range φ)) = ⊥ :=
    (ideal_smul_top_eq_bot_iff _).2 fun r hr =>
      Module.mem_annihilator.mp ((Ideal.le_annihilator_coker_iff _ φ).2 hcok hr)
  obtain ⟨b, ⟨hb1, hb2⟩, -⟩ := Ideal.existsUnique_canonicalMap_of_smul_eq_bot
    (LinearMap.ker φ).subtype φ (LinearMap.range φ).mkQ
    (LinearMap.exact_subtype_ker_map φ) (LinearMap.exact_map_mkQ_range φ)
    (K ^ t) hT hQ hc hd
  refine ⟨b, fun y => ?_, fun x => LinearMap.congr_fun hb2 x⟩
  obtain ⟨x, hx⟩ := hcok c hc y
  rw [hb1 y x hx, map_smul, hx, smul_smul, mul_comm d c]

/-- **Tag 0888 (2) ⟹ (1), on global sections.** If `K ^ t` annihilates the kernel and the
cokernel of `α_Y`, then `K ^ (2t)` annihilates the kernel and the cokernel of every map of global
sections `Γ(α_k)`.

The projections of the completed module onto the terms are surjective with kernel the `(k+1)`-st
ideal-power multiple, and the canonical map `"fg"` preserves that multiple, so it descends to the
`k`-th term. -/
public theorem sections_kernel_cokernel_annihilated_of_module
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (I K : Ideal Γ(Y, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    {t : ℕ}
    (hker : ∀ r ∈ K ^ t, ∀ x : Stacks.Coherent.completedModuleAsBase Y I F,
      (completedModuleHomBase Y I f).hom x = 0 → r • x = 0)
    (hcok : ∀ r ∈ K ^ t, ∀ y : Stacks.Coherent.completedModuleAsBase Y I G,
      ∃ x : Stacks.Coherent.completedModuleAsBase Y I F,
        (completedModuleHomBase Y I f).hom x = r • y) (k : ℕ) :
    (∀ r ∈ K ^ (2 * t), ∀ x : Γ(F.obj.obj (op k), ⊤),
        (f.hom.app (op k)).app ⊤ x = 0 → r • x = 0) ∧
      ∀ r ∈ K ^ (2 * t), ∀ y : Γ(G.obj.obj (op k), ⊤),
        ∃ x : Γ(F.obj.obj (op k), ⊤), (f.hom.app (op k)).app ⊤ x = r • y := by
  have key : ∀ c ∈ K ^ t, ∀ d ∈ K ^ t,
      (∀ x : Γ(F.obj.obj (op k), ⊤), (f.hom.app (op k)).app ⊤ x = 0 → (c * d) • x = 0) ∧
        ∀ y : Γ(G.obj.obj (op k), ⊤), ∃ x : Γ(F.obj.obj (op k), ⊤),
          (f.hom.app (op k)).app ⊤ x = (c * d) • y := by
    intro c hc d hd
    obtain ⟨b, hb1, hb2⟩ := exists_canonicalMap_completedModule Y I K f hker hcok hc hd
    constructor
    · intro x hx
      obtain ⟨m, hm⟩ := Stacks.Coherent.affineLevelProjection_surjective Y I F k x
      have hphi : (Stacks.Coherent.affineLevelProjection Y I G k).hom
          ((completedModuleHomBase Y I f).hom m) = 0 := by
        rwa [affineLevelProjection_completedModuleHomBase Y I f k m, hm]
      have hmemN : (completedModuleHomBase Y I f).hom m ∈ I ^ (k + 1) • (⊤ : Submodule Γ(Y, ⊤)
          (Stacks.Coherent.completedModuleAsBase Y I G)) := by
        rw [← Stacks.Coherent.affineLevelProjection_ker Y I G k]
        exact LinearMap.mem_ker.2 hphi
      have hmemM : (c * d) • m ∈ I ^ (k + 1) • (⊤ : Submodule Γ(Y, ⊤)
          (Stacks.Coherent.completedModuleAsBase Y I F)) := by
        rw [← hb2 m]
        exact Submodule.mem_comap.mp
          (Submodule.smul_top_le_comap_smul_top (I ^ (k + 1)) b hmemN)
      rw [← Stacks.Coherent.affineLevelProjection_ker Y I F k] at hmemM
      have hz := LinearMap.mem_ker.mp hmemM
      rwa [map_smul, hm] at hz
    · intro y
      obtain ⟨n, hn⟩ := Stacks.Coherent.affineLevelProjection_surjective Y I G k y
      refine ⟨(Stacks.Coherent.affineLevelProjection Y I F k).hom (b n), ?_⟩
      have h1 := affineLevelProjection_completedModuleHomBase Y I f k (b n)
      rw [hb1 n, map_smul, hn] at h1
      exact h1.symm
  rw [two_mul, pow_add]
  refine ⟨fun r hr x hx => ?_, fun r hr y => ?_⟩
  · refine Submodule.mul_induction_on hr (fun c hc d hd => (key c hc d hd).1 x hx) ?_
    intro p q hp hq
    rw [add_smul, hp, hq, add_zero]
  · refine Submodule.mul_induction_on hr (fun c hc d hd => (key c hc d hd).2 y) ?_
    rintro p q ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂, add_smul]⟩

/-! ### The equivalence -/

/-- **Tag 0888 (2), transported across the comparison of Tag 087W.** The module condition, which
is stated on the inverse limit of the systems of global sections, is the elementwise annihilation
condition on the map of completed modules. -/
public theorem isAffineKernelCokernelAnnihilated_iff_completedModule
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (I K : Ideal Γ(Y, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G) :
    IsAffineKernelCokernelAnnihilated K f ↔
      ∃ t : ℕ, 0 < t ∧
        (∀ r ∈ K ^ t, ∀ x : Stacks.Coherent.completedModuleAsBase Y I F,
            (completedModuleHomBase Y I f).hom x = 0 → r • x = 0) ∧
          ∀ r ∈ K ^ t, ∀ y : Stacks.Coherent.completedModuleAsBase Y I G,
            ∃ x : Stacks.Coherent.completedModuleAsBase Y I F,
              (completedModuleHomBase Y I f).hom x = r • y := by
  rw [isAffineKernelCokernelAnnihilated_iff]
  exact exists_congr fun t => and_congr_right fun _ => and_congr
    (Ideal.kernel_annihilation_congr
      (Stacks.Coherent.globalSectionsComparison Y I F).toLinearEquiv
      (Stacks.Coherent.globalSectionsComparison Y I G).toLinearEquiv
      (completedModuleHomBase Y I f).hom (adicSystemLimitMap f).hom
      (adicSystemLimitMap_comparison Y I f) (K ^ t))
    (Ideal.cokernel_annihilation_congr
      (Stacks.Coherent.globalSectionsComparison Y I F).toLinearEquiv
      (Stacks.Coherent.globalSectionsComparison Y I G).toLinearEquiv
      (completedModuleHomBase Y I f).hom (adicSystemLimitMap f).hom
      (adicSystemLimitMap_comparison Y I f) (K ^ t))

/-- **Tag 0888, (1) ⟹ (2) on an affine scheme.** -/
public theorem isAffineKernelCokernelAnnihilated_of_levelwise
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (I K : Ideal Γ(Y, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (h : IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop K) f.hom) :
    IsAffineKernelCokernelAnnihilated K f := by
  obtain ⟨t, ht, hkc⟩ := h
  exact (isAffineKernelCokernelAnnihilated_iff_completedModule Y I K f).2
    ⟨t, ht, fun _ hr x hx => completedModuleHom_smul_eq_zero_of_apply_eq_zero Y I K f
        (fun j => (hkc j).1) hr x hx,
      fun _ hr y => exists_apply_eq_smul_of_cokernel_eq_bot Y I K f (fun j => (hkc j).2) hr y⟩

/-- **Tag 0888, (2) ⟹ (1) on an affine scheme.** -/
public theorem isKernelCokernelAnnihilatedByPower_of_affine
    (Y : Scheme.{u}) [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (I K : Ideal Γ(Y, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (h : IsAffineKernelCokernelAnnihilated K f) :
    IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop K) f.hom := by
  obtain ⟨t, ht, hker, hcok⟩ :=
    (isAffineKernelCokernelAnnihilated_iff_completedModule Y I K f).1 h
  refine ⟨2 * t, by omega, fun k => ?_⟩
  have hFc : (F.obj.obj (op k)).IsCoherent := F.property.1 k
  have hGc : (G.obj.obj (op k)).IsCoherent := G.property.1 k
  obtain ⟨h1, h2⟩ := sections_kernel_cokernel_annihilated_of_module Y I K f hker hcok k
  exact idealPowerMultiple_kernel_cokernel_eq_bot_of_sections K (2 * t)
    (f.hom.app (op k)) h1 h2

/-- **Stacks Project, Tag 0888, conditions (1) and (2) on an affine scheme.** For a morphism `α`
of `Coh(Y, 𝓘)` on an affine Noetherian scheme `Y` the following are equivalent: one positive power
of `𝓚` annihilates every levelwise kernel `Ker(α_n)` and every levelwise cokernel `Coker(α_n)`;
and one positive power of `K = 𝓚(⊤)` annihilates the kernel and the cokernel of the map
`α_Y : M → N` of finite modules over the completion which Tag 087W attaches to `α`.

Both ideal sheaves on an affine scheme are attached to ideals of `Γ(Y, ⊤)`, by
`AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`, so the statement may be reduced to that
presentation. -/
@[stacks 0888 "equivalence of (1) and (2) on an affine scheme"]
public theorem isKernelCokernelAnnihilatedByPower_iff_affine {Y : Scheme.{u}} [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (ℐ 𝒦 : Y.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems ℐ} (f : F ⟶ G) :
    IsKernelCokernelAnnihilatedByPower 𝒦 f.hom ↔
      IsAffineKernelCokernelAnnihilated (𝒦.ideal ⟨⊤, isAffineOpen_top Y⟩) f := by
  obtain ⟨I, rfl⟩ : ∃ I : Ideal Γ(Y, ⊤), ℐ = Scheme.IdealSheafData.ofIdealTop I :=
    ⟨_, (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply ℐ).symm⟩
  obtain ⟨K, rfl⟩ : ∃ K : Ideal Γ(Y, ⊤), 𝒦 = Scheme.IdealSheafData.ofIdealTop K :=
    ⟨_, (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply 𝒦).symm⟩
  rw [Stacks.Coherent.ofIdealTop_ideal_top]
  exact ⟨isAffineKernelCokernelAnnihilated_of_levelwise Y I K f,
    isKernelCokernelAnnihilatedByPower_of_affine Y I K f⟩

end Stacks.Algebraization

end
