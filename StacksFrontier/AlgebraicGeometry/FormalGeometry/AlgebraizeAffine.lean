module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineToolbox
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.LimitSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleDescent
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Algebraizing a map into a completion on an affine scheme

Let `X` be an affine Noetherian scheme, `I ⊆ Γ(X, ⊤)` an ideal and `𝓘` the quasi-coherent ideal
sheaf it determines. Let `G` be a coherent `𝒪_X`-module and `(F_n)` a coherent adic system along
`𝓘`. This file carries out the affine case of Stacks 0889 part (1): a morphism
`α : (F_n) ⟶ G^∧` into the completion of `G` whose levelwise kernels and cokernels are annihilated
by one power of `𝓘` is the completion of a morphism `a : F ⟶ G` of coherent modules whose kernel
and cokernel are annihilated by a power of `𝓘`, and `a` is unique up to a unique isomorphism.

The statement is reached in two stages. At the level of modules, `α` comes from a map
`ψ : M₀ → Γ(G, ⊤)` of finite `Γ(X, ⊤)`-modules with ideal-power torsion kernel and cokernel,
together with an identification of the completed module of `(F_n)` with the extension of scalars of
`M₀` which is compatible with `α`. At the level of sheaves, `ψ` is realized by a morphism of
coherent modules because global sections are an equivalence onto the finite modules over
`Γ(X, ⊤)`, and the identification is turned into an isomorphism of coherent adic systems by the
equivalence of tag 087W.

The argument is the one of the source. Tag 087W identifies `Coh(X, 𝓘)` with the finite modules
over the `I`-adic completion `A^∧` of `A = Γ(X, ⊤)`, through the inverse limit of global sections,
and tag 0880 identifies the module attached to `G^∧` with the `I`-adic completion of `Γ(G, ⊤)`,
hence with `A^∧ ⊗_A Γ(G, ⊤)`. So `α` becomes an `A^∧`-linear map `φ : M' → A^∧ ⊗_A Γ(G, ⊤)` of
finite `A^∧`-modules, and the hypothesis on `α` becomes that the kernel and cokernel of `φ` are
`I A^∧`-power torsion. Formal glueing, in the form of
`AdicCompletion.exists_finite_descent_of_isIPowerTorsion`, descends such a `φ` to a map of finite
`A`-modules.

Translating the hypothesis is the step which is not a transport, and it is the main content here.
The condition of tag 0888 is *levelwise*: each `Ker(α_k)` and each `Coker(α_k)` is killed by
`𝓘 ^ t`. Over an affine scheme, evaluation at `⊤` is exact on quasi-coherent modules, so this says
that `I ^ t` kills the kernel and the cokernel of each map of global sections `Γ(α_k)`. The
projections of `M'` onto the terms `Γ(F_k, ⊤)` are surjective with kernel `I ^ (k+1) M'`, so
`I ^ t · Ker(φ)` lies in every `I ^ (k+1) M'` and `I ^ t · Coker(φ)` in every
`I ^ (k+1) Coker(φ)`; both modules are finite over the complete ring `A^∧`, hence `I`-adically
Hausdorff, so both intersections vanish. No derived limit and no abelian structure on
`Coh(X, 𝓘)` is used: the hypothesis is consumed exactly in the levelwise form in which tag 0888
states it.

## Main definitions

* `Stacks.Algebraization.completedFGModule`, `Stacks.Algebraization.completedModuleHom` and
  `Stacks.Algebraization.completedModuleMap` — the finite module over the completion which tag
  087W attaches to a coherent adic system, and the map attached to a morphism of such, in the two
  spellings of its linearity.
* `Stacks.Algebraization.completionSectionsLimitEquiv` and
  `Stacks.Algebraization.completionModuleEquiv` — the module attached to the completion of a
  coherent module, identified with the `I`-adic completion of its global sections; the
  companion `Stacks.Algebraization.completionModuleEquivₛ` is the same identification read over
  the completed ring.
* `Stacks.Algebraization.adicCompletionCongrIdeal` — the comparison of the adic completions along
  an equality of ideals.
* `Stacks.Algebraization.sectionsEvaluationEquiv` and
  `Stacks.Algebraization.evaluationForgetEquiv` — the three spellings of the sections of an
  `𝒪_X`-module over an open, identified with one another.
* `Stacks.Algebraization.evaluationOfTopSectionsMap` — a map of global sections read as a
  morphism between the values of the evaluation functor, the inverse of
  `Stacks.Algebraization.topSectionsMap` on underlying maps.
* `Stacks.Algebraization.affineSectionsHomLift` — the morphism of quasi-coherent modules on an
  affine scheme which a map of global sections induces.

## Main results

* `Stacks.Algebraization.smul_eq_zero_of_app_eq_zero` and
  `Stacks.Algebraization.smul_mem_range_of_cokernel_eq_bot` — the affine-sections form of
  annihilation of the kernel and of the cokernel of a morphism of `𝒪_X`-modules.
* `Stacks.Algebraization.completedModuleMap_isIPowerTorsion_ker` and
  `Stacks.Algebraization.completedModuleMap_isIPowerTorsion_cokernel` — **the affine translation
  of the condition of tag 0888 (1)**: the kernel and cokernel of the induced map of completed
  modules are `I A^∧`-power torsion.
* `Stacks.Algebraization.completionModuleEquiv_naturality` — the identification of the completed
  module of a completion with an adic completion is natural in the coherent module.
* `Stacks.Algebraization.isPowerAnnihilated_kernel_cokernel_of_sections` — conversely,
  annihilation on global sections gives annihilation of the sheaf kernel and the sheaf cokernel of
  a morphism of coherent modules, which is the form of the conclusion of tag 0889.
* `Stacks.Algebraization.affine_exists_module_algebraization` — **the affine case of Stacks 0889
  (1), at the level of modules**: the descended map `ψ`, its ideal-power torsion kernel and
  cokernel, the identification of the completed module of `(F_n)` with the extension of scalars of
  the source of `ψ`, and the compatibility of that identification with `α`.
* `Stacks.Algebraization.sectionsEvaluationEquiv_naturality`,
  `Stacks.Algebraization.topSectionsMap_eq_evaluation_map` and
  `Stacks.Algebraization.affineSectionsHomLift_app` — the identifications of the spellings of the
  sections are natural, and the lift of a map of global sections acts on sections by that map.
* `Stacks.Algebraization.isIPowerTorsion_ker_affineSectionMap` and
  `Stacks.Algebraization.isIPowerTorsion_cokernel_affineSectionMap` — annihilation of the sheaf
  kernel and the sheaf cokernel of a morphism by a power of an ideal sheaf gives ideal-power
  torsion of the kernel and the cokernel of the morphism on the sections over each affine open.
* `Stacks.Algebraization.exists_coherent_realization` — a map of finite `Γ(X, ⊤)`-modules with
  ideal-power torsion kernel and cokernel is the map of global sections of a morphism of coherent
  modules whose kernel and cokernel are annihilated by a power of `𝓘`.
* `Stacks.Algebraization.tensorProduct_linearMap_ext` — two linear maps out of an extension of
  scalars agreeing on the elements `1 ⊗ m` are equal.
* `Stacks.Algebraization.affine_exists_algebraization` — **the affine case of Stacks 0889 (1)**:
  the coherent module `F`, the morphism `a : F ⟶ G` with kernel and cokernel annihilated by a
  power of `𝓘`, and the isomorphism of `(F_n)` with the completion of `F` through which `α` is the
  completion of `a`.
* `Stacks.Algebraization.unique_algebraization_of_isPowerAnnihilated` and
  `Stacks.Algebraization.affine_unique_algebraization` — **the uniqueness clause of Stacks 0889
  (1)**: two such algebraizations are related by a unique isomorphism compatible with the maps to
  `G` and with the two identifications of the formal system.

## Implementation notes

The conclusion that is proved about a map `a` of coherent modules is annihilation of the kernel
and the cokernel of `a` itself, formed in the abelian category `X.Modules`, which is what the
source asserts. It is *not* the levelwise condition `IsKernelCokernelAnnihilatedByPower` applied
to the completion of `a`: the cokernel half of that would follow, but the kernel half is the
Artin–Rees comparison of `ψ ⁻¹ (I ^ k N)` with `I ^ k M + Ker ψ`, which is a separate statement.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances. Every categorical construction below is
therefore given its category explicitly as `(C := X.Modules)`, the coherence of a kernel or a
cokernel is supplied by name rather than by instance search, the bridging `local instance`s for
the module structure on sections are reactivated from
`Stacks.Algebraization.CompletionFunctor.AffineSections`, and the steps that would naturally be
`rw` are `congrArg` chains or `exact`, since a rewrite motive mixing the two presentations is not
type-correct at the transparency `rw` builds it at.

The sections of a module over an open occur in three spellings: `Γ(M, U)`, the value of
`AlgebraicGeometry.SheafOfModules.evaluation`, and the value of the underlying presheaf of modules.
They have the same underlying type and the same scalar action, but
`AlgebraicGeometry.Scheme.Modules.presheaf` and `AlgebraicGeometry.SheafOfModules.evaluation` stand
between them. Rather than relax the transparency of `isDefEq`, the identifications are named:
`Stacks.Algebraization.sectionsEvaluationEquiv` and
`Stacks.Algebraization.evaluationForgetEquiv` are the identity on elements, their naturality is
recorded, and the bridging module instances restate at each spelling the instance Mathlib declares
at the other. A statement whose instances are resolved with the module arguments free then
instantiates at a concrete module without any further instance search, which is what makes the
annihilation hypotheses of `Stacks.Algebraization.isPowerAnnihilated_kernel_cokernel_of_sections`
usable at a module as syntactically involved as `M₀ ~`; this is the role of
`Stacks.Algebraization.smul_top_evaluationKernel_eq_bot`.

The completed module of a coherent adic system is `Stacks.Coherent.completedModuleAsBase`, a
module over `Γ(X, ⊤)`; its action by the completed ring, its finiteness over the completed ring
and the compatibility of the two actions are supplied as `local instance`s, which is what makes
`Stacks.Coherent.finiteCompletionModule_isAdicComplete` applicable to it and hence what makes it
`I`-adically Hausdorff.

The identification of the module attached to `G^∧` with `AdicCompletion I Γ(G, ⊤)` is
`AdicCompletion.quotientSystemLimitEquiv` applied to the system of global sections of `G^∧`: its
terms are the module quotients `Γ(G, ⊤) / I ^ (n+1) Γ(G, ⊤)` by
`Stacks.Algebraization.completionQuotientSectionsEquiv`, compatibly with the transitions. The
ideal appearing there is `𝓘(⊤)` rather than `I`; the two are equal by
`Stacks.Coherent.ofIdealTop_ideal_top`, and the equality is moved across by substituting it in a
reflexivity equivalence rather than by rewriting inside a dependent type. Its naturality is proved
through `Stacks.Algebraization.linearMap_eq_of_comp_of`: two maps out of an adic completion into a
Hausdorff module agree as soon as they agree on the image of the canonical map, which replaces a
chase through the inverse limit by a computation on the canonical projections.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] Stacks.Coherent.isLocallyNoetherian_of_isNoetherianRing_top

/-! ### Bridging instances across the two presentations of the category of modules

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, so the module
structure on sections declared at one presentation is not found at the other. The bridging
`local instance`s of `Stacks.Algebraization.CompletionFunctor.AffineSections` are reactivated
rather than restated. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal


/-! ### Transporting ideal-power torsion -/

/-- Ideal-power torsion is invariant under a linear equivalence. -/
public theorem isIPowerTorsion_of_linearEquiv {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N) (hM : IsIPowerTorsion R M J) :
    IsIPowerTorsion R N J := fun x => by
  obtain ⟨n, hn, hx⟩ := hM (e.symm x)
  refine ⟨n, hn, fun a ha => ?_⟩
  calc
    a • x = e (a • e.symm x) := by simp
    _ = e 0 := by rw [hx a ha]
    _ = 0 := map_zero e

/-- A module annihilated by `J ^ n` over the base ring is `J S`-power torsion over an extension
`S` of the base: the annihilator of the module contains the extension of `J ^ n`. -/
public theorem isIPowerTorsion_of_smul_top_eq_bot
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (J : Ideal R) (n : ℕ) (h : J ^ n • (⊤ : Submodule R M) = ⊥) :
    IsIPowerTorsion S M (J.map (algebraMap R S)) := by
  intro x
  have hkill := (ideal_smul_top_eq_bot_iff (J ^ n)).1 h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hx : x = 0 := by simpa using hkill 1 (by simp [hn]) x
    exact ⟨1, Nat.one_pos, fun a _ => by simp [hx]⟩
  refine ⟨n, hn, fun a ha => ?_⟩
  have hle : Ideal.map (algebraMap R S) (J ^ n) ≤ Module.annihilator S M :=
    Ideal.map_le_iff_le_comap.mpr fun r hr => by
      rw [Ideal.mem_comap, Module.mem_annihilator]
      intro y
      rw [IsScalarTower.algebraMap_smul S r y]
      exact hkill r hr y
  exact Module.mem_annihilator.mp (hle (by simpa only [Ideal.map_pow] using ha)) x

/-! ### Kernels and cokernels on the global sections of an affine scheme -/

/-- The projection to the cokernel kills the image of a section of the source. -/
private theorem cokernel_π_app_comp_app {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (x : Γ(M, U)) : (cokernel.π (C := X.Modules) f).app U (f.app U x) = 0 :=
  congrArg (fun g : M ⟶ cokernel (C := X.Modules) f => g.app U x)
    (cokernel.condition (C := X.Modules) f)

/-- A section killed by a morphism of `𝒪_X`-modules comes from a section of the kernel:
evaluation at an open preserves finite limits and zero morphisms, so it carries the exact
sequence `Ker f → M → N` to an exact sequence of modules. -/
public theorem exists_kernel_section {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (x : Γ(M, U)) (hx : f.app U x = 0) :
    ∃ y : Γ(kernel (C := X.Modules) f, U), (kernel.ι (C := X.Modules) f).app U y = x := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  exact (ShortComplex.moduleCat_exact_iff _).mp
    ((ShortComplex.exact_kernel (C := X.Modules) f).map_of_mono_of_preservesKernel T
      inferInstance inferInstance) x hx

/-- **Evaluation at an affine open is exact on quasi-coherent modules.** A section of the target
which dies in the cokernel is in the image: the morphism factors through its image by an
epimorphism, which is surjective on the sections over an affine open. -/
public theorem affine_sections_cokernel_exact {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (U : X.affineOpens) :
    Function.Exact (f.app U.1) ((cokernel.π (C := X.Modules) f).app U.1) := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U.1) := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U.1)
  have him : (Abelian.image (C := X.Modules) f).IsQuasicoherent := by
    dsimp [Abelian.image]
    infer_instance
  have hs := surjective_app_of_epi_of_isAffineOpen
    (Abelian.factorThruImage (C := X.Modules) f) U
  have hex := (ShortComplex.exact_kernel (C := X.Modules)
    (cokernel.π (C := X.Modules) f)).map_of_mono_of_preservesKernel T inferInstance inferInstance
  have hh := (ShortComplex.moduleCat_exact_iff _).mp hex
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := hh y hy
    obtain ⟨x, hx⟩ := hs z
    refine ⟨x, ?_⟩
    have he := congrArg (fun g : M ⟶ N => g.app U.1 x) (Abelian.image.fac (C := X.Modules) f)
    exact he.symm.trans
      ((congrArg (fun z => (kernel.ι (C := X.Modules)
        (cokernel.π (C := X.Modules) f)).app U.1 z) hx).trans hz)
  · rintro ⟨x, rfl⟩
    exact cokernel_π_app_comp_app f U.1 x

/-- If `𝓘 ^ t` annihilates a module `M` on an affine scheme, then `I ^ t` kills its global
sections. -/
private theorem smul_eq_zero_of_idealPowerMultiple_eq_bot_top {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) {t : ℕ} {M : X.Modules}
    (hM : idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop I) t M = ⊥)
    {r : Γ(X, ⊤)} (hr : r ∈ I ^ t) (y : Γ(M, ⊤)) : r • y = 0 := by
  refine affine_sections_annihilated_of_idealPowerMultiple_eq_bot hM ⟨⊤, isAffineOpen_top X⟩ ?_ y
  rwa [Stacks.Coherent.ofIdealTop_ideal_top X I]

/-- If `𝓘 ^ t` annihilates the kernel of a morphism `f` of `𝒪_X`-modules on an affine scheme,
then `I ^ t` kills every global section of the source which `f` sends to zero. -/
public theorem smul_eq_zero_of_app_eq_zero {X : Scheme.{u}} [IsAffine X] (I : Ideal Γ(X, ⊤))
    {t : ℕ} {M N : X.Modules} (f : M ⟶ N)
    (hker : idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop I) t
      (kernel (C := X.Modules) f) = ⊥)
    {r : Γ(X, ⊤)} (hr : r ∈ I ^ t) (x : Γ(M, ⊤)) (hx : f.app ⊤ x = 0) : r • x = 0 := by
  obtain ⟨y, hy⟩ := exists_kernel_section f ⊤ x hx
  rw [← hy, ← Scheme.Modules.Hom.app_smul, smul_eq_zero_of_idealPowerMultiple_eq_bot_top I hker hr,
    map_zero]

/-- If `𝓘 ^ t` annihilates the cokernel of a morphism `f` of quasi-coherent modules on an affine
scheme, then `I ^ t` carries every global section of the target into the image of `f`. -/
public theorem smul_mem_range_of_cokernel_eq_bot {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) {t : ℕ} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hcok : idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop I) t
      (cokernel (C := X.Modules) f) = ⊥)
    {r : Γ(X, ⊤)} (hr : r ∈ I ^ t) (y : Γ(N, ⊤)) :
    ∃ x : Γ(M, ⊤), f.app ⊤ x = r • y := by
  have hzero : (cokernel.π (C := X.Modules) f).app ⊤ (r • y) = 0 := by
    rw [Scheme.Modules.Hom.app_smul]
    exact smul_eq_zero_of_idealPowerMultiple_eq_bot_top I hcok hr _
  exact (affine_sections_cokernel_exact f ⟨⊤, isAffineOpen_top X⟩ (r • y)).mp hzero

/-- An element of an `J`-adically Hausdorff module lying in every positive ideal-power multiple is
zero: the exponent `0` contributes nothing, so the hypothesis is the vanishing of the
intersection. -/
public theorem eq_zero_of_mem_pow_succ_smul_top {R : Type*} [CommRing R] (J : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] [IsHausdorff J M] {x : M}
    (hx : ∀ k : ℕ, x ∈ J ^ (k + 1) • (⊤ : Submodule R M)) : x = 0 := by
  have hmem : x ∈ (⨅ n : ℕ, J ^ n • (⊤ : Submodule R M)) := by
    refine Submodule.mem_iInf _ |>.2 fun n => ?_
    cases n with
    | zero => simp
    | succ k => exact hx k
  simpa using (IsHausdorff.iInf_pow_smul (inferInstance : IsHausdorff J M)).le hmem

/-! ### The completed module of a coherent adic system -/

/-- **Stacks 087W.** The finite module over the `I`-adic completion of `Γ(X, ⊤)` which the
equivalence of Stacks 087W attaches to a coherent adic system. -/
public noncomputable abbrev completedFGModule
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    FGModuleCat.{u} (AdicCompletion I Γ(X, ⊤)) :=
  (Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I).functor.obj F

/-- **Stacks 087W.** The map of completed modules attached to a morphism of coherent adic
systems. -/
public noncomputable abbrev completedModuleHom
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G) :
    (completedFGModule X I F).obj ⟶ (completedFGModule X I G).obj :=
  ((Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I).functor.map f).hom

/-- The same map of completed modules, read as a map of modules over `Γ(X, ⊤)`. This is the
spelling the projections onto the terms of the system are stated at. -/
public noncomputable abbrev completedModuleHomBase
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G) :
    Stacks.Coherent.completedModuleAsBase X I F ⟶
      Stacks.Coherent.completedModuleAsBase X I G :=
  (ModuleCat.restrictScalars (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))).map
    ((Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I).functor.map f).hom

/-- Restricting scalars changes neither the underlying map of the completed modules nor its
values. -/
public theorem completedModuleHomBase_apply
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (x : Stacks.Coherent.completedModuleAsBase X I F) :
    (completedModuleHomBase X I f).hom x = (completedModuleHom X I f).hom x := rfl

/-- The action of the completed ring on the completed module of a coherent adic system, at the
spelling `Stacks.Coherent.completedModuleAsBase` of that module. -/
local instance moduleCompletionCompletedModuleAsBase
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    Module (AdicCompletion I Γ(X, ⊤)) (Stacks.Coherent.completedModuleAsBase X I F) :=
  inferInstanceAs (Module (AdicCompletion I Γ(X, ⊤)) (completedFGModule X I F).obj)

/-- The completed module of a coherent adic system is finite over the completed ring. -/
local instance finiteCompletedModuleAsBase
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    Module.Finite (AdicCompletion I Γ(X, ⊤)) (Stacks.Coherent.completedModuleAsBase X I F) :=
  (completedFGModule X I F).property

/-- The two actions on the completed module of a coherent adic system agree through the
structure map of the completion. -/
local instance isScalarTowerCompletedModuleAsBase
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    IsScalarTower Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤))
      (Stacks.Coherent.completedModuleAsBase X I F) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The completed module of a coherent adic system is `I`-adically complete: it is a finite module
over the `I`-adic completion of `Γ(X, ⊤)`. -/
public theorem isAdicComplete_completedModuleAsBase
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) :
    IsAdicComplete I (Stacks.Coherent.completedModuleAsBase X I F) :=
  Stacks.Coherent.finiteCompletionModule_isAdicComplete I I.fg_of_isNoetherianRing _

/-- Evaluating a morphism of `𝒪_X`-modules at `⊤` is the same whether it is read through the
evaluation functor on sheaves of modules or through the action on sections. -/
public theorem evaluation_map_hom_apply {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N)
    (x : Γ(M, ⊤)) :
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map g).hom x = g.app ⊤ x := rfl

/-- The projections onto the terms of the system intertwine the map of completed modules with the
corresponding maps of global sections. -/
public theorem affineLevelProjection_completedModuleHomBase
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (n : ℕ) (x : Stacks.Coherent.completedModuleAsBase X I F) :
    (Stacks.Coherent.affineLevelProjection X I G n).hom ((completedModuleHomBase X I f).hom x) =
      (f.hom.app (op n)).app ⊤
        ((Stacks.Coherent.affineLevelProjection X I F n).hom x) := by
  have h := congrArg (fun k : Stacks.Coherent.completedModuleAsBase X I F ⟶
      (Stacks.Coherent.globalSectionsSystem G).obj (op n) => k.hom x)
    (Stacks.Coherent.affineLevelProjection_naturality X I f n)
  exact h

/-! ### The affine translation of the condition of Stacks 0888 (1) -/

/-- An element of the completed module of a coherent adic system whose projection onto the `k`-th
term vanishes lies in the `(k+1)`-st power multiple. -/
private theorem mem_pow_succ_smul_top_of_affineLevelProjection_eq_zero
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)) (k : ℕ)
    {z : Stacks.Coherent.completedModuleAsBase X I F}
    (h : (Stacks.Coherent.affineLevelProjection X I F k).hom z = 0) :
    z ∈ I ^ (k + 1) • (⊤ : Submodule Γ(X, ⊤) (Stacks.Coherent.completedModuleAsBase X I F)) := by
  rw [← Stacks.Coherent.affineLevelProjection_ker X I F k]
  exact LinearMap.mem_ker.2 h

/-- **The kernel half.** If one power of `𝓚` annihilates every levelwise kernel of a morphism of
coherent adic systems, the same power of `K` kills every element of the kernel of the induced map
of completed modules: such an element projects into the kernel of each map of global sections, so
after multiplication it lies in every `I ^ (k+1)` multiple of the completed module, which is
`I`-adically Hausdorff.

The annihilating ideal `K` is unrelated to the adic ideal `I` of the system: completeness is used
along `I` only, and `K` enters solely through the annihilation hypothesis. -/
public theorem completedModuleHom_smul_eq_zero_of_apply_eq_zero
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I K : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    {t : ℕ}
    (hker : ∀ k : ℕ, idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop K) t
      (kernel (C := X.Modules) (f.hom.app (op k))) = ⊥)
    {r : Γ(X, ⊤)} (hr : r ∈ K ^ t) (x : Stacks.Coherent.completedModuleAsBase X I F)
    (hx : (completedModuleHomBase X I f).hom x = 0) : r • x = 0 := by
  have hcomplete := isAdicComplete_completedModuleAsBase X I F
  refine eq_zero_of_mem_pow_succ_smul_top I fun k =>
    mem_pow_succ_smul_top_of_affineLevelProjection_eq_zero X I F k ?_
  rw [map_smul]
  refine smul_eq_zero_of_app_eq_zero K (f.hom.app (op k)) (hker k) hr _ ?_
  rw [← affineLevelProjection_completedModuleHomBase X I f k x, hx]
  exact map_zero _

/-- **The cokernel half.** If one power of `𝓚` annihilates every levelwise cokernel of a morphism
of coherent adic systems, then after multiplication by that power of `K` every element of the
target completed module lies in the image of the induced map up to any `I ^ (k+1)` multiple.

As in the kernel half, the annihilating ideal `K` is unrelated to the adic ideal `I`. -/
public theorem completedModuleHom_exists_sub_mem
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I K : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    {t : ℕ}
    (hcok : ∀ k : ℕ, idealPowerMultiple (Scheme.IdealSheafData.ofIdealTop K) t
      (cokernel (C := X.Modules) (f.hom.app (op k))) = ⊥)
    {r : Γ(X, ⊤)} (hr : r ∈ K ^ t) (y : Stacks.Coherent.completedModuleAsBase X I G) (k : ℕ) :
    ∃ x : Stacks.Coherent.completedModuleAsBase X I F,
      r • y - (completedModuleHomBase X I f).hom x ∈
        I ^ (k + 1) • (⊤ : Submodule Γ(X, ⊤) (Stacks.Coherent.completedModuleAsBase X I G)) := by
  have hFq : (F.obj.obj (op k)).IsQuasicoherent :=
    (Stacks.Coherent.coherentSystemAdicData X I F).isQuasicoherent (op k)
  have hGq : (G.obj.obj (op k)).IsQuasicoherent :=
    (Stacks.Coherent.coherentSystemAdicData X I G).isQuasicoherent (op k)
  obtain ⟨z, hz⟩ := smul_mem_range_of_cokernel_eq_bot K (f.hom.app (op k)) (hcok k) hr
    ((Stacks.Coherent.affineLevelProjection X I G k).hom y)
  obtain ⟨x, hx⟩ := Stacks.Coherent.affineLevelProjection_surjective X I F k z
  refine ⟨x, ?_⟩
  refine mem_pow_succ_smul_top_of_affineLevelProjection_eq_zero X I G k ?_
  rw [map_sub, map_smul, affineLevelProjection_completedModuleHomBase X I f k x, hx, hz]
  exact sub_self _

/-- The map of completed modules of a morphism of coherent adic systems, written as a map of
modules over the completed ring at the spelling `Stacks.Coherent.completedModuleAsBase`, which is
the one the projections onto the terms of the system use. -/
public noncomputable def completedModuleMap
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G) :
    Stacks.Coherent.completedModuleAsBase X I F →ₗ[AdicCompletion I Γ(X, ⊤)]
      Stacks.Coherent.completedModuleAsBase X I G where
  toFun := (completedModuleHomBase X I f).hom
  map_add' x y := map_add (completedModuleHomBase X I f).hom x y
  map_smul' r x := ((completedModuleHom X I f).hom).map_smul r x

/-- `Stacks.Algebraization.completedModuleMap` has the same values as the underlying map over
`Γ(X, ⊤)`. -/
public theorem completedModuleMap_apply
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (x : Stacks.Coherent.completedModuleAsBase X I F) :
    completedModuleMap X I f x = (completedModuleHomBase X I f).hom x := rfl

/-- **Tag 0888 (1) on the completed module, kernel half.** If the levelwise kernels and cokernels
of a morphism of coherent adic systems are annihilated by a power of `𝓘`, the kernel of the
induced map of completed modules is `I A^∧`-power torsion. -/
public theorem completedModuleMap_isIPowerTorsion_ker
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (hf : IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop I) f.hom) :
    IsIPowerTorsion (AdicCompletion I Γ(X, ⊤))
      (LinearMap.ker (completedModuleMap X I f))
      (I.map (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) := by
  obtain ⟨t, -, hkc⟩ := hf
  refine isIPowerTorsion_of_smul_top_eq_bot I t ?_
  rw [ideal_smul_top_eq_bot_iff]
  intro r hr z
  exact Subtype.ext (completedModuleHom_smul_eq_zero_of_apply_eq_zero X I I f
    (fun k => (hkc k).1) hr z.1 (LinearMap.mem_ker.1 z.2))

/-- **Tag 0888 (1) on the completed module, cokernel half.** Under the same hypothesis the
cokernel of the induced map of completed modules is `I A^∧`-power torsion: it is a finite module
over the completion, hence `I`-adically Hausdorff, and the chosen power of `I` carries every class
into every `I ^ (k+1)` multiple. -/
public theorem completedModuleMap_isIPowerTorsion_cokernel
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)} (f : F ⟶ G)
    (hf : IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop I) f.hom) :
    IsIPowerTorsion (AdicCompletion I Γ(X, ⊤))
      (Stacks.Coherent.completedModuleAsBase X I G ⧸ LinearMap.range (completedModuleMap X I f))
      (I.map (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) := by
  obtain ⟨t, -, hkc⟩ := hf
  let P := LinearMap.range (completedModuleMap X I f)
  let : Module.Finite (AdicCompletion I Γ(X, ⊤))
      (Stacks.Coherent.completedModuleAsBase X I G ⧸ P) :=
    Module.Finite.of_surjective P.mkQ P.mkQ_surjective
  have hcomplete : IsAdicComplete I
      (Stacks.Coherent.completedModuleAsBase X I G ⧸ P) :=
    Stacks.Coherent.finiteCompletionModule_isAdicComplete I I.fg_of_isNoetherianRing _
  refine isIPowerTorsion_of_smul_top_eq_bot I t ?_
  rw [ideal_smul_top_eq_bot_iff]
  intro r hr c
  induction c using Submodule.Quotient.induction_on with
  | H y =>
    refine eq_zero_of_mem_pow_succ_smul_top I fun k => ?_
    obtain ⟨x, hx⟩ := completedModuleHom_exists_sub_mem X I I f (fun j => (hkc j).2) hr y k
    have hq : ∀ z, (P.mkQ.restrictScalars Γ(X, ⊤)) z = P.mkQ z := fun _ => rfl
    have hmem := Submodule.mem_map_of_mem (f := P.mkQ.restrictScalars Γ(X, ⊤)) hx
    rw [Stacks.Coherent.map_smul_top_local (I ^ (k + 1)) (P.mkQ.restrictScalars Γ(X, ⊤))
      P.mkQ_surjective] at hmem
    have hzero : P.mkQ ((completedModuleHomBase X I f).hom x) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).2 (LinearMap.mem_range.2 ⟨x, rfl⟩)
    rw [map_sub, map_smul, hq, hq, hzero, sub_zero] at hmem
    exact hmem

/-! ### Maps out of an adic completion -/

/-- Two `A`-linear maps out of an adic completion into a Hausdorff module which agree on the
image of the canonical map are equal: every element of the completion differs from such an image
by an element of `I ^ k` times the completion, for every `k`. -/
public theorem linearMap_eq_of_comp_of {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    {N P : Type u} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    [IsHausdorff I P] (g₁ g₂ : AdicCompletion I N →ₗ[A] P)
    (h : ∀ s : N, g₁ (AdicCompletion.of I N s) = g₂ (AdicCompletion.of I N s)) : g₁ = g₂ := by
  refine LinearMap.ext fun x => sub_eq_zero.1 (eq_zero_of_mem_pow_succ_smul_top I fun k => ?_)
  obtain ⟨s, hs⟩ := (I ^ (k + 1) • (⊤ : Submodule A N)).mkQ_surjective
    (AdicCompletion.eval I N (k + 1) x)
  have hz : x - AdicCompletion.of I N s ∈
      I ^ (k + 1) • (⊤ : Submodule A (AdicCompletion I N)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    refine LinearMap.mem_ker.2 ?_
    rw [map_sub, AdicCompletion.eval_of, ← hs]
    exact sub_self _
  have himg (g : AdicCompletion I N →ₗ[A] P) :
      g (x - AdicCompletion.of I N s) ∈ I ^ (k + 1) • (⊤ : Submodule A P) := by
    have hmap := Submodule.mem_map_of_mem (f := g) hz
    rw [Submodule.map_smul'', Submodule.map_top] at hmap
    exact smul_le_smul_left (I ^ (k + 1)) (show LinearMap.range g ≤ ⊤ from le_top) hmap
  have hdiff : g₁ x - g₂ x =
      g₁ (x - AdicCompletion.of I N s) - g₂ (x - AdicCompletion.of I N s) := by
    rw [map_sub, map_sub, h s]
    abel
  rw [hdiff]
  exact Submodule.sub_mem _ (himg g₁) (himg g₂)

/-- Equal ideals have the same adic completion. -/
public noncomputable def adicCompletionCongrIdeal {R : Type u} [CommRing R] {I J : Ideal R}
    (h : I = J) (M : Type u) [AddCommGroup M] [Module R M] :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J M := by
  subst h
  exact LinearEquiv.refl _ _

/-- The comparison of two adic completions along an equality of ideals fixes the image of the
canonical map. -/
public theorem adicCompletionCongrIdeal_of {R : Type u} [CommRing R] {I J : Ideal R}
    (h : I = J) (M : Type u) [AddCommGroup M] [Module R M] (x : M) :
    adicCompletionCongrIdeal h M (AdicCompletion.of I M x) = AdicCompletion.of J M x := by
  subst h
  rfl

/-- The projections onto the terms of a coherent adic system are jointly injective on its
completed module: their kernels are the ideal-power multiples, and the completed module is
`I`-adically Hausdorff. -/
public theorem completedModuleAsBase_ext
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    {x y : Stacks.Coherent.completedModuleAsBase X I F}
    (h : ∀ n : ℕ, (Stacks.Coherent.affineLevelProjection X I F n).hom x =
      (Stacks.Coherent.affineLevelProjection X I F n).hom y) : x = y := by
  have hcomplete := isAdicComplete_completedModuleAsBase X I F
  refine sub_eq_zero.1 (eq_zero_of_mem_pow_succ_smul_top I fun k =>
    mem_pow_succ_smul_top_of_affineLevelProjection_eq_zero X I F k ?_)
  rw [map_sub, h k]
  exact sub_self _

/-! ### The completed module of the completion of a coherent module -/

/-- **Stacks 0880.** The adic completion of the global sections of a coherent module is the
inverse limit of the global sections of its completion: the terms of that system are the adic
quotients of the global sections, compatibly with the transitions. -/
public noncomputable def completionSectionsLimitEquiv
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AdicCompletion ((Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top X⟩)
        Γ(G.obj, ⊤) ≃ₗ[Γ(X, ⊤)]
      (limit (Stacks.Coherent.globalSectionsSystem
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G)) :
          ModuleCat.{u} Γ(X, ⊤)) :=
  AdicCompletion.quotientSystemLimitEquiv
    ((Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top X⟩) Γ(G.obj, ⊤)
    (Stacks.Coherent.globalSectionsSystem
      ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G))
    (fun n => completionQuotientSectionsEquiv X (Scheme.IdealSheafData.ofIdealTop I) G n
      ⟨⊤, isAffineOpen_top X⟩)
    (fun h x => completionQuotientSectionsEquiv_naturality X
      (Scheme.IdealSheafData.ofIdealTop I) G ⟨⊤, isAffineOpen_top X⟩ h x)

/-- **Stacks 0880 and 087W.** The completed module of the completion of a coherent module is the
`I`-adic completion of its global sections. -/
public noncomputable def completionModuleEquiv
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AdicCompletion I Γ(G.obj, ⊤) ≃ₗ[Γ(X, ⊤)]
      Stacks.Coherent.completedModuleAsBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G) :=
  ((adicCompletionCongrIdeal (Stacks.Coherent.ofIdealTop_ideal_top X I).symm
      Γ(G.obj, ⊤)).trans (completionSectionsLimitEquiv X I G)).trans
    (Stacks.Coherent.globalSectionsComparison X I
      ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G)).toLinearEquiv.symm

/-- The comparison of the previous definition carries the image of a global section of `G` to the
element whose projection onto each term of the completion is the canonical one. -/
public theorem affineLevelProjection_completionModuleEquiv_of
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (s : Γ(G.obj, ⊤)) :
    (Stacks.Coherent.affineLevelProjection X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G) n).hom
      (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s)) =
      (completionProjection X (Scheme.IdealSheafData.ofIdealTop I) G n).val.app
        (op (⊤ : X.Opens)) s := by
  set Gc := (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G with hGc
  set c := Stacks.Coherent.globalSectionsComparison X I Gc with hc
  have hinv : ∀ w, c.hom.hom (c.inv.hom w) = w := fun w =>
    congrArg (fun k : (limit (Stacks.Coherent.globalSectionsSystem Gc) :
      ModuleCat.{u} Γ(X, ⊤)) ⟶ _ => k.hom w) c.inv_hom_id
  have h2 := AdicCompletion.limit_π_quotientSystemLimitEquiv_of
    ((Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top X⟩) Γ(G.obj, ⊤)
    (Stacks.Coherent.globalSectionsSystem Gc)
    (fun m => completionQuotientSectionsEquiv X (Scheme.IdealSheafData.ofIdealTop I) G m
      ⟨⊤, isAffineOpen_top X⟩)
    (fun hmn x => completionQuotientSectionsEquiv_naturality X
      (Scheme.IdealSheafData.ofIdealTop I) G ⟨⊤, isAffineOpen_top X⟩ hmn x) n s
  have h1 : (Stacks.Coherent.affineLevelProjection X I Gc n).hom
        (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s)) =
      (limit.π (Stacks.Coherent.globalSectionsSystem Gc) (op n))
        (c.hom.hom (c.inv.hom (completionSectionsLimitEquiv X I G
          (adicCompletionCongrIdeal (Stacks.Coherent.ofIdealTop_ideal_top X I).symm
            Γ(G.obj, ⊤) (AdicCompletion.of I Γ(G.obj, ⊤) s))))) := rfl
  rw [h1, hinv, adicCompletionCongrIdeal_of]
  exact h2.trans (completionQuotientSectionsEquiv_mk X (Scheme.IdealSheafData.ofIdealTop I) G n
    ⟨⊤, isAffineOpen_top X⟩ s)

/-- The map of global sections of a morphism of coherent modules, as a `Γ(X, ⊤)`-linear map. -/
public noncomputable abbrev topSectionsMap {X : Scheme.{u}}
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G) :
    Γ(F.obj, ⊤) →ₗ[Γ(X, ⊤)] Γ(G.obj, ⊤) :=
  (a.hom.val.app (op (⊤ : X.Opens))).hom

/-- **Stacks 0880.** The identification of the completed module of a completion with an adic
completion is natural: it carries the map induced on completions by a morphism of coherent
modules to the adic completion of the map of global sections.

Both sides are `Γ(X, ⊤)`-linear maps out of an adic completion into an `I`-adically complete
module, so they agree as soon as they agree on the image of the canonical map, where the
comparison is computed by the canonical projections. -/
public theorem completionModuleEquiv_naturality
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (z : AdicCompletion I Γ(F.obj, ⊤)) :
    (completedModuleHomBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)).hom
      (completionModuleEquiv X I F z) =
      completionModuleEquiv X I G (AdicCompletion.map I (topSectionsMap a) z) := by
  have hG : IsAdicComplete I (Stacks.Coherent.completedModuleAsBase X I
      ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G)) :=
    isAdicComplete_completedModuleAsBase X I _
  refine LinearMap.congr_fun (linearMap_eq_of_comp_of I I.fg_of_isNoetherianRing
    (((completedModuleHomBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)).hom).comp
      (completionModuleEquiv X I F).toLinearMap)
    ((completionModuleEquiv X I G).toLinearMap.comp
      ((AdicCompletion.map I (topSectionsMap a)).restrictScalars Γ(X, ⊤))) ?_) z
  intro s
  refine completedModuleAsBase_ext X I _ fun n => ?_
  change (Stacks.Coherent.affineLevelProjection X I _ n).hom
      ((completedModuleHomBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)).hom
          (completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) s))) =
    (Stacks.Coherent.affineLevelProjection X I _ n).hom
      (completionModuleEquiv X I G
        (AdicCompletion.map I (topSectionsMap a) (AdicCompletion.of I Γ(F.obj, ⊤) s)))
  rw [affineLevelProjection_completedModuleHomBase,
    affineLevelProjection_completionModuleEquiv_of, AdicCompletion.map_of,
    affineLevelProjection_completionModuleEquiv_of]
  exact congrArg (fun k : F.obj ⟶
      ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj.obj (op n) =>
    k.val.app (op (⊤ : X.Opens)) s)
    (completionFunctor_map_quotient X (Scheme.IdealSheafData.ofIdealTop I) a n)

/-! ### Descending the map of completed modules -/

/-- A `Γ(X, ⊤)`-linear equivalence between modules over the completion whose target is
`I`-adically Hausdorff is linear over the completion. -/
public noncomputable def completionLinearEquiv {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module (AdicCompletion I R) M] [Module (AdicCompletion I R) N]
    [IsScalarTower R (AdicCompletion I R) M] [IsScalarTower R (AdicCompletion I R) N]
    [IsHausdorff I N] (e : M ≃ₗ[R] N) : M ≃ₗ[AdicCompletion I R] N :=
  LinearEquiv.ofBijective
    (show M →ₗ[AdicCompletion I R] N from
      { __ := e.toAddMonoidHom
        map_smul' r m := Stacks.Coherent.completion_linearMap_smul I hI e.toLinearMap r m })
    e.bijective

/-- Upgrading the linearity of an equivalence does not change its values. -/
public theorem completionLinearEquiv_apply {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module (AdicCompletion I R) M] [Module (AdicCompletion I R) N]
    [IsScalarTower R (AdicCompletion I R) M] [IsScalarTower R (AdicCompletion I R) N]
    [IsHausdorff I N] (e : M ≃ₗ[R] N) (x : M) : completionLinearEquiv I hI e x = e x := rfl

/-- **Stacks 0880 and 087W.** The identification of the completed module of a completion with an
adic completion, as an equivalence over the completed ring. -/
public noncomputable def completionModuleEquivₛ
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AdicCompletion I Γ(G.obj, ⊤) ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      Stacks.Coherent.completedModuleAsBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G) :=
  haveI := isAdicComplete_completedModuleAsBase X I
    ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G)
  completionLinearEquiv I I.fg_of_isNoetherianRing (completionModuleEquiv X I G)

/-- `Stacks.Algebraization.completionModuleEquivₛ` has the same values as
`Stacks.Algebraization.completionModuleEquiv`. -/
public theorem completionModuleEquivₛ_apply
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (z : AdicCompletion I Γ(G.obj, ⊤)) :
    completionModuleEquivₛ X I G z = completionModuleEquiv X I G z := rfl

/-- On a finite module over a Noetherian ring, elementwise ideal-power torsion has a uniform
exponent: the support is cut out by the radical of the ideal, so some power of the ideal lies in
the annihilator. -/
public theorem exists_pow_smul_top_eq_bot_of_isIPowerTorsion {R : Type*} [CommRing R]
    (J : Ideal R) (hJ : J.FG) (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsIPowerTorsion R M J) : ∃ n : ℕ, J ^ n • (⊤ : Submodule R M) = ⊥ := by
  have hsupp := support_subset_zeroLocus_of_isIPowerTorsion hM
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsupp
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hsupp hJ
  refine ⟨n, le_antisymm (Submodule.smul_le.mpr fun a ha m _ => ?_) bot_le⟩
  simpa using (Module.mem_annihilator.mp (hn ha)) m

/-- **The affine case of Stacks 0889 (1), at the level of modules.** Let `X` be an affine
Noetherian scheme, `I ⊆ Γ(X, ⊤)` an ideal, `G` a coherent `𝒪_X`-module and `(F_n)` a coherent adic
system along `𝓘`. A morphism `α : (F_n) ⟶ G^∧` whose levelwise kernels and cokernels are
annihilated by one power of `𝓘` comes from a map `ψ : M₀ → Γ(G, ⊤)` of finite `Γ(X, ⊤)`-modules
whose kernel and cokernel are annihilated by a power of `I`, together with an identification of
the completed module of `(F_n)` with the extension of scalars of `M₀`, compatibly with `α`.

This is the whole content of the affine case: the remaining step is to realize `ψ` as a map of
coherent modules through `affineTilde`. -/
public theorem affine_exists_module_algebraization
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (α : Fsys.obj ⟶ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop I) α) :
    ∃ (M₀ : ModuleCat.{u} Γ(X, ⊤)) (ψ : M₀ →ₗ[Γ(X, ⊤)] Γ(G.obj, ⊤))
      (e : TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) M₀ ≃ₗ[AdicCompletion I Γ(X, ⊤)]
        (completedFGModule X I Fsys).obj),
      Module.Finite Γ(X, ⊤) M₀ ∧
        IsIPowerTorsion Γ(X, ⊤) (LinearMap.ker ψ) I ∧
        IsIPowerTorsion Γ(X, ⊤) (Γ(G.obj, ⊤) ⧸ LinearMap.range ψ) I ∧
        ∀ m : M₀, completedModuleMap X I (ObjectProperty.homMk α)
            (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m)) =
          completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) (ψ m)) := by
  have hGcoh : G.obj.IsCoherent := G.property
  have hNfin : Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤) :=
    Stacks.Coherent.coherentAdicTerm_finiteSections X G.obj
  set N := ModuleCat.of Γ(X, ⊤) Γ(G.obj, ⊤) with hN
  set α' : Fsys ⟶ (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G :=
    ObjectProperty.homMk α with hα'
  set E : Stacks.Coherent.completedModuleAsBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G) ≃ₗ[
        AdicCompletion I Γ(X, ⊤)] TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) N :=
    (completionModuleEquivₛ X I G).symm.trans
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N).symm with hE
  set φ : Stacks.Coherent.completedModuleAsBase X I Fsys →ₗ[AdicCompletion I Γ(X, ⊤)]
      TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) N :=
    E.toLinearMap.comp (completedModuleMap X I α') with hφ
  have hkerφ : LinearMap.ker φ = LinearMap.ker (completedModuleMap X I α') := by
    refine Submodule.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hx' : E (completedModuleMap X I α' x) = 0 := LinearMap.mem_ker.1 hx
      exact LinearMap.mem_ker.2 (E.injective (hx'.trans (map_zero E).symm))
    · refine LinearMap.mem_ker.2 ?_
      change E (completedModuleMap X I α' x) = 0
      rw [LinearMap.mem_ker.1 hx, map_zero]
  have hrangeφ : (LinearMap.range (completedModuleMap X I α')).map E.toLinearMap =
      LinearMap.range φ := (LinearMap.range_comp _ _).symm
  have hK : IsIPowerTorsion (AdicCompletion I Γ(X, ⊤)) (LinearMap.ker φ)
      (I.map (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) :=
    isIPowerTorsion_of_linearEquiv _ (LinearEquiv.ofEq _ _ hkerφ.symm)
      (completedModuleMap_isIPowerTorsion_ker X I α' hα)
  have hC : IsIPowerTorsion (AdicCompletion I Γ(X, ⊤))
      (TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) N ⧸ LinearMap.range φ)
      (I.map (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) :=
    isIPowerTorsion_of_linearEquiv _ (Submodule.Quotient.equiv _ _ E hrangeφ)
      (completedModuleMap_isIPowerTorsion_cokernel X I α' hα)
  obtain ⟨M₀, ψ, e, hM₀, hKψ, hCψ, he⟩ :=
    AdicCompletion.exists_finite_descent_of_isIPowerTorsion.{u, u} I N
      (completedFGModule X I Fsys).obj φ hK hC
  refine ⟨M₀, ψ, e, hM₀, hKψ, hCψ, fun m => ?_⟩
  have hcompat := LinearMap.congr_fun he ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m)
  simp only [LinearMap.baseChange_tmul] at hcompat
  have hEapply : E (completedModuleMap X I α'
      (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m))) =
      (1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] (ψ m) := hcompat
  have hofT : AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N
      ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] (ψ m)) =
      AdicCompletion.of I Γ(G.obj, ⊤) (ψ m) := by
    rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
      AdicCompletion.ofTensorProduct_tmul, one_smul]
  have hEinv : E.symm ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] (ψ m)) =
      completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) (ψ m)) := by
    change completionModuleEquivₛ X I G
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N
        ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] (ψ m))) = _
    rw [hofT, completionModuleEquivₛ_apply]
  rw [← hEinv, ← hEapply, E.symm_apply_apply]

/-! ### Annihilation of the kernel and cokernel of a map of coherent modules -/

/-- Annihilation of a module by an ideal transports along a linear equivalence. -/
public theorem ideal_smul_top_eq_bot_of_linearEquiv {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N) (h : J • (⊤ : Submodule R M) = ⊥) :
    J • (⊤ : Submodule R N) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr fun r hr y _ => ?_) bot_le
  obtain ⟨x, rfl⟩ := e.surjective y
  have : r • e x = 0 := by rw [← e.map_smul, (ideal_smul_top_eq_bot_iff J).1 h r hr x, e.map_zero]
  simpa using this

/-- **Evaluation at `⊤` preserves the cokernel of a morphism of quasi-coherent modules on an
affine scheme.** On global sections the morphism is exact onto the sections of its cokernel, and
the quotient projection is surjective there, which is exactly the cokernel cofork in modules. -/
public theorem affine_evaluation_preservesCokernel {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    PreservesColimit (parallelPair (C := X.Modules) f 0)
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) := by
  let T : X.Modules ⥤ ModuleCat Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  have hq : (cokernel (C := X.Modules) f).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f
  have hs := surjective_app_of_epi_of_isAffineOpen (cokernel.π (C := X.Modules) f)
    ⟨⊤, isAffineOpen_top X⟩
  have hc := ModuleCat.isColimitCokernelCofork (T.map f) (T.map (cokernel.π (C := X.Modules) f))
    (affine_sections_cokernel_exact f ⟨⊤, isAffineOpen_top X⟩) hs
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel (C := X.Modules) f) ?_
  exact ((CokernelCofork.ofπ (cokernel.π (C := X.Modules) f)
    (cokernel.condition (C := X.Modules) f)).isColimitMapCoconeEquiv T).symm hc

/-- **Tag 0888 for a morphism of coherent modules on an affine scheme.** If a power of `I`
annihilates the kernel and the cokernel of the map of global sections, then a power of `𝓘`
annihilates the sheaf kernel and the sheaf cokernel: evaluation at `⊤` preserves both. -/
public theorem isPowerAnnihilated_kernel_cokernel_of_sections {X : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (hK : ∃ n : ℕ, I ^ n • (⊤ : Submodule Γ(X, ⊤)
      (kernel ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map a.hom) :
        ModuleCat Γ(X, ⊤))) = ⊥)
    (hC : ∃ n : ℕ, ∀ r ∈ I ^ n, ∀ y : Γ(G.obj, ⊤),
      ∃ x : Γ(F.obj, ⊤), Scheme.Modules.Hom.app a.hom ⊤ x = r • y) :
    IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I) (kernel (C := X.Modules) a.hom) ∧
      IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
        (cokernel (C := X.Modules) a.hom) := by
  let T : X.Modules ⥤ ModuleCat Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op (⊤ : X.Opens))
  have hFc : F.obj.IsCoherent := F.property
  have hGc : G.obj.IsCoherent := G.property
  have hFq : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hGq : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  have hKcoh : (kernel (C := X.Modules) a.hom).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel a.hom
  have hCcoh : (cokernel (C := X.Modules) a.hom).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel a.hom
  have hKq : (kernel (C := X.Modules) a.hom).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hCq : (cokernel (C := X.Modules) a.hom).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  constructor
  · obtain ⟨n, hn⟩ := hK
    exact ⟨n, Stacks.Coherent.affine_idealPowerMultiple_eq_bot I n
      (kernel (C := X.Modules) a.hom)
      (ideal_smul_top_eq_bot_of_linearEquiv (I ^ n)
        (PreservesKernel.iso T a.hom).symm.toLinearEquiv hn)⟩
  · obtain ⟨n, hn⟩ := hC
    refine ⟨n, Stacks.Coherent.affine_idealPowerMultiple_eq_bot I n
      (cokernel (C := X.Modules) a.hom) ?_⟩
    rw [ideal_smul_top_eq_bot_iff]
    intro r hr y
    have hepi : Epi (cokernel.π (C := X.Modules) a.hom) := coequalizer.π_epi
    obtain ⟨z, hz⟩ := surjective_app_of_epi_of_isAffineOpen
      (cokernel.π (C := X.Modules) a.hom) ⟨⊤, isAffineOpen_top X⟩ y
    obtain ⟨w, hw⟩ := hn r hr z
    calc
      r • y = r • Scheme.Modules.Hom.app (cokernel.π (C := X.Modules) a.hom) ⊤ z :=
        congrArg (fun t => r • t) hz.symm
      _ = Scheme.Modules.Hom.app (cokernel.π (C := X.Modules) a.hom) ⊤ (r • z) :=
        (Scheme.Modules.Hom.app_smul _ r z).symm
      _ = Scheme.Modules.Hom.app (cokernel.π (C := X.Modules) a.hom) ⊤
            (Scheme.Modules.Hom.app a.hom ⊤ w) :=
        congrArg (fun t => Scheme.Modules.Hom.app (cokernel.π (C := X.Modules) a.hom) ⊤ t) hw.symm
      _ = 0 := cokernel_π_app_comp_app a.hom ⊤ w


/-! ### Bridging the three spellings of the global sections of a module

The sections of an `𝒪_X`-module `M` over an open `U` occur in three shapes: as the abelian group
`Γ(M, U)`, as the `Γ(X, U)`-module `(SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M`
produced by the evaluation functor on sheaves of modules, and as
`((SheafOfModules.forget X.ringCatSheaf).obj M).obj (op U)`, read through the forgetful functor to
presheaves of modules. The three have the same underlying type and the same scalar action, but
`AlgebraicGeometry.Scheme.Modules.presheaf` and `AlgebraicGeometry.SheafOfModules.evaluation` stand
between them, so neither instance search nor the `isDefEq` of `exact` and `rw` crosses from one to
another. The bridging instances restate the existing module structure at each spelling, and the
equivalences below name the resulting identifications so that a goal may be moved between the
spellings by a rewrite instead of by relaxing transparency. -/

/-- The `Γ(X, U)`-module structure on the value at `U` of the evaluation functor applied to the
`𝒪_X`-module `M`. -/
local instance moduleEvaluationSections {X : Scheme.{u}} (M : X.Modules)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) ((SheafOfModules.evaluation X.ringCatSheaf U).obj M) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- The `Γ(X, U)`-module structure on the value at `U` of the evaluation functor applied to a
sheaf of `X.ringCatSheaf`-modules `M`. -/
local instance moduleEvaluationSectionsSheaf {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) ((SheafOfModules.evaluation X.ringCatSheaf U).obj M) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- The `Γ(X, U)`-module structure on the sections over `U` of the presheaf of modules underlying
an `𝒪_X`-module `M`. -/
local instance moduleForgetSections {X : Scheme.{u}} (M : X.Modules)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) (((SheafOfModules.forget X.ringCatSheaf).obj M).obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- The `Γ(X, U)`-module structure on the sections over `U` of the presheaf of modules underlying
a sheaf of `X.ringCatSheaf`-modules `M`. -/
local instance moduleForgetSectionsSheaf {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) (((SheafOfModules.forget X.ringCatSheaf).obj M).obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- The sections of an `𝒪_X`-module over an open, identified with the value there of the
evaluation functor on sheaves of modules. The two are the same module over `Γ(X, U)`; the
identification is the identity on elements. -/
public noncomputable def sectionsEvaluationEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M :=
  LinearEquiv.refl _ _

/-- The identification of the two spellings of the sections is the identity on elements. -/
@[simp]
public theorem sectionsEvaluationEquiv_apply {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) : sectionsEvaluationEquiv M U x = x := rfl

/-- The inverse of the identification of the two spellings of the sections is the identity on
elements. -/
@[simp]
public theorem sectionsEvaluationEquiv_symm_apply {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M) :
    (sectionsEvaluationEquiv M U).symm x = x := rfl

/-- **The identification of the two spellings of the sections is natural.** It carries the action
of a morphism of `𝒪_X`-modules on sections to the map the evaluation functor assigns to it. -/
public theorem sectionsEvaluationEquiv_naturality {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (x : Γ(M, U)) :
    sectionsEvaluationEquiv N U (f.app U x) =
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom
        (sectionsEvaluationEquiv M U x) := rfl

/-- The value of the evaluation functor on sheaves of modules, identified with the value of the
underlying presheaf of modules. -/
public noncomputable def evaluationForgetEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M ≃ₗ[Γ(X, U)]
      ((SheafOfModules.forget X.ringCatSheaf).obj M).obj (op U) :=
  LinearEquiv.refl _ _

/-- The identification of the sections read through evaluation with the sections read through the
forgetful functor is the identity on elements. -/
@[simp]
public theorem evaluationForgetEquiv_apply {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M) :
    evaluationForgetEquiv M U x = x := rfl

/-- The map of global sections of a morphism of coherent modules is the map the evaluation functor
assigns to it. This is `Stacks.Algebraization.evaluation_map_hom_apply` read at the spelling
`Stacks.Algebraization.topSectionsMap`. -/
public theorem topSectionsMap_eq_evaluation_map {X : Scheme.{u}}
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (x : Γ(F.obj, ⊤)) :
    topSectionsMap a x =
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map a.hom).hom x := rfl

/-- A `Γ(X, ⊤)`-linear map of global sections, read as a morphism between the values of the
evaluation functor at `⊤`. This is the inverse of
`Stacks.Algebraization.topSectionsMap` on underlying maps. -/
public noncomputable def evaluationOfTopSectionsMap {X : Scheme.{u}} {M N : X.Modules}
    (h : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M ⟶
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj N :=
  ModuleCat.ofHom
    (show (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M →ₗ[Γ(X, ⊤)]
        (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj N from
      ((sectionsEvaluationEquiv N ⊤).toLinearMap.comp h).comp
        (sectionsEvaluationEquiv M ⊤).symm.toLinearMap)

/-- Reading a map of global sections as a morphism of evaluations does not change its values. -/
@[simp]
public theorem evaluationOfTopSectionsMap_hom_apply {X : Scheme.{u}} {M N : X.Modules}
    (h : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)) (x : Γ(M, ⊤)) :
    (evaluationOfTopSectionsMap h).hom x = h x := rfl

/-- **A map of global sections of quasi-coherent modules on an affine scheme comes from a
morphism of modules.** This is `Stacks.Coherent.affineQuasicoherentHomLift` applied to a map of
sections written at the spelling `Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)`. -/
public noncomputable def affineSectionsHomLift {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (h : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)) : M ⟶ N :=
  Stacks.Coherent.affineQuasicoherentHomLift (evaluationOfTopSectionsMap h)

/-- The morphism of modules produced by `Stacks.Algebraization.affineSectionsHomLift` acts on
global sections by the given map. -/
@[simp]
public theorem affineSectionsHomLift_app {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (h : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤)) (x : Γ(M, ⊤)) :
    (affineSectionsHomLift h).app ⊤ x = h x :=
  congrArg (fun k : (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M ⟶
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj N => k.hom x)
    (Stacks.Coherent.affineQuasicoherentHomLift_map (evaluationOfTopSectionsMap h))

/-- Annihilation of the module kernel of a morphism of `𝒪_X`-modules on global sections,
transferred to the kernel formed in `ModuleCat Γ(X, ⊤)` of the map the evaluation functor assigns
to it.

This is the shape in which the kernel hypothesis of
`Stacks.Algebraization.isPowerAnnihilated_kernel_cokernel_of_sections` is stated: the inclusion of
the kernel is a monomorphism of modules, hence injective, so an element of the kernel is pinned
down by its image among the sections. -/
public theorem smul_top_evaluationKernel_eq_bot {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (J : Ideal Γ(X, ⊤)) (h : ∀ r ∈ J, ∀ x : Γ(M, ⊤), f.app ⊤ x = 0 → r • x = 0) :
    J • (⊤ : Submodule Γ(X, ⊤)
      (kernel ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map f) :
        ModuleCat Γ(X, ⊤))) = ⊥ := by
  rw [ideal_smul_top_eq_bot_iff]
  intro r hr z
  have hinj : Function.Injective
      (kernel.ι ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map f)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine hinj ?_
  have hzero : f.app ⊤
      ((kernel.ι ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map f)).hom z) =
      0 :=
    congrArg (fun k => k.hom z)
      (kernel.condition ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map f))
  have hsm := (ModuleCat.Hom.hom
      (kernel.ι ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map f))).map_smul
    (show X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) from r) z
  exact (hsm.trans (h r hr _ hzero)).trans (map_zero _).symm

/-! ### Affine sections of the kernel and the cokernel of a morphism of modules -/

/-- **The affine-sections form of annihilation of the sheaf kernel.** If a power of `ℐ`
annihilates the kernel of a morphism of `𝒪_X`-modules, then over every affine open the kernel of
the morphism on sections is `ℐ(U)`-power torsion: a section killed by the morphism comes from a
section of the kernel sheaf, where a power of `ℐ(U)` kills it. -/
public theorem isIPowerTorsion_ker_affineSectionMap {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} (a : M ⟶ N)
    (hK : IsPowerAnnihilated I (kernel (C := X.Modules) a)) (U : X.affineOpens) :
    IsIPowerTorsion Γ(X, U) (LinearMap.ker (affineSectionMap a U)) (I.ideal U) := by
  intro z
  have hz : affineSectionMap a U z.1 = 0 := LinearMap.mem_ker.1 z.2
  have hz' : a.app U.1 z.1 = 0 := hz
  obtain ⟨y, hy⟩ := exists_kernel_section a U.1 z.1 hz'
  obtain ⟨n, hn, hkill⟩ := isIPowerTorsion_sections_of_isPowerAnnihilated hK U y
  refine ⟨n, hn, fun r hr => Subtype.ext ?_⟩
  calc
    r • z.1 = r • (kernel.ι (C := X.Modules) a).app U.1 y := by rw [hy]
    _ = (kernel.ι (C := X.Modules) a).app U.1 (r • y) :=
      (Scheme.Modules.Hom.app_smul _ _ _).symm
    _ = 0 := by rw [hkill r hr, map_zero]

/-- **The affine-sections form of annihilation of the sheaf cokernel.** If a power of `ℐ`
annihilates the cokernel of a morphism of quasi-coherent modules, then over every affine open the
cokernel of the morphism on sections is `ℐ(U)`-power torsion: a power of `ℐ(U)` carries the class
of a section into the kernel of the projection to the cokernel sheaf, and evaluation at an affine
open is exact there. -/
public theorem isIPowerTorsion_cokernel_affineSectionMap {X : Scheme.{u}} (I : X.IdealSheafData)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (hC : IsPowerAnnihilated I (cokernel (C := X.Modules) a)) (U : X.affineOpens) :
    IsIPowerTorsion Γ(X, U) (Γ(N, U) ⧸ LinearMap.range (affineSectionMap a U)) (I.ideal U) := by
  intro c
  induction c using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨n, hn, hkill⟩ := isIPowerTorsion_sections_of_isPowerAnnihilated hC U
      ((cokernel.π (C := X.Modules) a).app U.1 y)
    refine ⟨n, hn, fun r hr => ?_⟩
    have hzero : (cokernel.π (C := X.Modules) a).app U.1 (r • y) = 0 := by
      rw [Scheme.Modules.Hom.app_smul]
      exact hkill r hr
    obtain ⟨x, hx⟩ := (affine_sections_cokernel_exact a U (r • y)).mp hzero
    have hsm : r • Submodule.Quotient.mk (p := LinearMap.range (affineSectionMap a U)) y =
        Submodule.Quotient.mk (p := LinearMap.range (affineSectionMap a U)) (r • y) := rfl
    rw [hsm]
    exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨x, hx⟩)

/-! ### Realizing a map of finite modules by a morphism of coherent modules -/

/-- **The sheaf form of the output of the affine descent.** On an affine Noetherian scheme a map
`ψ : M₀ → Γ(G, ⊤)` of finite `Γ(X, ⊤)`-modules whose kernel and cokernel are `I`-power torsion is
the map of global sections of a morphism `a : F ⟶ G` of coherent modules, with `M₀` identified
with `Γ(F, ⊤)`; and the kernel and the cokernel of `a` are then annihilated by a power of the
ideal sheaf attached to `I`.

The module `F` is the sheaf `M₀ ~` attached to `M₀`, which is coherent because `M₀` is finite, and
`a` is the morphism that `ψ` induces because global sections are fully faithful on quasi-coherent
modules. The annihilation statements come from
`Stacks.Algebraization.isPowerAnnihilated_kernel_cokernel_of_sections`, whose hypotheses are the
uniform annihilation of the kernel and of the cokernel of `ψ`; those follow from elementwise
ideal-power torsion because both modules are finite over a Noetherian ring. -/
public theorem exists_coherent_realization (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (M₀ : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M₀]
    (ψ : M₀ →ₗ[Γ(X, ⊤)] Γ(G.obj, ⊤))
    (hK : IsIPowerTorsion Γ(X, ⊤) (LinearMap.ker ψ) I)
    (hC : IsIPowerTorsion Γ(X, ⊤) (Γ(G.obj, ⊤) ⧸ LinearMap.range ψ) I) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
      (δ : M₀ ≃ₗ[Γ(X, ⊤)] Γ(F.obj, ⊤)),
      (∀ m : M₀, topSectionsMap a (δ m) = ψ m) ∧
        IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
            (kernel (C := X.Modules) a.hom) ∧
          IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
            (cokernel (C := X.Modules) a.hom) := by
  have hGcoh : G.obj.IsCoherent := G.property
  have hGq : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  have hGfin : Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤) :=
    Stacks.Coherent.coherentAdicTerm_finiteSections X G.obj
  have hTq : ((Stacks.Coherent.affineTilde X).obj M₀).IsQuasicoherent :=
    Stacks.Coherent.affineTilde_quasicoherent X M₀
  have hTcoh : ((Stacks.Coherent.affineTilde X).obj M₀).IsCoherent :=
    Stacks.Coherent.affineTilde_coherent X M₀
  set δ : M₀ ≃ₗ[Γ(X, ⊤)] Γ((Stacks.Coherent.affineTilde X).obj M₀, ⊤) :=
    (Stacks.Coherent.affineTildeSectionsIso X M₀).toLinearEquiv.trans
      (sectionsEvaluationEquiv ((Stacks.Coherent.affineTilde X).obj M₀) ⊤).symm with hδ
  set a : (⟨(Stacks.Coherent.affineTilde X).obj M₀, hTcoh⟩ :
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ⟶ G :=
    ObjectProperty.homMk (affineSectionsHomLift (ψ.comp δ.symm.toLinearMap)) with ha
  have hfac : ∀ m : M₀, topSectionsMap a (δ m) = ψ m := by
    intro m
    have h1 : (affineSectionsHomLift (ψ.comp δ.symm.toLinearMap)).app ⊤ (δ m) =
        ψ (δ.symm (δ m)) := affineSectionsHomLift_app (ψ.comp δ.symm.toLinearMap) (δ m)
    rw [δ.symm_apply_apply] at h1
    exact h1
  have hkerfin : Module.Finite Γ(X, ⊤) (LinearMap.ker ψ) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  obtain ⟨nK, hnK⟩ := exists_pow_smul_top_eq_bot_of_isIPowerTorsion I
    I.fg_of_isNoetherianRing (LinearMap.ker ψ) hK
  have hquotfin : Module.Finite Γ(X, ⊤) (Γ(G.obj, ⊤) ⧸ LinearMap.range ψ) :=
    Module.Finite.of_surjective (LinearMap.range ψ).mkQ (LinearMap.range ψ).mkQ_surjective
  obtain ⟨nC, hnC⟩ := exists_pow_smul_top_eq_bot_of_isIPowerTorsion I
    I.fg_of_isNoetherianRing (Γ(G.obj, ⊤) ⧸ LinearMap.range ψ) hC
  have hKbridge : ∃ n : ℕ, I ^ n • (⊤ : Submodule Γ(X, ⊤)
      (kernel ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map a.hom) :
        ModuleCat Γ(X, ⊤))) = ⊥ := by
    refine ⟨nK, smul_top_evaluationKernel_eq_bot a.hom (I ^ nK) ?_⟩
    intro r hr x hx
    have hm : ψ (δ.symm x) = 0 := by
      have h1 : topSectionsMap a (δ (δ.symm x)) = ψ (δ.symm x) := hfac (δ.symm x)
      rw [δ.apply_symm_apply] at h1
      exact h1.symm.trans hx
    have h2 : r • δ.symm x = 0 :=
      congrArg Subtype.val ((ideal_smul_top_eq_bot_iff (I ^ nK)).1 hnK r hr
        ⟨δ.symm x, LinearMap.mem_ker.2 hm⟩)
    rw [← δ.apply_symm_apply x, ← map_smul, h2, map_zero]
  have hCbridge : ∃ n : ℕ, ∀ r ∈ I ^ n, ∀ y : Γ(G.obj, ⊤),
      ∃ x : Γ((⟨(Stacks.Coherent.affineTilde X).obj M₀, hTcoh⟩ :
        AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf).obj, ⊤),
        Scheme.Modules.Hom.app a.hom ⊤ x = r • y := by
    refine ⟨nC, fun r hr y => ?_⟩
    have h0 := (ideal_smul_top_eq_bot_iff (I ^ nC)).1 hnC r hr (Submodule.Quotient.mk y)
    obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range ψ)).1 h0
    exact ⟨δ m, (hfac m).trans hm⟩
  obtain ⟨hk, hc⟩ := isPowerAnnihilated_kernel_cokernel_of_sections I a hKbridge hCbridge
  exact ⟨_, a, δ, hfac, hk, hc⟩

/-! ### Maps out of an extension of scalars -/

/-- Two `S`-linear maps out of `S ⊗_R M` which agree on the elements `1 ⊗ m` are equal: those
elements generate the tensor product over `S`.

This is the public form of the corresponding step of
`AdicCompletion.exists_finite_descent_of_isIPowerTorsion`. -/
public theorem tensorProduct_linearMap_ext {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {M : Type*} [AddCommGroup M] [Module R M]
    {P : Type*} [AddCommGroup P] [Module S P] (f g : TensorProduct R S M →ₗ[S] P)
    (h : ∀ m : M, f ((1 : S) ⊗ₜ[R] m) = g ((1 : S) ⊗ₜ[R] m)) : f = g := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    have hs : (s ⊗ₜ[R] m : TensorProduct R S M) = s • ((1 : S) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### The affine case of Stacks 0889 (1) -/

/-- **The affine case of Stacks 0889 (1).** Let `X` be an affine Noetherian scheme,
`I ⊆ Γ(X, ⊤)` an ideal, `𝓘` the quasi-coherent ideal sheaf it determines, `G` a coherent
`𝒪_X`-module and `(F_n)` a coherent adic system along `𝓘`. A morphism
`α : (F_n) ⟶ G^∧` whose levelwise kernels and cokernels are annihilated by one power of `𝓘` is the
completion of a morphism of coherent modules: there are a coherent module `F`, a morphism
`a : F ⟶ G` whose kernel and cokernel are annihilated by a power of `𝓘`, and an isomorphism `β` of
`(F_n)` with the completion of `F` through which `α` is the completion of `a`.

Everything analytic has already happened in
`Stacks.Algebraization.affine_exists_module_algebraization`, which produces the finite module
`M₀`, the map `ψ : M₀ → Γ(G, ⊤)`, and the identification `e` of the completed module of `(F_n)`
with the extension of scalars of `M₀`. The map `ψ` becomes a morphism of coherent modules by
`Stacks.Algebraization.exists_coherent_realization`, and the isomorphism `β` is produced from `e`
by the equivalence of tag 087W: composing `e` with the comparison of the adic completion of `M₀`
with the extension of scalars, with the adic completion of the identification `M₀ ≅ Γ(F, ⊤)`, and
with the identification of the completed module of a completion with an adic completion, gives an
isomorphism of completed modules, and the equivalence turns it back into an isomorphism of
coherent adic systems. That `α` is the completion of `a` read through `β` is checked after
applying the equivalence, where both sides are maps out of the extension of scalars of `M₀` and
agree on the elements `1 ⊗ m` by the compatibility clause of the module statement and the
naturality of the identification of a completion with an adic completion. -/
public theorem affine_exists_algebraization (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (α : Fsys.obj ⟶ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop I) α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
      (β : Fsys.obj ≅
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F).obj),
      α = β.hom ≫ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a).hom ∧
        IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
            (kernel (C := X.Modules) a.hom) ∧
          IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
            (cokernel (C := X.Modules) a.hom) := by
  obtain ⟨M₀, ψ, e, hM₀, hKψ, hCψ, hcompat⟩ :=
    affine_exists_module_algebraization X I G Fsys α hα
  obtain ⟨F, a, δ, hfac, hker, hcok⟩ := exists_coherent_realization X I G M₀ ψ hKψ hCψ
  set Θ₀ : (completedFGModule X I Fsys).obj ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      (completedFGModule X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F)).obj :=
    e.symm.trans (((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀).trans
      (AdicCompletion.congr I δ)).trans (completionModuleEquivₛ X I F)) with hΘ₀
  have hΘval : ∀ m : M₀, Θ₀ (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m)) =
      completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) (δ m)) := by
    intro m
    change completionModuleEquivₛ X I F (AdicCompletion.congr I δ
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀
        (e.symm (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m))))) = _
    rw [e.symm_apply_apply, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
      AdicCompletion.ofTensorProduct_tmul, one_smul, AdicCompletion.congr_apply,
      AdicCompletion.map_of, completionModuleEquivₛ_apply]
    rfl
  have hkey : ∀ w : Stacks.Coherent.completedModuleAsBase X I Fsys,
      completedModuleMap X I (ObjectProperty.homMk α) w =
        completedModuleMap X I
          ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a) (Θ₀ w) := by
    have hL : (completedModuleMap X I (ObjectProperty.homMk α)).comp e.toLinearMap =
        ((completedModuleMap X I
            ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)).comp
          Θ₀.toLinearMap).comp e.toLinearMap := by
      refine tensorProduct_linearMap_ext _ _ fun m => ?_
      have hlhs : completedModuleMap X I (ObjectProperty.homMk α)
          (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m)) =
          completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) (ψ m)) := hcompat m
      have hnat := completionModuleEquiv_naturality X I a
        (AdicCompletion.of I Γ(F.obj, ⊤) (δ m))
      rw [AdicCompletion.map_of, hfac m] at hnat
      change completedModuleMap X I (ObjectProperty.homMk α)
          (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m)) =
        completedModuleMap X I
          ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)
          (Θ₀ (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m)))
      rw [hlhs, hΘval m]
      exact hnat.symm
    intro w
    obtain ⟨t, rfl⟩ := e.surjective w
    exact LinearMap.congr_fun hL t
  set E := Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I with hE
  set Θ : completedFGModule X I Fsys ≅
      completedFGModule X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F) :=
    ObjectProperty.isoMk _ Θ₀.toModuleIso with hΘ
  set βsys : Fsys ≅ (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F :=
    E.functor.preimageIso Θ with hβsys
  have hmapβ : E.functor.map βsys.hom = Θ.hom := E.functor.map_preimage Θ.hom
  have hmain : (ObjectProperty.homMk α :
      Fsys ⟶ (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G) =
      βsys.hom ≫ (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a := by
    refine E.functor.map_injective ?_
    rw [E.functor.map_comp, hmapβ]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext hkey
  refine ⟨F, a, ⟨βsys.hom.hom, βsys.inv.hom,
    ObjectProperty.isoHom_inv_id_hom βsys, ObjectProperty.isoInv_hom_id_hom βsys⟩,
    ?_, hker, hcok⟩
  exact congrArg (fun k : Fsys ⟶
    (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G => k.hom) hmain

/-- **The uniqueness clause of Stacks 0889 (1).** Two algebraizations of the same datum
`(G, (F_n), α)` whose comparison maps have kernel and cokernel annihilated by a power of `ℐ` are
related by a unique isomorphism compatible with the maps to `G` and with the two identifications
of the formal system.

The formal pullback of `(G, (F_n), α)` mediates: an algebraization whose comparison map has
power-torsion kernel and cokernel on the sections over each affine open is the formal pullback, by
`Stacks.Algebraization.formalPullbackFromAlgebraization_isIso`, and the annihilation of the sheaf
kernel and the sheaf cokernel gives that affine-sections hypothesis through
`Stacks.Algebraization.isIPowerTorsion_ker_affineSectionMap` and
`Stacks.Algebraization.isIPowerTorsion_cokernel_affineSectionMap`. -/
public theorem unique_algebraization_of_isPowerAnnihilated {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (a : F ⟶ G) (a' : F' ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (β' : Fsys.obj ≅ ((completionFunctor X I).obj F').obj)
    (hα : α = β.hom ≫ ((completionFunctor X I).map a).hom)
    (hα' : α = β'.hom ≫ ((completionFunctor X I).map a').hom)
    (hKa : IsPowerAnnihilated I (kernel (C := X.Modules) a.hom))
    (hCa : IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom))
    (hKa' : IsPowerAnnihilated I (kernel (C := X.Modules) a'.hom))
    (hCa' : IsPowerAnnihilated I (cokernel (C := X.Modules) a'.hom)) :
    ∃! d : F.obj ≅ F'.obj,
      d.hom ≫ a'.hom = a.hom ∧
        d.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules) β'.inv) =
          completionToLimit X I F ≫ limMap (C := X.Modules) β.inv := by
  have hFq : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hF'q : F'.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F'.obj
  have hGq : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  exact formalPullback_unique_iso_of_isIso X I G Fsys α F F' a a' β β' hα hα'
    (formalPullbackFromAlgebraization_isIso X I G Fsys α F a β hα
      (fun U => isIPowerTorsion_ker_affineSectionMap I a.hom hKa U)
      (fun U => isIPowerTorsion_cokernel_affineSectionMap I a.hom hCa U))
    (formalPullbackFromAlgebraization_isIso X I G Fsys α F' a' β' hα'
      (fun U => isIPowerTorsion_ker_affineSectionMap I a'.hom hKa' U)
      (fun U => isIPowerTorsion_cokernel_affineSectionMap I a'.hom hCa' U))

/-- **The affine case of the uniqueness clause of Stacks 0889 (1).** On an affine Noetherian
scheme, two algebraizations of the same datum along the ideal sheaf attached to an ideal
`I ⊆ Γ(X, ⊤)`, with kernel and cokernel of both comparison maps annihilated by a power of that
ideal sheaf, are related by a unique isomorphism compatible with the maps to `G` and with the two
identifications of the formal system.

Together with `Stacks.Algebraization.affine_exists_algebraization` this is the affine case of
Stacks 0889 part (1). -/
public theorem affine_unique_algebraization (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (α : Fsys.obj ⟶ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj)
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (a : F ⟶ G) (a' : F' ⟶ G)
    (β : Fsys.obj ≅ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F).obj)
    (β' : Fsys.obj ≅ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F').obj)
    (hα : α = β.hom ≫ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a).hom)
    (hα' : α = β'.hom ≫ ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a').hom)
    (hKa : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (kernel (C := X.Modules) a.hom))
    (hCa : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (cokernel (C := X.Modules) a.hom))
    (hKa' : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (kernel (C := X.Modules) a'.hom))
    (hCa' : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (cokernel (C := X.Modules) a'.hom)) :
    ∃! d : F.obj ≅ F'.obj,
      d.hom ≫ a'.hom = a.hom ∧
        d.hom ≫ (completionToLimit X (Scheme.IdealSheafData.ofIdealTop I) F' ≫
            limMap (C := X.Modules) β'.inv) =
          completionToLimit X (Scheme.IdealSheafData.ofIdealTop I) F ≫
            limMap (C := X.Modules) β.inv :=
  unique_algebraization_of_isPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I) G Fsys α F F'
    a a' β β' hα hα' hKa hCa hKa' hCa'

end Stacks.Algebraization

end
