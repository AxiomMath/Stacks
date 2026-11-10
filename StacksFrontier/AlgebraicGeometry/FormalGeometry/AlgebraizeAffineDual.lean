module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleCodescent

/-!
# Algebraizing a map out of a completion on an affine scheme

Let `X` be an affine Noetherian scheme, `I ⊆ Γ(X, ⊤)` an ideal and `𝓘` the quasi-coherent ideal
sheaf it determines. Let `G` be a coherent `𝒪_X`-module and `(F_n)` a coherent adic system along
`𝓘`. This file carries out the affine case of Stacks 0889 part (2), the statement with both arrows
reversed: a morphism `α : G^∧ ⟶ (F_n)` *out of* the completion of `G` whose levelwise kernels and
cokernels are annihilated by one power of `𝓘` is the completion of a morphism `a : G ⟶ F` of
coherent modules whose kernel and cokernel are annihilated by a power of `𝓘`, through an
isomorphism `β : F^∧ ≅ (F_n)` with `α = β ∘ a^∧`.

The hypothesis on `α` is the levelwise condition of tag 0888 (1), which is stated for an arbitrary
morphism of systems of `𝒪_X`-modules and therefore applies in this direction unchanged.

## Main definitions

* `Stacks.Algebraization.completionSectionsTensorEquiv` — the completed module of `G^∧`, read as
  the extension of scalars of `Γ(G, ⊤)` to the completed ring.
* `Stacks.Algebraization.codescentCompletedModuleEquiv` — the isomorphism of completed modules
  which a codescent of the map of completed modules produces.
* `Stacks.Algebraization.completedModuleEquivOfIso` and
  `Stacks.Algebraization.completionTensorSystemEquiv` — the isomorphism of completed modules
  attached to an isomorphism of coherent adic systems, and the extension of scalars of
  `Γ(F, ⊤)` identified with the completed module of `(F_n)` through an isomorphism `F^∧ ≅ (F_n)`.
* `Stacks.Algebraization.affineSectionsIsoLift` and
  `Stacks.Algebraization.topSectionsEquivOfIso` — an isomorphism of the global sections of two
  coherent modules on an affine scheme, read as an isomorphism of the modules, and conversely.

## Main results

* `Stacks.Algebraization.affine_exists_module_algebraization_dual` — **the affine case of Stacks
  0889 (2), at the level of modules**: the codescended map `ψ : Γ(G, ⊤) → M₀`, its ideal-power
  torsion kernel and cokernel, the identification of the extension of scalars of `M₀` with the
  completed module of `(F_n)`, and the compatibility of that identification with `α`.
* `Stacks.Algebraization.exists_coherent_realization_dual` — a map of finite `Γ(X, ⊤)`-modules out
  of `Γ(G, ⊤)` with ideal-power torsion kernel and cokernel is the map of global sections of a
  morphism `a : G ⟶ F` of coherent modules whose kernel and cokernel are annihilated by a power
  of `𝓘`.
* `Stacks.Algebraization.completedModuleMap_eq_codescent` — the map of completed modules induced
  by `α` is the completion of `a` read through the codescent.
* `Stacks.Algebraization.affine_exists_algebraization_dual` — **the affine case of Stacks 0889
  (2)**: the coherent module `F`, the morphism `a : G ⟶ F` with kernel and cokernel annihilated by
  a power of `𝓘`, and the isomorphism `β : F^∧ ≅ (F_n)` through which `α` is the completion of
  `a`.
* `Stacks.Algebraization.completedModuleHom_ext_of_sections` — two morphisms out of the completion
  of a coherent module agree once their completed modules agree on the images of global sections.
* `Stacks.Algebraization.isIPowerTorsion_ker_topSectionsMap` and
  `Stacks.Algebraization.isIPowerTorsion_cokernel_topSectionsMap` — annihilation of the sheaf
  kernel and the sheaf cokernel by a power of `𝓘` makes the kernel and the cokernel of the map of
  global sections `I`-power torsion.
* `Stacks.Algebraization.affine_unique_algebraization_dual` — **the uniqueness clause of the
  affine case of Stacks 0889 (2)**: two such algebraizations are related by a unique isomorphism
  compatible with the maps out of `G` and with the two identifications of the formal system.

## Implementation notes

The translation of the levelwise hypothesis is reused verbatim rather than dualized.
`Stacks.Algebraization.completedModuleMap_isIPowerTorsion_ker` and
`Stacks.Algebraization.completedModuleMap_isIPowerTorsion_cokernel` are stated for an arbitrary
morphism of coherent adic systems, and the completeness they consume is that of the completed
module of the source for the kernel half and of a quotient of the completed module of the target
for the cokernel half. Every completed module of a coherent adic system is finite over the
`I`-adic completion of `Γ(X, ⊤)`, hence `I`-adically complete and so Hausdorff, so both halves
hold with the roles of `G^∧` and `(F_n)` exchanged.

What genuinely changes is the module-level input. The map of completed modules induced by `α` is
read as a map *out of* the extension of scalars `A^∧ ⊗_A Γ(G, ⊤)`, and it is
`AdicCompletion.exists_finite_codescent_of_isIPowerTorsion` rather than the descent theorem that
applies to it. That result replaces the target of such a map by the extension of scalars of a
finite `A`-module, which is the direction dual to the one replacing the source.

Uniqueness is not the fibre-product characterization that settles part (1). In this direction the
mediating object would be a pushout rather than a pullback and does not have the required
property, so the comparison is made at the level of modules and transported back:
`AdicCompletion.codescent_unique` compares two codescents of one map, and global sections, which
are fully faithful on coherent modules over an affine scheme, together with the faithfulness of
the equivalence of tag 087W, turn its unique isomorphism of modules into the unique isomorphism of
sheaves.

The local instances bridging the two presentations of the category of modules, and those recording
the structure of the completed module of a coherent adic system over the completed ring, are
reactivated from `Stacks.Algebraization.CompletionFunctor.AffineSections` and from
`Stacks.Algebraization.AlgebraizeAffine`; as there, categorical constructions name their category
explicitly as `(C := X.Modules)` and the coherence of a kernel or a cokernel is supplied by name.
The isomorphisms of coherent adic systems built from an isomorphism of the underlying systems are
introduced by `let` rather than `have`, since the proofs reduce their underlying morphisms.
Equations which would naturally be `rw` are `congrArg` chains composed with `Eq.trans`: a rewrite
motive mixing the two presentations of the category of modules is not type correct at the
transparency `rw` builds it at.

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

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

attribute [local instance] moduleCompletionCompletedModuleAsBase finiteCompletedModuleAsBase
  isScalarTowerCompletedModuleAsBase

attribute [local instance] moduleEvaluationSections moduleEvaluationSectionsSheaf
  moduleForgetSections moduleForgetSectionsSheaf

/-! ### Transporting ideal-power torsion along a change of source -/

/-- Precomposing with a linear equivalence does not change the ideal-power torsion of the kernel:
the equivalence restricts to an isomorphism of the two kernels. -/
public theorem isIPowerTorsion_ker_comp_linearEquiv {R : Type*} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (J : Ideal R) (e : M ≃ₗ[R] N) (g : N →ₗ[R] P)
    (hg : IsIPowerTorsion R (LinearMap.ker g) J) :
    IsIPowerTorsion R (LinearMap.ker (g.comp e.toLinearMap)) J := by
  intro x
  have hx : e x.1 ∈ LinearMap.ker g := x.2
  obtain ⟨n, hn, hkill⟩ := hg ⟨e x.1, hx⟩
  refine ⟨n, hn, fun a ha => ?_⟩
  apply Subtype.ext
  apply e.injective
  have h0 : a • e x.1 = 0 := congrArg Subtype.val (hkill a ha)
  simpa using h0

/-! ### Codescending the map of completed modules -/

/-- The comparison of the completed module of `G^∧` with an extension of scalars carries `1 ⊗ s` to
the image of the global section `s`. -/
private theorem completionModuleEquivₛ_ofTensorProductEquiv_one_tmul
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤)] (s : Γ(G.obj, ⊤)) :
    completionModuleEquivₛ X I G
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I
        (ModuleCat.of Γ(X, ⊤) Γ(G.obj, ⊤))
        ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s)) =
      completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s) := by
  rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul, one_smul, completionModuleEquivₛ_apply]

/-- **The affine case of Stacks 0889 (2), at the level of modules.** Let `X` be an affine
Noetherian scheme, `I ⊆ Γ(X, ⊤)` an ideal, `G` a coherent `𝒪_X`-module and `(F_n)` a coherent adic
system along `𝓘`. A morphism `α : G^∧ ⟶ (F_n)` whose levelwise kernels and cokernels are
annihilated by one power of `𝓘` comes from a map `ψ : Γ(G, ⊤) → M₀` of finite `Γ(X, ⊤)`-modules
whose kernel and cokernel are `I`-power torsion, together with an identification of the extension
of scalars of `M₀` with the completed module of `(F_n)`, compatibly with `α`.

The completed module of `G^∧` is the extension of scalars `A^∧ ⊗_A Γ(G, ⊤)`, by
`Stacks.Algebraization.completionModuleEquivₛ` and the comparison of an adic completion with an
extension of scalars, so the map of completed modules which `α` induces is a map out of that
extension of scalars whose kernel and cokernel are `I A^∧`-power torsion. Codescent along the
completion, in the form `AdicCompletion.exists_finite_codescent_of_isIPowerTorsion`, replaces its
target by the extension of scalars of a finite `Γ(X, ⊤)`-module. -/
public theorem affine_exists_module_algebraization_dual
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (α : ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop I) α) :
    ∃ (M₀ : ModuleCat.{u} Γ(X, ⊤)) (ψ : Γ(G.obj, ⊤) →ₗ[Γ(X, ⊤)] M₀)
      (e : TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) M₀ ≃ₗ[AdicCompletion I Γ(X, ⊤)]
        (completedFGModule X I Fsys).obj),
      Module.Finite Γ(X, ⊤) M₀ ∧
        IsIPowerTorsion Γ(X, ⊤) (LinearMap.ker ψ) I ∧
        IsIPowerTorsion Γ(X, ⊤) (M₀ ⧸ LinearMap.range ψ) I ∧
        ∀ s : Γ(G.obj, ⊤),
          completedModuleMap X I (ObjectProperty.homMk α)
              (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s)) =
            e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] ψ s) := by
  have hGcoh : G.obj.IsCoherent := G.property
  have hNfin : Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤) :=
    Stacks.Coherent.coherentAdicTerm_finiteSections X G.obj
  set N := ModuleCat.of Γ(X, ⊤) Γ(G.obj, ⊤) with hN
  set α' : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G ⟶ Fsys :=
    ObjectProperty.homMk α with hα'
  set E : Stacks.Coherent.completedModuleAsBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G) ≃ₗ[
        AdicCompletion I Γ(X, ⊤)] TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) N :=
    (completionModuleEquivₛ X I G).symm.trans
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N).symm with hE
  set φ : TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) N →ₗ[AdicCompletion I Γ(X, ⊤)]
      Stacks.Coherent.completedModuleAsBase X I Fsys :=
    (completedModuleMap X I α').comp E.symm.toLinearMap with hφ
  have hK : IsIPowerTorsion (AdicCompletion I Γ(X, ⊤)) (LinearMap.ker φ)
      (I.map (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) :=
    isIPowerTorsion_ker_comp_linearEquiv _ E.symm (completedModuleMap X I α')
      (completedModuleMap_isIPowerTorsion_ker X I α' hα)
  have hrange : LinearMap.range (completedModuleMap X I α') = LinearMap.range φ :=
    (LinearEquiv.range_comp E.symm (completedModuleMap X I α')).symm
  have hC : IsIPowerTorsion (AdicCompletion I Γ(X, ⊤))
      (Stacks.Coherent.completedModuleAsBase X I Fsys ⧸ LinearMap.range φ)
      (I.map (algebraMap Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)))) :=
    isIPowerTorsion_of_linearEquiv _ (Submodule.quotEquivOfEq _ _ hrange)
      (completedModuleMap_isIPowerTorsion_cokernel X I α' hα)
  obtain ⟨M₀, ψ, e, hM₀, hKψ, hCψ, he⟩ :=
    AdicCompletion.exists_finite_codescent_of_isIPowerTorsion.{u, u} I N
      (completedFGModule X I Fsys).obj φ hK hC
  refine ⟨M₀, ψ, e, hM₀, hKψ, hCψ, fun s => ?_⟩
  have hbc : LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) ψ
      ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) =
      (1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] ψ s := LinearMap.baseChange_tmul _ _ _
  have hcf : e (LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) ψ
        ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s)) =
      φ ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) :=
    LinearMap.congr_fun he _
  have hcompat : e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] ψ s) =
      φ ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) :=
    (congrArg e hbc).symm.trans hcf
  have hEinv : E.symm ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) =
      completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s) :=
    completionModuleEquivₛ_ofTensorProductEquiv_one_tmul X I G s
  have hlhs : φ ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) =
      completedModuleMap X I α'
        (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s)) :=
    congrArg (completedModuleMap X I α') hEinv
  exact hlhs.symm.trans hcompat.symm

/-! ### Realizing a map out of the global sections by a morphism of coherent modules -/

/-- **The sheaf form of the output of the affine codescent.** On an affine Noetherian scheme a map
`ψ : Γ(G, ⊤) → M₀` from the global sections of a coherent module to a finite `Γ(X, ⊤)`-module,
with `I`-power torsion kernel and cokernel, is the map of global sections of a morphism
`a : G ⟶ F` of coherent modules, with `M₀` identified with `Γ(F, ⊤)`; and the kernel and the
cokernel of `a` are then annihilated by a power of the ideal sheaf attached to `I`.

The module `F` is the sheaf `M₀ ~` attached to `M₀`, which is coherent because `M₀` is finite, and
`a` is the morphism that `ψ` induces because global sections are fully faithful on quasi-coherent
modules over an affine scheme. The annihilation statements come from
`Stacks.Algebraization.isPowerAnnihilated_kernel_cokernel_of_sections`, which is stated for an
arbitrary morphism of coherent modules; its hypotheses are the uniform annihilation of the kernel
and of the cokernel of `ψ`, and those follow from elementwise ideal-power torsion because both
modules are finite over a Noetherian ring. -/
public theorem exists_coherent_realization_dual (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (M₀ : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M₀]
    (ψ : Γ(G.obj, ⊤) →ₗ[Γ(X, ⊤)] M₀)
    (hK : IsIPowerTorsion Γ(X, ⊤) (LinearMap.ker ψ) I)
    (hC : IsIPowerTorsion Γ(X, ⊤) (M₀ ⧸ LinearMap.range ψ) I) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : G ⟶ F)
      (δ : M₀ ≃ₗ[Γ(X, ⊤)] Γ(F.obj, ⊤)),
      (∀ s : Γ(G.obj, ⊤), topSectionsMap a s = δ (ψ s)) ∧
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
  set a : G ⟶ (⟨(Stacks.Coherent.affineTilde X).obj M₀, hTcoh⟩ :
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :=
    ObjectProperty.homMk (affineSectionsHomLift (δ.toLinearMap.comp ψ)) with ha
  have hfac : ∀ s : Γ(G.obj, ⊤), topSectionsMap a s = δ (ψ s) := fun s =>
    affineSectionsHomLift_app (δ.toLinearMap.comp ψ) s
  have hkerfin : Module.Finite Γ(X, ⊤) (LinearMap.ker ψ) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  obtain ⟨nK, hnK⟩ := exists_pow_smul_top_eq_bot_of_isIPowerTorsion I
    I.fg_of_isNoetherianRing (LinearMap.ker ψ) hK
  have hquotfin : Module.Finite Γ(X, ⊤) (M₀ ⧸ LinearMap.range ψ) :=
    Module.Finite.of_surjective (LinearMap.range ψ).mkQ (LinearMap.range ψ).mkQ_surjective
  obtain ⟨nC, hnC⟩ := exists_pow_smul_top_eq_bot_of_isIPowerTorsion I
    I.fg_of_isNoetherianRing (M₀ ⧸ LinearMap.range ψ) hC
  have hKbridge : ∃ n : ℕ, I ^ n • (⊤ : Submodule Γ(X, ⊤)
      (kernel ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map a.hom) :
        ModuleCat Γ(X, ⊤))) = ⊥ := by
    refine ⟨nK, smul_top_evaluationKernel_eq_bot a.hom (I ^ nK) ?_⟩
    intro r hr x hx
    have hd : δ (ψ x) = 0 := (hfac x).symm.trans hx
    have hm : ψ x = 0 := δ.injective (hd.trans (map_zero δ).symm)
    exact congrArg Subtype.val ((ideal_smul_top_eq_bot_iff (I ^ nK)).1 hnK r hr
      ⟨x, LinearMap.mem_ker.2 hm⟩)
  have hCbridge : ∃ n : ℕ, ∀ r ∈ I ^ n,
      ∀ y : Γ((⟨(Stacks.Coherent.affineTilde X).obj M₀, hTcoh⟩ :
        AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf).obj, ⊤),
        ∃ x : Γ(G.obj, ⊤), Scheme.Modules.Hom.app a.hom ⊤ x = r • y := by
    refine ⟨nC, fun r hr y => ?_⟩
    have h0 := (ideal_smul_top_eq_bot_iff (I ^ nC)).1 hnC r hr
      (Submodule.Quotient.mk (δ.symm y))
    obtain ⟨s, hs⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range ψ)).1 h0
    refine ⟨s, ?_⟩
    have h2 : δ (ψ s) = r • y := by
      rw [hs, map_smul, δ.apply_symm_apply]
    exact (hfac s).trans h2
  obtain ⟨hk, hc⟩ := isPowerAnnihilated_kernel_cokernel_of_sections I a hKbridge hCbridge
  exact ⟨_, a, δ, hfac, hk, hc⟩

/-! ### The comparison of the completed modules produced by a codescent -/

/-- The completed module of the completion of a coherent module, read as the extension of scalars
of its global sections: the completed module of `G^∧` is the `I`-adic completion of `Γ(G, ⊤)`, and
that completion is the extension of scalars of `Γ(G, ⊤)` because `Γ(G, ⊤)` is finite over the
Noetherian ring `Γ(X, ⊤)`. -/
public noncomputable def completionSectionsTensorEquiv
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤)] :
    TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤))
        (ModuleCat.of Γ(X, ⊤) Γ(G.obj, ⊤)) ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      Stacks.Coherent.completedModuleAsBase X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G) :=
  (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I
    (ModuleCat.of Γ(X, ⊤) Γ(G.obj, ⊤))).trans (completionModuleEquivₛ X I G)

/-- The identification of the completed module of `G^∧` with an extension of scalars carries the
element `1 ⊗ s` to the image of the global section `s`. -/
public theorem completionSectionsTensorEquiv_tmul
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤)] (s : Γ(G.obj, ⊤)) :
    completionSectionsTensorEquiv X I G ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) =
      completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s) := by
  exact completionModuleEquivₛ_ofTensorProductEquiv_one_tmul X I G s

/-- **Stacks 087W on the output of a codescent.** The isomorphism of completed modules attached to
a codescent: the completed module of `(F_n)` is the extension of scalars of `M₀` through `e`, that
extension of scalars is the `I`-adic completion of `M₀`, and the identification `δ` of `M₀` with
`Γ(F, ⊤)` turns the latter into the completed module of `F^∧`. -/
public noncomputable def codescentCompletedModuleEquiv
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (M₀ : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M₀]
    (δ : M₀ ≃ₗ[Γ(X, ⊤)] Γ(F.obj, ⊤))
    (e : TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) M₀ ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      (completedFGModule X I Fsys).obj) :
    (completedFGModule X I Fsys).obj ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      (completedFGModule X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F)).obj :=
  e.symm.trans (((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀).trans
    (AdicCompletion.congr I δ)).trans (completionModuleEquivₛ X I F))

/-- The isomorphism of completed modules attached to a codescent carries the image of `1 ⊗ m`
under `e` to the image of the global section `δ m`. -/
public theorem codescentCompletedModuleEquiv_apply
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (M₀ : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M₀]
    (δ : M₀ ≃ₗ[Γ(X, ⊤)] Γ(F.obj, ⊤))
    (e : TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) M₀ ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      (completedFGModule X I Fsys).obj) (m : M₀) :
    codescentCompletedModuleEquiv X I Fsys F M₀ δ e
        (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m)) =
      completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) (δ m)) := by
  change completionModuleEquivₛ X I F (AdicCompletion.congr I δ
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀
      (e.symm (e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m))))) = _
  rw [e.symm_apply_apply, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul, one_smul, AdicCompletion.congr_apply,
    AdicCompletion.map_of, completionModuleEquivₛ_apply]
  rfl

/-- The inverse of the isomorphism of completed modules attached to a codescent carries the image
of the global section `δ m` to the image of `1 ⊗ m` under `e`. -/
public theorem codescentCompletedModuleEquiv_symm_apply
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (M₀ : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M₀]
    (δ : M₀ ≃ₗ[Γ(X, ⊤)] Γ(F.obj, ⊤))
    (e : TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) M₀ ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      (completedFGModule X I Fsys).obj) (m : M₀) :
    (codescentCompletedModuleEquiv X I Fsys F M₀ δ e).symm
        (completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) (δ m))) =
      e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) :=
  (codescentCompletedModuleEquiv X I Fsys F M₀ δ e).symm_apply_eq.2
    (codescentCompletedModuleEquiv_apply X I Fsys F M₀ δ e m).symm

/-- **The map of completed modules induced by `α` is the completion of `a` read through the
codescent.** Both sides are maps over the completed ring out of the completed module of `G^∧`,
which is the extension of scalars of `Γ(G, ⊤)`, so they agree as soon as they agree on the
elements `1 ⊗ s`. There the left-hand side is computed by the compatibility clause of the
codescent and the right-hand side by the naturality of the identification of a completion with an
adic completion together with the identification of `ψ` with the map of global sections of `a`. -/
public theorem completedModuleMap_eq_codescent
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤)]
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (α : ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj ⟶ Fsys.obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : G ⟶ F)
    (M₀ : ModuleCat.{u} Γ(X, ⊤)) [Module.Finite Γ(X, ⊤) M₀]
    (ψ : Γ(G.obj, ⊤) →ₗ[Γ(X, ⊤)] M₀) (δ : M₀ ≃ₗ[Γ(X, ⊤)] Γ(F.obj, ⊤))
    (e : TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) M₀ ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      (completedFGModule X I Fsys).obj)
    (hfac : ∀ s : Γ(G.obj, ⊤), topSectionsMap a s = δ (ψ s))
    (hcompat : ∀ s : Γ(G.obj, ⊤),
      completedModuleMap X I (ObjectProperty.homMk α)
          (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s)) =
        e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] ψ s))
    (w : Stacks.Coherent.completedModuleAsBase X I
      ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G)) :
    completedModuleMap X I (ObjectProperty.homMk α) w =
      (codescentCompletedModuleEquiv X I Fsys F M₀ δ e).symm
        (completedModuleMap X I
          ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a) w) := by
  set Θ := codescentCompletedModuleEquiv X I Fsys F M₀ δ e with hΘdef
  set Eg := completionSectionsTensorEquiv X I G with hEgdef
  have hL : (completedModuleMap X I (ObjectProperty.homMk α)).comp Eg.toLinearMap =
      (Θ.symm.toLinearMap.comp (completedModuleMap X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a))).comp
          Eg.toLinearMap := by
    refine tensorProduct_linearMap_ext _ _ fun s => ?_
    have hnat := completionModuleEquiv_naturality X I a (AdicCompletion.of I Γ(G.obj, ⊤) s)
    rw [AdicCompletion.map_of, hfac s] at hnat
    have hnat' : completedModuleMap X I
          ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)
          (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s)) =
        completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) (δ (ψ s))) := hnat
    have hlhs : completedModuleMap X I (ObjectProperty.homMk α)
          (Eg ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s)) =
        e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] ψ s) :=
      (congrArg (completedModuleMap X I (ObjectProperty.homMk α))
        (completionSectionsTensorEquiv_tmul X I G s)).trans (hcompat s)
    have hrhs : Θ.symm (completedModuleMap X I
          ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)
          (Eg ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s))) =
        e ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] ψ s) :=
      (congrArg Θ.symm
        ((congrArg (completedModuleMap X I
          ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a))
            (completionSectionsTensorEquiv_tmul X I G s)).trans hnat')).trans
        (codescentCompletedModuleEquiv_symm_apply X I Fsys F M₀ δ e (ψ s))
    exact hlhs.trans hrhs.symm
  obtain ⟨t, rfl⟩ := Eg.surjective w
  exact LinearMap.congr_fun hL t

/-! ### The affine case of Stacks 0889 (2) -/

/-- **The affine case of Stacks 0889 (2).** Let `X` be an affine Noetherian scheme,
`I ⊆ Γ(X, ⊤)` an ideal, `𝓘` the quasi-coherent ideal sheaf it determines, `G` a coherent
`𝒪_X`-module and `(F_n)` a coherent adic system along `𝓘`. A morphism `α : G^∧ ⟶ (F_n)` whose
levelwise kernels and cokernels are annihilated by one power of `𝓘` is the completion of a
morphism of coherent modules *out of* `G`: there are a coherent module `F`, a morphism
`a : G ⟶ F` whose kernel and cokernel are annihilated by a power of `𝓘`, and an isomorphism
`β : F^∧ ≅ (F_n)` with `α = β ∘ a^∧`.

Everything analytic has already happened in
`Stacks.Algebraization.affine_exists_module_algebraization_dual`, which produces the finite module
`M₀`, the map `ψ : Γ(G, ⊤) → M₀`, and the identification `e` of the extension of scalars of `M₀`
with the completed module of `(F_n)`. The map `ψ` becomes a morphism of coherent modules by
`Stacks.Algebraization.exists_coherent_realization_dual`, the isomorphism `β` is produced from `e`
by the equivalence of tag 087W applied to
`Stacks.Algebraization.codescentCompletedModuleEquiv`, and the factorization is
`Stacks.Algebraization.completedModuleMap_eq_codescent` read through that equivalence. -/
public theorem affine_exists_algebraization_dual (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (α : ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower (Scheme.IdealSheafData.ofIdealTop I) α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : G ⟶ F)
      (β : ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F).obj ≅ Fsys.obj),
      α = ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a).hom ≫ β.hom ∧
        IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
            (kernel (C := X.Modules) a.hom) ∧
          IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
            (cokernel (C := X.Modules) a.hom) := by
  have hGcoh : G.obj.IsCoherent := G.property
  have hNfin : Module.Finite Γ(X, ⊤) Γ(G.obj, ⊤) :=
    Stacks.Coherent.coherentAdicTerm_finiteSections X G.obj
  obtain ⟨M₀, ψ, e, hM₀, hKψ, hCψ, hcompat⟩ :=
    affine_exists_module_algebraization_dual X I G Fsys α hα
  obtain ⟨F, a, δ, hfac, hker, hcok⟩ := exists_coherent_realization_dual X I G M₀ ψ hKψ hCψ
  set E := Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I
  set Θ : completedFGModule X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F) ≅
      completedFGModule X I Fsys :=
    ObjectProperty.isoMk _
      (codescentCompletedModuleEquiv X I Fsys F M₀ δ e).symm.toModuleIso
  set βsys : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ≅ Fsys :=
    E.functor.preimageIso Θ
  have hmapβ : E.functor.map βsys.hom = Θ.hom := E.functor.map_preimage Θ.hom
  have hmain : (ObjectProperty.homMk α :
      (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G ⟶ Fsys) =
      (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a ≫ βsys.hom := by
    refine E.functor.map_injective ?_
    rw [E.functor.map_comp, hmapβ]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun w =>
      completedModuleMap_eq_codescent X I G Fsys α F a M₀ ψ δ e hfac hcompat w
  refine ⟨F, a, ⟨βsys.hom.hom, βsys.inv.hom,
    ObjectProperty.isoHom_inv_id_hom βsys, ObjectProperty.isoInv_hom_id_hom βsys⟩,
    ?_, hker, hcok⟩
  exact congrArg (fun k : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G ⟶
    Fsys => k.hom) hmain

/-! ### Functoriality of the completed module -/

/-- The completed module of a composite of morphisms of coherent adic systems is the composite of
the completed modules. -/
public theorem completedModuleMap_comp
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G H : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (f : F ⟶ G) (g : G ⟶ H) (x : Stacks.Coherent.completedModuleAsBase X I F) :
    completedModuleMap X I (f ≫ g) x =
      completedModuleMap X I g (completedModuleMap X I f x) :=
  congrArg (fun k : completedFGModule X I F ⟶ completedFGModule X I H => k.hom.hom x)
    ((Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I).functor.map_comp f g)

/-- The completed module of the identity is the identity. -/
public theorem completedModuleMap_id
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (x : Stacks.Coherent.completedModuleAsBase X I F) :
    completedModuleMap X I (𝟙 F) x = x :=
  congrArg (fun k : completedFGModule X I F ⟶ completedFGModule X I F => k.hom.hom x)
    ((Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I).functor.map_id F)

/-- An isomorphism of coherent adic systems induces an isomorphism of their completed modules. -/
public noncomputable def completedModuleEquivOfIso
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (i : F ≅ G) :
    Stacks.Coherent.completedModuleAsBase X I F ≃ₗ[AdicCompletion I Γ(X, ⊤)]
      Stacks.Coherent.completedModuleAsBase X I G :=
  LinearEquiv.ofLinearMap (completedModuleMap X I i.hom) (completedModuleMap X I i.inv)
    (LinearMap.ext fun y =>
      ((completedModuleMap_comp X I i.inv i.hom y).symm.trans
        (congrArg (fun k : G ⟶ G => completedModuleMap X I k y) i.inv_hom_id)).trans
        (completedModuleMap_id X I G y))
    (LinearMap.ext fun x =>
      ((completedModuleMap_comp X I i.hom i.inv x).symm.trans
        (congrArg (fun k : F ⟶ F => completedModuleMap X I k x) i.hom_inv_id)).trans
        (completedModuleMap_id X I F x))

/-- The isomorphism of completed modules induced by an isomorphism of coherent adic systems acts
by the completed module of its underlying morphism. -/
public theorem completedModuleEquivOfIso_apply
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (i : F ≅ G) (x : Stacks.Coherent.completedModuleAsBase X I F) :
    completedModuleEquivOfIso X I i x = completedModuleMap X I i.hom x := rfl

/-- The map of global sections of a composite of morphisms of coherent modules is the composite of
the maps of global sections. -/
public theorem topSectionsMap_comp {X : Scheme.{u}}
    {F G H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (f : F ⟶ G) (g : G ⟶ H) (s : Γ(F.obj, ⊤)) :
    topSectionsMap (f ≫ g) s = topSectionsMap g (topSectionsMap f s) := rfl

/-- The map of global sections of the identity is the identity. -/
public theorem topSectionsMap_id {X : Scheme.{u}}
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (s : Γ(F.obj, ⊤)) :
    topSectionsMap (𝟙 F) s = s := rfl

/-- **Stacks 0880, naturality on global sections.** The completed module of the completion of a
morphism of coherent modules carries the image of a global section to the image of its image. -/
public theorem completedModuleMap_completionFunctor_map_of
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (s : Γ(F.obj, ⊤)) :
    completedModuleMap X I ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a)
        (completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) s)) =
      completionModuleEquiv X I G
        (AdicCompletion.of I Γ(G.obj, ⊤) (topSectionsMap a s)) := by
  have hnat := completionModuleEquiv_naturality X I a (AdicCompletion.of I Γ(F.obj, ⊤) s)
  rwa [AdicCompletion.map_of] at hnat

/-- **Two morphisms out of the completion of a coherent module agree once their completed modules
agree on the images of global sections.** The completed module of `F^∧` is the `I`-adic completion
of `Γ(F, ⊤)`, the completed module of the target is `I`-adically complete hence Hausdorff, and the
equivalence of tag 087W is faithful. -/
public theorem completedModuleHom_ext_of_sections
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (f₁ f₂ : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ⟶ Fsys)
    (h : ∀ m : Γ(F.obj, ⊤),
      completedModuleMap X I f₁
          (completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) m)) =
        completedModuleMap X I f₂
          (completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) m))) :
    f₁ = f₂ := by
  have hH : IsAdicComplete I (Stacks.Coherent.completedModuleAsBase X I Fsys) :=
    isAdicComplete_completedModuleAsBase X I Fsys
  have heq := linearMap_eq_of_comp_of I I.fg_of_isNoetherianRing
    ((completedModuleHomBase X I f₁).hom.comp (completionModuleEquiv X I F).toLinearMap)
    ((completedModuleHomBase X I f₂).hom.comp (completionModuleEquiv X I F).toLinearMap) h
  refine (Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat X I).functor.map_injective ?_
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun w => ?_
  obtain ⟨z, rfl⟩ := (completionModuleEquiv X I F).surjective w
  exact LinearMap.congr_fun heq z

/-! ### Comparing two algebraizations -/

/-- The extension of scalars of the global sections of a coherent module `F`, identified with the
completed module of a coherent adic system through an isomorphism `F^∧ ≅ (F_n)`. -/
public noncomputable def completionTensorSystemEquiv
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(F.obj, ⊤)]
    (i : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ≅ Fsys) :
    TensorProduct Γ(X, ⊤) (AdicCompletion I Γ(X, ⊤)) Γ(F.obj, ⊤)
        ≃ₗ[AdicCompletion I Γ(X, ⊤)] Stacks.Coherent.completedModuleAsBase X I Fsys :=
  (completionSectionsTensorEquiv X I F).trans (completedModuleEquivOfIso X I i)

/-- The identification of the extension of scalars of `Γ(F, ⊤)` with the completed module of
`(F_n)` carries `1 ⊗ m` to the image of the global section `m`. -/
public theorem completionTensorSystemEquiv_tmul
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(F.obj, ⊤)]
    (i : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ≅ Fsys)
    (m : Γ(F.obj, ⊤)) :
    completionTensorSystemEquiv X I F i ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) =
      completedModuleMap X I i.hom
        (completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) m)) :=
  congrArg (completedModuleEquivOfIso X I i) (completionSectionsTensorEquiv_tmul X I F m)

/-- **The affine-sections form of annihilation of the sheaf kernel at `⊤`.** If a power of `𝓘`
annihilates the kernel of a morphism of coherent modules on an affine scheme, the kernel of the
map of global sections is `I`-power torsion. -/
public theorem isIPowerTorsion_ker_topSectionsMap
    (X : Scheme.{u}) [IsAffine X] (I : Ideal Γ(X, ⊤))
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (hK : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (kernel (C := X.Modules) a.hom)) :
    IsIPowerTorsion Γ(X, ⊤) (LinearMap.ker (topSectionsMap a)) I := by
  have h := isIPowerTorsion_ker_affineSectionMap (Scheme.IdealSheafData.ofIdealTop I) a.hom hK
    ⟨⊤, isAffineOpen_top X⟩
  rwa [Stacks.Coherent.ofIdealTop_ideal_top X I] at h

/-- **The affine-sections form of annihilation of the sheaf cokernel at `⊤`.** If a power of `𝓘`
annihilates the cokernel of a morphism of coherent modules on an affine scheme, the cokernel of
the map of global sections is `I`-power torsion. -/
public theorem isIPowerTorsion_cokernel_topSectionsMap
    (X : Scheme.{u}) [IsAffine X] (I : Ideal Γ(X, ⊤))
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : F ⟶ G)
    (hC : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (cokernel (C := X.Modules) a.hom)) :
    IsIPowerTorsion Γ(X, ⊤) (Γ(G.obj, ⊤) ⧸ LinearMap.range (topSectionsMap a)) I := by
  have hFc : F.obj.IsCoherent := F.property
  have hGc : G.obj.IsCoherent := G.property
  have hFq : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hGq : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  have h := isIPowerTorsion_cokernel_affineSectionMap (Scheme.IdealSheafData.ofIdealTop I) a.hom
    hC ⟨⊤, isAffineOpen_top X⟩
  rwa [Stacks.Coherent.ofIdealTop_ideal_top X I] at h

/-- **Global sections are fully faithful on coherent modules over an affine scheme.** An
isomorphism of the global sections of two coherent modules is the map of global sections of an
isomorphism of the modules. -/
public noncomputable def affineSectionsIsoLift {X : Scheme.{u}} [IsAffine X]
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (d : Γ(F.obj, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(F'.obj, ⊤)) : F ≅ F' := by
  have hFc : F.obj.IsCoherent := F.property
  have hF'c : F'.obj.IsCoherent := F'.property
  have hFq : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hF'q : F'.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F'.obj
  have h1 : affineSectionsHomLift d.toLinearMap ≫ affineSectionsHomLift d.symm.toLinearMap =
      𝟙 F.obj := by
    refine Stacks.Coherent.affineQuasicoherentHom_ext
      (ModuleCat.hom_ext (LinearMap.ext fun m => ?_))
    have hl : ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
          (affineSectionsHomLift d.toLinearMap ≫
            affineSectionsHomLift d.symm.toLinearMap)).hom m =
        (affineSectionsHomLift d.symm.toLinearMap).app ⊤
          ((affineSectionsHomLift d.toLinearMap).app ⊤ m) := rfl
    have hr : ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
          (𝟙 F.obj)).hom m = m := rfl
    refine hl.trans (Eq.trans ?_ hr.symm)
    refine Eq.trans (congrArg (fun z => (affineSectionsHomLift d.symm.toLinearMap).app ⊤ z)
      (affineSectionsHomLift_app d.toLinearMap m)) ?_
    exact (affineSectionsHomLift_app d.symm.toLinearMap (d m)).trans (d.symm_apply_apply m)
  have h2 : affineSectionsHomLift d.symm.toLinearMap ≫ affineSectionsHomLift d.toLinearMap =
      𝟙 F'.obj := by
    refine Stacks.Coherent.affineQuasicoherentHom_ext
      (ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
    have hl : ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
          (affineSectionsHomLift d.symm.toLinearMap ≫
            affineSectionsHomLift d.toLinearMap)).hom y =
        (affineSectionsHomLift d.toLinearMap).app ⊤
          ((affineSectionsHomLift d.symm.toLinearMap).app ⊤ y) := rfl
    have hr : ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
          (𝟙 F'.obj)).hom y = y := rfl
    refine hl.trans (Eq.trans ?_ hr.symm)
    refine Eq.trans (congrArg (fun z => (affineSectionsHomLift d.toLinearMap).app ⊤ z)
      (affineSectionsHomLift_app d.symm.toLinearMap y)) ?_
    exact (affineSectionsHomLift_app d.toLinearMap (d.symm y)).trans (d.apply_symm_apply y)
  exact ObjectProperty.isoMk _ ⟨affineSectionsHomLift d.toLinearMap,
    affineSectionsHomLift d.symm.toLinearMap, h1, h2⟩

/-- The isomorphism of coherent modules lifting an isomorphism of global sections acts on global
sections by that isomorphism. -/
public theorem affineSectionsIsoLift_topSectionsMap {X : Scheme.{u}} [IsAffine X]
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (d : Γ(F.obj, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(F'.obj, ⊤)) (m : Γ(F.obj, ⊤)) :
    topSectionsMap (affineSectionsIsoLift F F' d).hom m = d m := by
  have hFc : F.obj.IsCoherent := F.property
  have hF'c : F'.obj.IsCoherent := F'.property
  have hFq : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hF'q : F'.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F'.obj
  exact affineSectionsHomLift_app d.toLinearMap m

/-- The isomorphism of global sections attached to an isomorphism of coherent modules. -/
public noncomputable def topSectionsEquivOfIso {X : Scheme.{u}}
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (d : F ≅ F') :
    Γ(F.obj, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(F'.obj, ⊤) :=
  LinearEquiv.ofLinearMap (topSectionsMap d.hom) (topSectionsMap d.inv)
    (LinearMap.ext fun y => ((topSectionsMap_comp d.inv d.hom y).symm.trans
      (congrArg (fun k : F' ⟶ F' => topSectionsMap k y) d.inv_hom_id)).trans
      (topSectionsMap_id F' y))
    (LinearMap.ext fun x => ((topSectionsMap_comp d.hom d.inv x).symm.trans
      (congrArg (fun k : F ⟶ F => topSectionsMap k x) d.hom_inv_id)).trans
      (topSectionsMap_id F x))

/-- The isomorphism of global sections attached to an isomorphism of coherent modules acts by the
map of global sections of its underlying morphism. -/
public theorem topSectionsEquivOfIso_apply {X : Scheme.{u}}
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (d : F ≅ F')
    (m : Γ(F.obj, ⊤)) : topSectionsEquivOfIso d m = topSectionsMap d.hom m := rfl

/-- The completed module of the composite of the completion of `a` with an isomorphism `i` carries
the image of a global section `s` of `G` to the image of `1 ⊗ a s` under the identification of the
extension of scalars of `Γ(F, ⊤)` with the completed module of the system. -/
private theorem completedModuleMap_completionFunctor_map_comp_eq_tmul
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    [Module.Finite Γ(X, ⊤) Γ(F.obj, ⊤)] (a : G ⟶ F)
    (i : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ≅ Fsys)
    (s : Γ(G.obj, ⊤)) :
    completedModuleMap X I
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a ≫ i.hom)
        (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s)) =
      completionTensorSystemEquiv X I F i
        ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] topSectionsMap a s) :=
  ((completedModuleMap_comp X I
    ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a) i.hom _).trans
    (congrArg (completedModuleMap X I i.hom)
      (completedModuleMap_completionFunctor_map_of X I a s))).trans
    (completionTensorSystemEquiv_tmul X I F i (topSectionsMap a s)).symm

/-- **The two identifications of the formal system attached to two algebraizations agree on the
image of a global section of `G`.** Both carry the image of `s` to the value at `1 ⊗ s` of the map
of completed modules induced by `α`. -/
public theorem completionTensorSystemEquiv_compat
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(F.obj, ⊤)] [Module.Finite Γ(X, ⊤) Γ(F'.obj, ⊤)]
    (a : G ⟶ F) (a' : G ⟶ F')
    (i : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ≅ Fsys)
    (i' : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F' ≅ Fsys)
    (hmor : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a ≫ i.hom =
      (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a' ≫ i'.hom)
    (s : Γ(G.obj, ⊤)) :
    completionTensorSystemEquiv X I F' i'
        ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] topSectionsMap a' s) =
      completionTensorSystemEquiv X I F i
        ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] topSectionsMap a s) := by
  have h1 := completedModuleMap_completionFunctor_map_comp_eq_tmul X I a' i' s
  have h2 := completedModuleMap_completionFunctor_map_comp_eq_tmul X I a i s
  refine h1.symm.trans (Eq.trans ?_ h2)
  exact congrArg (fun k : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G ⟶
    Fsys => completedModuleMap X I k
      (completionModuleEquiv X I G (AdicCompletion.of I Γ(G.obj, ⊤) s))) hmor.symm

/-- **An isomorphism of coherent modules compatible with the two identifications of the formal
system is compatible with the two identifications of the completed module.** This is the second
clause of the module-level uniqueness statement, read off from the second clause of the sheaf-level
one. -/
public theorem completionTensorSystemEquiv_baseChange_eq
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    {Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I)}
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    [Module.Finite Γ(X, ⊤) Γ(F.obj, ⊤)] [Module.Finite Γ(X, ⊤) Γ(F'.obj, ⊤)]
    (i : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ≅ Fsys)
    (i' : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F' ≅ Fsys)
    (d : F ≅ F')
    (hd : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map d.hom ≫ i'.hom =
      i.hom) :
    (completionTensorSystemEquiv X I F' i').toLinearMap.comp
        (LinearMap.baseChange (AdicCompletion I Γ(X, ⊤))
          (topSectionsEquivOfIso d).toLinearMap) =
      (completionTensorSystemEquiv X I F i).toLinearMap := by
  refine tensorProduct_linearMap_ext _ _ fun m => ?_
  have hb : LinearMap.baseChange (AdicCompletion I Γ(X, ⊤))
        (topSectionsEquivOfIso d).toLinearMap
        ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) =
      (1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] topSectionsMap d.hom m :=
    LinearMap.baseChange_tmul _ _ _
  have hid : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map (𝟙 F) ≫ i.hom =
      i.hom :=
    (congrArg (fun k : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ⟶
        (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F => k ≫ i.hom)
      ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map_id F)).trans
      (Category.id_comp i.hom)
  exact (congrArg (completionTensorSystemEquiv X I F' i') hb).trans
    (completionTensorSystemEquiv_compat X I F F F' (𝟙 F) d.hom i i' (hid.trans hd.symm) m)

/-! ### The uniqueness clause of the affine case of Stacks 0889 (2) -/

/-- Two morphisms of quasi-coherent modules over an affine scheme are equal once they agree on
global sections. -/
private theorem hom_ext_of_app_top {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {f g : M ⟶ N}
    (h : ∀ s : Γ(M, ⊤), f.app ⊤ s = g.app ⊤ s) : f = g :=
  Stacks.Coherent.affineQuasicoherentHom_ext (ModuleCat.hom_ext (LinearMap.ext h))

/-- **The uniqueness clause of the affine case of Stacks 0889 (2).** On an affine Noetherian
scheme, two algebraizations of the same datum `(G, (F_n), α)` out of `G`, with the kernel and the
cokernel of both comparison maps annihilated by a power of the ideal sheaf attached to `I`, are
related by a unique isomorphism compatible with the maps out of `G` and with the two
identifications of the formal system.

The comparison happens at the level of modules. Global sections carry the two algebraizations to
two codescents of one and the same map `A^∧ ⊗_A Γ(G, ⊤) → M'`: the identifications of the
extensions of scalars of `Γ(F, ⊤)` and of `Γ(F', ⊤)` with the completed module of `(F_n)` agree
after composing with the base changes of the two maps of global sections, because the two
factorizations of `α` do. The kernel and the cokernel of each map of global sections are
`I`-power torsion because the corresponding sheaf kernel and sheaf cokernel are annihilated by a
power of `𝓘`, so `AdicCompletion.codescent_unique` applies and produces a unique isomorphism
`Γ(F, ⊤) ≅ Γ(F', ⊤)` compatible with the two maps out of `Γ(G, ⊤)` and with the two
identifications. Global sections are fully faithful on coherent modules over an affine scheme and
the equivalence of tag 087W is faithful, so that unique isomorphism of modules is the unique
isomorphism of sheaves the statement asks for. -/
public theorem affine_unique_algebraization_dual (X : Scheme.{u}) [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] (I : Ideal Γ(X, ⊤))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (α : ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj G).obj ⟶ Fsys.obj)
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (a : G ⟶ F) (a' : G ⟶ F')
    (β : ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F).obj ≅ Fsys.obj)
    (β' : ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F').obj ≅ Fsys.obj)
    (hα : α = ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a).hom ≫ β.hom)
    (hα' : α = ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a').hom ≫ β'.hom)
    (hKa : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (kernel (C := X.Modules) a.hom))
    (hCa : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (cokernel (C := X.Modules) a.hom))
    (hKa' : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (kernel (C := X.Modules) a'.hom))
    (hCa' : IsPowerAnnihilated (Scheme.IdealSheafData.ofIdealTop I)
      (cokernel (C := X.Modules) a'.hom)) :
    ∃! d : F ≅ F',
      a ≫ d.hom = a' ∧
        ((completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map d.hom).hom ≫ β'.hom =
          β.hom := by
  have hGc : G.obj.IsCoherent := G.property
  have hFc : F.obj.IsCoherent := F.property
  have hF'c : F'.obj.IsCoherent := F'.property
  have hGq : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  have hFq : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hF'q : F'.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F'.obj
  have hM₁ : Module.Finite Γ(X, ⊤) Γ(F.obj, ⊤) :=
    Stacks.Coherent.coherentAdicTerm_finiteSections X F.obj
  have hM₂ : Module.Finite Γ(X, ⊤) Γ(F'.obj, ⊤) :=
    Stacks.Coherent.coherentAdicTerm_finiteSections X F'.obj
  let i : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ≅ Fsys :=
    ObjectProperty.isoMk _ β
  let i' : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F' ≅ Fsys :=
    ObjectProperty.isoMk _ β'
  let e₁ := completionTensorSystemEquiv X I F i
  let e₂ := completionTensorSystemEquiv X I F' i'
  have hmor : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a ≫ i.hom =
      (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map a' ≫ i'.hom :=
    ObjectProperty.hom_ext _ (hα.symm.trans hα')
  have hcompat := completionTensorSystemEquiv_compat X I G F F' a a' i i' hmor
  have hbase : e₂.toLinearMap.comp
        (LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) (topSectionsMap a')) =
      e₁.toLinearMap.comp
        (LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) (topSectionsMap a)) := by
    refine tensorProduct_linearMap_ext _ _ fun s => ?_
    have hb2 : LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) (topSectionsMap a')
          ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) =
        (1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] topSectionsMap a' s :=
      LinearMap.baseChange_tmul _ _ _
    have hb1 : LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) (topSectionsMap a)
          ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] s) =
        (1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] topSectionsMap a s :=
      LinearMap.baseChange_tmul _ _ _
    exact ((congrArg e₂ hb2).trans (hcompat s)).trans (congrArg e₁ hb1).symm
  obtain ⟨dm, ⟨hdm1, hdm2⟩, hdmuniq⟩ :=
    AdicCompletion.codescent_unique.{u, u} I
      (e₁.toLinearMap.comp
        (LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) (topSectionsMap a)))
      (topSectionsMap a) (topSectionsMap a') e₁ e₂ rfl hbase
      (isIPowerTorsion_ker_topSectionsMap X I a hKa)
      (isIPowerTorsion_cokernel_topSectionsMap X I a hCa)
      (isIPowerTorsion_ker_topSectionsMap X I a' hKa')
      (isIPowerTorsion_cokernel_topSectionsMap X I a' hCa')
  have hd₀sec : ∀ m : Γ(F.obj, ⊤),
      topSectionsMap (affineSectionsIsoLift F F' dm).hom m = dm m :=
    fun m => affineSectionsIsoLift_topSectionsMap F F' dm m
  have hc1 : a ≫ (affineSectionsIsoLift F F' dm).hom = a' := by
    refine ObjectProperty.hom_ext _ (hom_ext_of_app_top fun s => ?_)
    exact (hd₀sec (topSectionsMap a s)).trans (LinearMap.congr_fun hdm1 s)
  have hc2sys : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map
      (affineSectionsIsoLift F F' dm).hom ≫ i'.hom = i.hom := by
    refine completedModuleHom_ext_of_sections X I F _ _ fun m => ?_
    have hL := completedModuleMap_completionFunctor_map_comp_eq_tmul X I
      (affineSectionsIsoLift F F' dm).hom i' m
    have hR : completedModuleMap X I i.hom
          (completionModuleEquiv X I F (AdicCompletion.of I Γ(F.obj, ⊤) m)) =
        e₁ ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) :=
      (completionTensorSystemEquiv_tmul X I F i m).symm
    have hb : LinearMap.baseChange (AdicCompletion I Γ(X, ⊤)) dm.toLinearMap
          ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) =
        (1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] dm m :=
      LinearMap.baseChange_tmul _ _ _
    have hmid : e₂ ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] dm m) =
        e₁ ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m) :=
      (congrArg e₂ hb).symm.trans
        (LinearMap.congr_fun hdm2 ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] m))
    refine hL.trans (Eq.trans ?_ hR.symm)
    exact (congrArg (fun z : Γ(F'.obj, ⊤) =>
      e₂ ((1 : AdicCompletion I Γ(X, ⊤)) ⊗ₜ[Γ(X, ⊤)] z)) (hd₀sec m)).trans hmid
  refine ⟨affineSectionsIsoLift F F' dm, ⟨hc1,
    congrArg (fun k : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).obj F ⟶
      Fsys => k.hom) hc2sys⟩, ?_⟩
  rintro d ⟨hd1, hd2⟩
  have hd2sys : (completionFunctor X (Scheme.IdealSheafData.ofIdealTop I)).map d.hom ≫ i'.hom =
      i.hom := ObjectProperty.hom_ext _ hd2
  have hm1 : (topSectionsEquivOfIso d).toLinearMap.comp (topSectionsMap a) =
      topSectionsMap a' :=
    LinearMap.ext fun s => (topSectionsMap_comp a d.hom s).symm.trans
      (congrArg (fun k : G ⟶ F' => topSectionsMap k s) hd1)
  have hdd : topSectionsEquivOfIso d = dm := hdmuniq _
    ⟨hm1, completionTensorSystemEquiv_baseChange_eq X I F F' i i' d hd2sys⟩
  refine Iso.ext (ObjectProperty.hom_ext _ (hom_ext_of_app_top fun m => ?_))
  exact (congrArg (fun k : Γ(F.obj, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(F'.obj, ⊤) => k m) hdd).trans
    (hd₀sec m).symm

end Stacks.Algebraization

end
