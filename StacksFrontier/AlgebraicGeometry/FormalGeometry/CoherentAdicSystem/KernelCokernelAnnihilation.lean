module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Cokernel
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LiftedQuotientTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Exactness

/-!
# Annihilation of the kernel and the cokernel of a map of coherent modules, read off the
completions

Let `X` be a Noetherian scheme and let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves. The proof of
[Stacks, Tag 088A] needs to carry the hypothesis of Tag 0889 — annihilation of the levelwise
kernels and cokernels of a comparison map by a power of `𝒦` — *backwards* along completion: from
the completion `a ^∧_ℐ` of a map `a : M ⟶ N` of coherent `𝒪_X`-modules annihilated by `𝒦 ᵉ⁺¹` to
`a` itself.

The engine for a single module is
`Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion`. What this file adds is the two
wrappers that make it apply to a kernel and to a cokernel.

The first is a statement about the abelian structure of `Coh(X, ℐ)`. The kernel there is *not*
the levelwise kernel — it is the system of stable kernel images of
`Stacks.Coherent.coherentAdicKernel` — so annihilation of the levelwise kernels of a morphism
does not immediately give annihilation of the terms of the kernel. It does give it after one
step: the terms of the kernel are adic quotients of the stable kernel images
(`Stacks.Coherent.kernelImageQuotients_eventuallyConstant`), a stable kernel image is a quotient
of a levelwise kernel, and annihilation passes along epimorphisms and quotients. The cokernel is
the levelwise cokernel (`Stacks.Coherent.coherentAdicCokernel`) and needs only that
identification.

The second is the passage between the two abelian structures that occur: kernels and cokernels
of maps of *coherent modules* are formed in `Coh(𝒪_X)`, and the inclusion of `Coh(𝒪_X)` into all
sheaves of modules preserves them, so their underlying sheaves are the kernel and the cokernel of
the underlying map.

## Main results

* `Stacks.Coherent.idealPowerMultiple_kernel_obj_eq_bot_of_termwise` — **the terms of the
  kernel in `Coh(X, ℐ)` are annihilated by any power of `𝒦` annihilating all the levelwise
  kernels.**
* `Stacks.Coherent.idealPowerMultiple_cokernel_obj_eq_bot_of_termwise` — the same for the cokernel.
* `Stacks.Coherent.idealPowerMultiple_kernel_cokernel_eq_bot_of_completion` — **completion
  reflects annihilation of kernels and cokernels on the `𝒦`-power-annihilated part**: if the
  levelwise kernels and cokernels of `a ^∧_ℐ` are annihilated by `𝒦 ᵗ` and both `M` and `N` are
  annihilated by `𝒦 ᵉ⁺¹`, then the kernel and the cokernel of `a` are annihilated by `𝒦 ᵗ⁺¹`.

## Implementation notes

The exponent rises by one in the last statement only because
`Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion` is stated for a positive exponent
`n + 1`; `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le` absorbs the difference.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice


namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- **Annihilation by a power of an ideal sheaf passes to subobjects.** If `ℐ ⁿ N` vanishes and
`M` injects into `N`, then `ℐ ⁿ M` vanishes: the condition is the vanishing of `a • x` for every
section `x` over an affine open, and the injection is injective and linear on those sections. -/
public theorem idealPowerMultiple_eq_bot_of_mono (I : X.IdealSheafData) {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (n : ℕ) (h : idealPowerMultiple I n N = ⊥) :
    idealPowerMultiple I n M = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun V a ha x => ?_
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, V.1) :=
    _root_.SheafOfModules.evaluation X.ringCatSheaf (op V.1)
  have : PreservesFiniteLimits E :=
    _root_.SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op V.1)
  have hinj : Function.Injective (E.map f).hom :=
    (ModuleCat.mono_iff_injective _).mp (E.map_mono f)
  refine hinj ?_
  exact (map_smul (E.map f).hom a x).trans
    ((affine_sections_annihilated_of_idealPowerMultiple_eq_bot h V ha _).trans
      (map_zero _).symm)

end Stacks.Algebraization

namespace Stacks.Coherent

/-! ### The terms of the kernel and the cokernel in `Coh(X, ℐ)` -/

section AdicKernelCokernel

variable {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
  {F G : CoherentAdicSystems I}

/-- **A stable kernel image is annihilated by whatever annihilates the levelwise kernels.** It is
the image of the kernel of `α` at the stabilization level, so an epimorphic image of it. -/
public theorem idealPowerMultiple_stableKernelImage_eq_bot (α : F ⟶ G) (t : ℕ)
    (hker : ∀ n : ℕ, idealPowerMultiple K t (kernel (α.hom.app (op n))) = ⊥) (m : ℕ) :
    idealPowerMultiple K t (stableKernelImage I α m) = ⊥ := by
  have : (F.obj.obj (op m)).IsCoherent := F.property.isCoherent m
  have : (F.obj.obj (op (kernelStableLevel I α m))).IsCoherent :=
    F.property.isCoherent _
  have : (G.obj.obj (op (kernelStableLevel I α m))).IsCoherent :=
    G.property.isCoherent _
  have : (kernel (α.hom.app (op (kernelStableLevel I α m)))).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel _
  have : (kernel (α.hom.app (op (kernelStableLevel I α m)))).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  set g : kernel (α.hom.app (op (kernelStableLevel I α m))) ⟶ F.obj.obj (op m) :=
    kernel.ι (α.hom.app (op (kernelStableLevel I α m))) ≫
      F.obj.map (homOfLE (le_kernelStableLevel I α m)).op with hg
  have : (cokernel g).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel g
  have : (Abelian.image g).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (cokernel.π g)
  have : (Abelian.image g).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (stableKernelImage I α m).IsCoherent := stableKernelImage_isCoherent I α m
  have : (stableKernelImage I α m).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact idealPowerMultiple_eq_bot_of_iso K (Abelian.imageIsoImage g).symm t
    (idealPowerMultiple_eq_bot_of_epi K t (Abelian.factorThruImage g)
      (hker (kernelStableLevel I α m)))

/-- **The terms of `Stacks.Coherent.coherentAdicKernel` are annihilated by whatever annihilates
the levelwise kernels.** Each is an `ℐ`-adic quotient of a stable kernel image, by
`Stacks.Coherent.kernelImageQuotients_eventuallyConstant`. -/
public theorem idealPowerMultiple_coherentAdicKernel_obj_eq_bot (α : F ⟶ G) (t : ℕ)
    (hker : ∀ n : ℕ, idealPowerMultiple K t (kernel (α.hom.app (op n))) = ⊥) (n : ℕ) :
    idealPowerMultiple K t ((coherentAdicKernel I α).obj.obj (op n)) = ⊥ := by
  obtain ⟨c, hc⟩ := kernelImageQuotients_eventuallyConstant I α n
  obtain ⟨e, -⟩ := hc (n + c) le_rfl
  have : (stableKernelImage I α (n + c)).IsCoherent :=
    stableKernelImage_isCoherent I α (n + c)
  have : (stableKernelImage I α (n + c)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  exact idealPowerMultiple_eq_bot_of_iso K e.symm t
    (idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot K I t (n + 1) _
      (idealPowerMultiple_stableKernelImage_eq_bot I K α t hker (n + c)))

/-- **The terms of the kernel in `Coh(X, ℐ)` are annihilated by whatever annihilates the
levelwise kernels.** The kernel is `Stacks.Coherent.coherentAdicKernel` up to the canonical
identification of two limits of the same diagram. -/
public theorem idealPowerMultiple_kernel_obj_eq_bot_of_termwise (α : F ⟶ G) (t : ℕ)
    (hker : ∀ n : ℕ, idealPowerMultiple K t (kernel (α.hom.app (op n))) = ⊥) (n : ℕ) :
    idealPowerMultiple K t ((kernel α).obj.obj (op n)) = ⊥ :=
  idealPowerMultiple_eq_bot_of_iso K
    (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel α)
        (coherentAdicKernelIsLimit I α))).app (op n)) t
    (idealPowerMultiple_coherentAdicKernel_obj_eq_bot I K α t hker n)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **The terms of the cokernel in `Coh(X, ℐ)` are annihilated by whatever annihilates the
levelwise cokernels.** The cokernel is the levelwise one,
`Stacks.Coherent.coherentAdicCokernel`. -/
public theorem idealPowerMultiple_cokernel_obj_eq_bot_of_termwise (α : F ⟶ G) (t : ℕ)
    (hcok : ∀ n : ℕ, idealPowerMultiple K t (cokernel (α.hom.app (op n))) = ⊥) (n : ℕ) :
    idealPowerMultiple K t ((cokernel α).obj.obj (op n)) = ⊥ :=
  idealPowerMultiple_eq_bot_of_iso K
    ((((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso
        (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel α)
          (coherentAdicCokernelIsColimit I α))).app (op n)).trans
      (cokernelObjIso α.hom (op n))) t (hcok n)

end AdicKernelCokernel


/-! ### Completion reflects annihilation of kernels and cokernels -/

section Reflect

variable {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)

/-- A module isomorphic to a coherent `P` that is annihilated by `𝒦 ᵉ⁺¹` is annihilated by
`𝒦 ᵗ⁺¹` once the terms of a system isomorphic to the completion of `P` are annihilated by `𝒦 ᵗ`. -/
private theorem idealPowerMultiple_succ_eq_bot_of_iso_of_completion (e t : ℕ)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) {Q : X.Modules}
    (E : P.obj ≅ Q) (hQ : idealPowerMultiple K (e + 1) Q = ⊥) {C : CoherentAdicSystems I}
    (D : (completionFunctor X I).obj P ≅ C)
    (hC : ∀ k : ℕ, idealPowerMultiple K t (C.obj.obj (op k)) = ⊥) :
    idealPowerMultiple K (t + 1) Q = ⊥ :=
  idealPowerMultiple_eq_bot_of_iso K E.symm (t + 1)
    (idealPowerMultiple_eq_bot_of_completion I K e t h P
      (idealPowerMultiple_eq_bot_of_iso K E (e + 1) hQ)
      fun k => idealPowerMultiple_eq_bot_of_iso K
        (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso D).app (op k)) (t + 1)
        (idealPowerMultiple_eq_bot_of_le (hC k) (Nat.le_succ t)))

/-- **Completion reflects annihilation of kernels and cokernels on the `𝒦`-power-annihilated
part.** Let `a : M ⟶ N` be a map of coherent `𝒪_X`-modules both annihilated by `𝒦 ᵉ⁺¹`, and
assume hypothesis (1) of [Stacks, Tag 088A] at the level `e`. If every levelwise kernel and every
levelwise cokernel of the completion `a ^∧_ℐ` is annihilated by `𝒦 ᵗ`, then the kernel and the
cokernel of `a` are annihilated by `𝒦 ᵗ⁺¹`.

This is what makes the comparison `(G_e) ⟶ H ^∧_𝒦` of the proof of Tag 088A satisfy the
hypothesis of Tag 0889: the comparison is built by lifting a map of completions through the full
faithfulness of completion on the annihilated part, so its kernel and cokernel are only known
after the fact, from those of the map of completions.

Both the kernel and the cokernel of `a` are again annihilated by `𝒦 ᵉ⁺¹` — a subobject of `M`
and a quotient of `N` — so `Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion` applies to
them once their completions are known to be termwise annihilated; and those completions are the
kernel and the cokernel of `a ^∧_ℐ`, because completion is exact ([Stacks, Tag 0881]). -/
public theorem idealPowerMultiple_kernel_cokernel_eq_bot_of_completion (e t : ℕ)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : M ⟶ N)
    (hM : idealPowerMultiple K (e + 1) M.obj = ⊥)
    (hN : idealPowerMultiple K (e + 1) N.obj = ⊥)
    (ha : ∀ k : ℕ,
      idealPowerMultiple K t (kernel (((completionFunctor X I).map a).hom.app (op k))) = ⊥ ∧
      idealPowerMultiple K t
        (cokernel (((completionFunctor X I).map a).hom.app (op k))) = ⊥) :
    idealPowerMultiple K (t + 1) (kernel a.hom) = ⊥ ∧
      idealPowerMultiple K (t + 1) (cokernel a.hom) = ⊥ := by
  have : PreservesFiniteLimits (completionFunctor X I) :=
    ((exactFunctor_iff _).1 (completionFunctor_exact X I)).1
  have : PreservesFiniteColimits (completionFunctor X I) :=
    ((exactFunctor_iff _).1 (completionFunctor_exact X I)).2
  have : M.obj.IsCoherent := M.property
  have : N.obj.IsCoherent := N.property
  have : N.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : PreservesFiniteLimits
      (ObjectProperty.ι (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)) :=
    AlgebraicGeometry.CoherentAbelian.coherentModules_inclusion_preservesFiniteLimits
      X.ringCatSheaf
  have : PreservesFiniteColimits
      (ObjectProperty.ι (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)) :=
    AlgebraicGeometry.CoherentAbelian.coherentModules_inclusion_preservesFiniteColimits
      X.ringCatSheaf
  have : Mono (C := X.Modules) (kernel.ι (C := X.Modules) a.hom) := equalizer.ι_mono
  have : Epi (C := X.Modules) (cokernel.π (C := X.Modules) a.hom) := coequalizer.π_epi
  have : (cokernel (C := X.Modules) a.hom).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel a.hom
  have : (cokernel (C := X.Modules) a.hom).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have Ek : ((kernel a).obj : X.Modules) ≅ kernel (C := X.Modules) a.hom :=
    PreservesKernel.iso
      (ObjectProperty.ι (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)) a
  have Ec : ((cokernel a).obj : X.Modules) ≅ cokernel (C := X.Modules) a.hom :=
    PreservesCokernel.iso
      (ObjectProperty.ι (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)) a
  exact ⟨idealPowerMultiple_succ_eq_bot_of_iso_of_completion I K e t h (kernel a) Ek
      (idealPowerMultiple_eq_bot_of_mono K (kernel.ι (C := X.Modules) a.hom) (e + 1) hM)
      (PreservesKernel.iso (completionFunctor X I) a)
      (idealPowerMultiple_kernel_obj_eq_bot_of_termwise I K
        ((completionFunctor X I).map a) t fun k => (ha k).1),
    idealPowerMultiple_succ_eq_bot_of_iso_of_completion I K e t h (cokernel a) Ec
      (idealPowerMultiple_eq_bot_of_epi K (e + 1) (cokernel.π (C := X.Modules) a.hom) hN)
      (PreservesCokernel.iso (completionFunctor X I) a)
      (idealPowerMultiple_cokernel_obj_eq_bot_of_termwise I K
        ((completionFunctor X I).map a) t fun k => (ha k).2)⟩

end Reflect

end Stacks.Coherent

end
