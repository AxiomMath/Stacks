module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.QuotientColumn
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Exactness
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AnnihilatorSheaf

/-!
# Faithfulness of completion over a map with annihilated kernel

Let `X` be a Noetherian scheme and let `𝒦 ⊆ 𝒪_X` be a quasi-coherent ideal sheaf. The last step
of the proof of [Stacks, Tag 088A] produces, for each `n`, an isomorphism `e_n` of coherent
`𝒪_X`-modules out of the uniqueness clause of [Stacks, Tag 0889], and then has to check that the
`e_n` commute with the transitions of the two towers. Each side is determined by its composite
with the comparison map `α_n : F_n ⟶ H_n` and by its `𝒦`-completion: that is the content of this
file.

Two maps into a coherent module annihilated by `𝒦 ᵉ⁺¹` with equal `𝒦`-completions are equal,
because the module *is* the `e`-th term of its own completion. A map whose kernel is
annihilated by a power of `𝒦` is jointly monic with completion: two maps into its source that
agree after composition with it and after completion are equal.

## Main results

* `Stacks.Coherent.completion_map_injective_of_target_annihilated` — two maps into a
  `𝒦 ᵉ⁺¹`-annihilated coherent module with equal `𝒦`-completions are equal.
* `Stacks.Coherent.completion_map_injective_over_map_with_annihilated_kernel` — two maps into
  the source of a map `a` whose kernel is annihilated by a power of `𝒦` are equal once they agree
  after composition with `a` and after `𝒦`-completion.
* `Stacks.Coherent.completion_map_term_annihilated` — the levelwise kernels and cokernels of the
  `ℐ`-completion of a map whose kernel and cokernel are annihilated by `𝒦 ᵗ` are annihilated by
  `𝒦 ²ᵗ`.

## Implementation notes

Completion is additive: it is termwise the reduction functor, which is additive by
`Stacks.Algebraization.idealPowerQuotientMap_add`. This is what lets the difference of two
morphisms be formed and carried through.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **Completion along `𝒦` is faithful on the maps into a `𝒦 ᵉ⁺¹`-annihilated coherent
module.** If `𝒦 ᵉ⁺¹ N = 0`, two maps `f, g : M ⟶ N` of coherent `𝒪_X`-modules with equal
`𝒦`-completions are equal. -/
public theorem completion_map_injective_of_target_annihilated (K : X.IdealSheafData) (e : ℕ)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (hN : idealPowerMultiple K (e + 1) N.obj = ⊥) {f g : M ⟶ N}
    (hfg : (completionFunctor X K).map f = (completionFunctor X K).map g) : f = g := by
  have hiso : IsIso (cokernel.π (C := X.Modules) (idealPowerMultiple K (e + 1) N.obj).ι) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot K (e + 1) N.obj hN
  let q : N.obj ≅ idealPowerQuotient K (e + 1) N.obj :=
    @asIso X.Modules _ _ _
      (cokernel.π (C := X.Modules) (idealPowerMultiple K (e + 1) N.obj).ι) hiso
  have step : ∀ h : M ⟶ N, h.hom ≫ q.hom =
      (completionProjection X K M e ≫ ((completionFunctor X K).map h).hom.app (op e)) ≫
        eqToHom (completionFunctor_obj X K N e) := by
    intro h
    refine Eq.trans (congrArg (fun z => h.hom ≫ z)
      (completionProjection_comp_eqToHom X K N e).symm) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    exact congrArg (fun z => z ≫ eqToHom (completionFunctor_obj X K N e))
      (completionFunctor_map_quotient X K h e).symm
  refine ObjectProperty.hom_ext _ ((Iso.cancel_iso_hom_right _ _ q).1 ?_)
  rw [step f, step g, hfg]

/-- **Joint faithfulness over a map with annihilated kernel.** Let `a : M ⟶ N` be a map of
coherent `𝒪_X`-modules whose kernel is annihilated by `𝒦 ᵉ`. Two maps `f, g : L ⟶ M` which agree
after composition with `a` and whose `𝒦`-completions agree are equal. -/
public theorem completion_map_injective_over_map_with_annihilated_kernel [IsNoetherian X]
    (K : X.IdealSheafData)
    {L M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : M ⟶ N)
    (e : ℕ) (ha : idealPowerMultiple K e (kernel (C := X.Modules) a.hom) = ⊥)
    {f g : L ⟶ M} (h : f ≫ a = g ≫ a)
    (hf : (completionFunctor X K).map f = (completionFunctor X K).map g) : f = g := by
  have : PreservesFiniteLimits (completionFunctor X K) :=
    ((exactFunctor_iff _).1 (completionFunctor_exact X K)).1
  have : PreservesFiniteColimits (completionFunctor X K) :=
    ((exactFunctor_iff _).1 (completionFunctor_exact X K)).2
  have : (completionFunctor X K).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have := (completionFunctor X K).preservesHomology_of_preservesMonos_and_cokernels
  have : PreservesBinaryBiproducts (completionFunctor X K) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (completionFunctor X K).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : PreservesFiniteLimits
      (ObjectProperty.ι (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)) :=
    AlgebraicGeometry.CoherentAbelian.coherentModules_inclusion_preservesFiniteLimits
      X.ringCatSheaf
  obtain ⟨k, hfac⟩ : ∃ k, k ≫ kernel.ι a = f - g :=
    ⟨kernel.lift a (f - g) (by rw [Preadditive.sub_comp, h, sub_self]), kernel.lift_ι _ _ _⟩
  have hp : (completionFunctor X K).map k = (completionFunctor X K).map 0 := by
    refine (cancel_mono ((completionFunctor X K).map (kernel.ι a))).mp ?_
    rw [← Functor.map_comp, ← Functor.map_comp, hfac, zero_comp, Functor.map_sub, hf,
      sub_self, Functor.map_zero]
  have hker : idealPowerMultiple K (e + 1) (kernel a).obj = ⊥ :=
    idealPowerMultiple_eq_bot_of_iso K
      (PreservesKernel.iso
        (ObjectProperty.ι (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)) a)
      (e + 1) (idealPowerMultiple_eq_bot_of_le ha (Nat.le_succ e))
  rw [← sub_eq_zero, ← hfac, completion_map_injective_of_target_annihilated K e hker hp,
    zero_comp]

/-- **The remark of [Stacks, Tag 0888] for the terms of a completion.** If the kernel and the
cokernel of a map `a` of coherent `𝒪_X`-modules are annihilated by `𝒦 ᵗ`, then the kernel and
the cokernel of each term of its `ℐ`-completion are annihilated by `𝒦 ²ᵗ`.

The `n`-th term of the completion of `a` *is* the reduction of `a` modulo `ℐ ⁿ⁺¹`, by
`Stacks.Coherent.completionTermQuotientIso`, and over sheaves of modules the remark is
`Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap`. -/
public theorem completion_map_term_annihilated (I K : X.IdealSheafData)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (a : M ⟶ N)
    {t : ℕ} (hk : idealPowerMultiple K t (kernel (C := X.Modules) a.hom) = ⊥)
    (hc : idealPowerMultiple K t (cokernel (C := X.Modules) a.hom) = ⊥) (n : ℕ) :
    idealPowerMultiple K (2 * t)
        (kernel (C := X.Modules) (((completionFunctor X I).map a).hom.app (op n))) = ⊥ ∧
      idealPowerMultiple K (2 * t)
        (cokernel (C := X.Modules) (((completionFunctor X I).map a).hom.app (op n))) = ⊥ := by
  have : M.obj.IsCoherent := M.property
  have : N.obj.IsCoherent := N.property
  have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : N.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have hann := idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap I K a.hom hk hc (n + 1)
  have w : ((completionFunctor X I).map a).hom.app (op n) ≫
      (completionTermQuotientIso I n).hom.app N =
      (completionTermQuotientIso I n).hom.app M ≫
        idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl a.hom :=
    (completionTermQuotientIso I n).hom.naturality a
  exact ⟨idealPowerMultiple_eq_bot_of_iso K
      (kernel.mapIso (C := X.Modules) _ _ ((completionTermQuotientIso I n).app M)
        ((completionTermQuotientIso I n).app N) w) (2 * t) hann.1,
    idealPowerMultiple_eq_bot_of_iso K
      (cokernel.mapIso (C := X.Modules) _ _ ((completionTermQuotientIso I n).app M)
        ((completionTermQuotientIso I n).app N) w) (2 * t) hann.2⟩

end Stacks.Coherent

end
