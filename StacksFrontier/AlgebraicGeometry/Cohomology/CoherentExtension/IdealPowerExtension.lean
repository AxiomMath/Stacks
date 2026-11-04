module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.MorphismExtension
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Functoriality

/-!
# Extending a morphism off an open subscheme by an ideal power

Let `X` be a Noetherian scheme, `ℱ` a coherent and `𝒢` a quasi-coherent `𝒪_X`-module, and
`U ⊆ X` an open subscheme. A morphism `φ : ℱ|_U ⟶ 𝒢|_U` need not extend to `X`, but it does
after multiplying `ℱ` by a sufficiently high power of the ideal sheaf `ℐ` of the closed
complement of `U`: there are an `n` and a morphism `ψ : ℐ ^ n ℱ ⟶ 𝒢` restricting to `φ` on `U`,
where `ℐ ^ n ℱ ⟶ ℱ` is invertible because `ℐ` is the unit ideal on `U`.

This is the surjectivity half of [Stacks, Tag 01YB] — there `U` is the complement of the closed
subscheme cut out by a given quasi-coherent ideal sheaf `ℐ`, and the conclusion is that the
canonical map `colim_n Hom(ℐ ^ n ℱ, 𝒢) ⟶ Hom_{𝒪_U}(ℱ|_U, 𝒢|_U)` hits every morphism. Here `U`
is arbitrary and `ℐ` is the vanishing ideal of its complement, which is the form in which the
dévissage of [Stacks, Tag 01YE] uses it.

## Main results

* `AlgebraicGeometry.isIso_restrictFunctor_map_idealPowSmul_ι` — multiplying by a power of the
  ideal sheaf of the closed complement of `U` changes nothing over `U`.
* `AlgebraicGeometry.exists_idealPowSmul_hom_restrict` — the extension statement above.

## Implementation notes

The extension is obtained from the unspecified-submodule form
`AlgebraicGeometry.exists_coherent_submodule_extension_of_isNoetherian` ([Stacks, Tag 0FD0] on a
Noetherian scheme) by pushing the submodule down to an ideal power. That form produces a
coherent `ℱ'`, a monomorphism `i : ℱ' ⟶ ℱ` invertible over `U`, and `ψ' : ℱ' ⟶ 𝒢` restricting
to `φ`; since `i` is invertible over `U`, its cokernel is supported in the closed complement of
`U`, so by [Stacks, Tag 01Y9] some power `ℐ ^ n` annihilates that cokernel. The inclusion
`ℐ ^ n ℱ ⟶ ℱ` therefore dies in the cokernel and, `i` being a monomorphism in an abelian
category, factors through `ℱ'`; composing the factorisation with `ψ'` is the morphism wanted.

Annihilation of the cokernel is read affine-locally, through
`AlgebraicGeometry.idealPowerMultiple_eq_bot_iff`, and the subsheaf `ℐ ^ n ℱ` is
`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul`, whose sections over an *arbitrary* open
are available: that is what makes "dies in the cokernel" a statement one can check on the affine
opens of a cover of an arbitrary open.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0FD0](https://stacks.math.columbia.edu/tag/0FD0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Algebraization (mem_submodule_of_affine)
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The ideal power of the complement changes nothing over the open -/

/-- **Multiplying by a power of the ideal sheaf of the closed complement of `U` does not change
a module over `U`.** The ideal sheaf is the unit ideal on every affine open contained in `U`, so
the sections of `ℐ ^ n ℱ` over an open contained in `U` are all of `ℱ`'s. -/
theorem isIso_restrictFunctor_map_idealPowSmul_ι (U : X.Opens) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (idealPowSmul (closedIdeal ⟨(U : Set X)ᶜ, isClosed_compl_iff.mpr U.2⟩) n F).ι) :=
  isIso_restrictFunctor_map_submodule_ι _ U
    (idealPowSmul_obj_eq_top _ n F U (closedIdeal_compl_ideal_eq_top U))

/-! ### A morphism whose target has no ideal-power multiples kills the ideal power -/

/-- A morphism out of `ℱ` kills `ℐ ^ n ℱ` as soon as its target has no `ℐ ^ n`-multiples at all.
Membership in `ℐ ^ n ℱ` is a local condition tested on affine opens, where it says the section is
a sum of `ℐ ^ n`-multiples; a module map takes those to `ℐ ^ n`-multiples of the target. -/
private lemma idealPowSmul_ι_comp_eq_zero (J : X.IdealSheafData) (n : ℕ)
    {F C : X.Modules} [F.IsQuasicoherent] (π : F ⟶ C)
    (hn : ∀ V : X.affineOpens, J.ideal V ^ n • (⊤ : Submodule Γ(X, V.1) Γ(C, V.1)) = ⊥) :
    (idealPowSmul J n F).ι ≫ π = 0 := by
  ext W s
  have hbot : π.val.app W s.val ∈ (⊥ : C.Submodule).toSubmodule.obj W := by
    refine mem_submodule_of_affine (⊥ : C.Submodule) W.unop (π.val.app W s.val) fun V g => ?_
    have hs : F.val.map g.op s.val ∈
        J.ideal V ^ n • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1)) := by
      have h := (idealPowSmul J n F).toSubmodule.map_mem g.op s.property
      rwa [obj_idealPowSmul] at h
    have hmem := mem_smul_top_app π V.1 (J.ideal V ^ n) _ hs
    rw [hn V] at hmem
    rw [← PresheafOfModules.naturality_apply]
    exact (SheafOfModules.Submodule.bot_obj C (op V.1)).ge hmem
  exact (Submodule.mem_bot _).1 ((SheafOfModules.Submodule.bot_obj C W).le hbot)

/-! ### The extension -/

/-- **The surjectivity half of [Stacks, Tag 01YB], for an arbitrary open.** Let `ℱ` be a
coherent and `𝒢` a quasi-coherent module on a Noetherian scheme `X`, let `U ⊆ X` be open and
let `ℐ` be the ideal sheaf of the reduced closed complement of `U`. Every morphism
`φ : ℱ|_U ⟶ 𝒢|_U` is the restriction of a morphism `ψ : ℐ ^ n ℱ ⟶ 𝒢` for some `n`, read through
the inclusion `ℐ ^ n ℱ ⟶ ℱ` — which is invertible over `U` by
`AlgebraicGeometry.isIso_restrictFunctor_map_idealPowSmul_ι`, so no information is lost. -/
theorem exists_idealPowSmul_hom_restrict [IsNoetherian X] (F G : X.Modules)
    [F.IsCoherent] [F.IsQuasicoherent] [G.IsQuasicoherent] (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    ∃ (n : ℕ) (ψ : (idealPowSmul (closedIdeal ⟨(U : Set X)ᶜ,
        isClosed_compl_iff.mpr U.2⟩) n F).toSheafOfModules ⟶ G),
      (Scheme.Modules.restrictFunctor U.ι).map
          (idealPowSmul (closedIdeal ⟨(U : Set X)ᶜ,
            isClosed_compl_iff.mpr U.2⟩) n F).ι ≫ φ =
        (Scheme.Modules.restrictFunctor U.ι).map ψ := by
  obtain ⟨F', hF'coh, i, hi, ψ', e, he₁, he₂⟩ :=
    exists_coherent_submodule_extension_of_isNoetherian F G U φ
  have := hF'coh
  have := hi
  set J : X.IdealSheafData := closedIdeal ⟨(U : Set X)ᶜ, isClosed_compl_iff.mpr U.2⟩ with hJ
  -- the cokernel of `i` is coherent and supported in the complement of `U`
  have hCcoh : (cokernel i).IsCoherent := CoherentAbelian.isCoherent_cokernel i
  have hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map i) := by
    rw [he₁]; infer_instance
  have hsupp : SheafOfModules.supp (cokernel i) ⊆ (J.support : Set X) := by
    intro x hx
    rw [hJ, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    intro hxU
    exact Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_cokernel_of_isIso_restrict
      i U hiso x hxU hx
  -- so a power of the ideal sheaf annihilates it
  obtain ⟨n, hn₀⟩ := (exists_idealPowerMultiple_eq_bot_iff_supp_subset (cokernel i) J).2 hsupp
  have hn := (idealPowerMultiple_eq_bot_iff J n (cokernel i)).1 hn₀
  -- hence the inclusion of `ℐ ^ n ℱ` dies in the cokernel and factors through `ℱ'`
  have hzero : (idealPowSmul J n F).ι ≫ (ShortComplex.cokernelSequence i).g = 0 :=
    idealPowSmul_ι_comp_eq_zero J n (cokernel.π i) hn
  have hex : (ShortComplex.cokernelSequence i).Exact := ShortComplex.cokernelSequence_exact i
  have hmono : Mono (ShortComplex.cokernelSequence i).f := hi
  obtain ⟨γ, hγ⟩ := hex.lift' ((idealPowSmul J n F).ι) hzero
  have hγ' : γ ≫ i = (idealPowSmul J n F).ι := hγ
  refine ⟨n, γ ≫ ψ', ?_⟩
  calc (Scheme.Modules.restrictFunctor U.ι).map (idealPowSmul J n F).ι ≫ φ
      = (Scheme.Modules.restrictFunctor U.ι).map (γ ≫ i) ≫ φ := by rw [hγ']
    _ = (Scheme.Modules.restrictFunctor U.ι).map γ ≫
          ((Scheme.Modules.restrictFunctor U.ι).map i ≫ φ) :=
        (congrArg (fun k => k ≫ φ)
          (Functor.map_comp (Scheme.Modules.restrictFunctor U.ι) γ i)).trans
          (Category.assoc _ _ _)
    _ = (Scheme.Modules.restrictFunctor U.ι).map γ ≫ (e.hom ≫ φ) :=
        congrArg (fun k => (Scheme.Modules.restrictFunctor U.ι).map γ ≫ (k ≫ φ)) he₁
    _ = (Scheme.Modules.restrictFunctor U.ι).map γ ≫
          (Scheme.Modules.restrictFunctor U.ι).map ψ' :=
        congrArg (fun k => (Scheme.Modules.restrictFunctor U.ι).map γ ≫ k) he₂
    _ = (Scheme.Modules.restrictFunctor U.ι).map (γ ≫ ψ') :=
        (Functor.map_comp _ _ _).symm

end AlgebraicGeometry

end
