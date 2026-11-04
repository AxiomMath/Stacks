module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.IdealPowerQuotientTower
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelCokernelAnnihilation
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AnnihilatedTowerLift
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AnnihilatorSheaf

/-!
# The comparison of the tower of algebraizations with the completion along the second ideal

Let `X` be a Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves, let `(F_n)` be
an object of `Coh(X, ℐ)` and let `α : (F_n) ⟶ H ^∧_ℐ` be the comparison of hypothesis (2) of
[Stacks, Tag 088A]. Assume hypothesis (1) at every level, and suppose given a tower `(G_e)` of
coherent modules, the term `e` annihilated by `𝒦 ᵉ⁺¹`, together with an identification

`c : (G_e) ^∧_ℐ ≅ (F_n / 𝒦 ᵉ⁺¹ F_n)`

of its termwise `ℐ`-completion with the tower of reductions of `(F_n)` — the output of the
assembly step of the proof of Tag 088A.

This file carries the next step: the comparison `γ : (G_e) ⟶ H ^∧_𝒦` along `𝒦`, and the
annihilation of its levelwise kernels and cokernels by a power of `𝒦`, which is what makes Tag
0889 applicable to it.

The comparison is produced by fullness. Reducing `α` modulo `𝒦 ᵉ⁺¹` gives a morphism
`(F_n / 𝒦 ᵉ⁺¹ F_n) ⟶ (H ^∧_ℐ) / 𝒦 ᵉ⁺¹`; the right-hand side is the `ℐ`-completion of the `e`-th
term `H / 𝒦 ᵉ⁺¹ H` of `H ^∧_𝒦` by
`Stacks.Coherent.completionQuotientTowerIso`, so through `c` this is a morphism of the
`ℐ`-completions of the towers `(G_e)` and `(H / 𝒦 ᵉ⁺¹ H)`, and completion is full on such towers
by `Stacks.Coherent.exists_whiskerRight_completionFunctor_eq_of_power_annihilated_tower`.

The annihilation then comes back the other way. The levelwise kernels and cokernels of the
reduction of `α` are annihilated by `𝒦 ²ᵗ` — this is the remark of [Stacks, Tag 0888], which the
library has over sheaves of modules as
`Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap` — and those are
the levelwise kernels and cokernels of the `ℐ`-completion of `γ_e`, up to the two isomorphisms
above. Completion reflects annihilation on the `𝒦`-power-annihilated part, which is
`Stacks.Coherent.idealPowerMultiple_kernel_cokernel_eq_bot_of_completion`, so `𝒦 ²ᵗ⁺¹`
annihilates the kernel and the cokernel of `γ_e` itself.

## Main results

* `Stacks.Coherent.exists_tower_map_to_completion` — **the comparison `γ`**, together with the
  formula identifying its `ℐ`-completion.
* `Stacks.Coherent.idealPowerMultiple_kernel_cokernel_tower_map_eq_bot` — **its levelwise
  kernels and cokernels are annihilated by `𝒦 ²ᵗ⁺¹`.**

## Implementation notes

What is *not* carried here is the identification `c`: the assembly step of the proof, which this
library has as
`Stacks.Coherent.exists_coherentAdicSystem_completion_iso_idealPowerQuotientSystem`, produces the
modules `G_e` and an isomorphism of completions *for each `e` separately*, not the natural
isomorphism of towers that the statements below consume. Producing that naturality is the
remaining gap between the fourth step and this one.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
  (F : CoherentAdicSystems I)
  (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (α : F ⟶ (completionFunctor X I).obj H)
  (G : ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The comparison `γ : (G_e) ⟶ H ^∧_𝒦` of the proof of [Stacks, Tag 088A].** Granted
hypothesis (1) of Tag 088A at every level, a tower `(G_e)` of coherent modules whose `e`-th term
is annihilated by `𝒦 ᵉ⁺¹` and whose termwise `ℐ`-completion is identified with the tower of
`𝒦 ᵉ⁺¹`-reductions of `(F_n)` admits a morphism into the tower of terms of `H ^∧_𝒦`, whose
`ℐ`-completion is the reduction of `α` read through that identification and through
`Stacks.Coherent.completionQuotientTowerIso`.

The morphism of the completions is the reduction of `α`; the lift is
`Stacks.Coherent.exists_whiskerRight_completionFunctor_eq_of_power_annihilated_tower`, the
fullness of completion on `𝒦`-power-annihilated towers. -/
public theorem exists_tower_map_to_completion
    (h : IsCompletionEquivalenceOnPowerThickenings I K)
    (hG : ∀ e : ℕ, idealPowerMultiple K (e + 1) (G.obj (op e)).obj = ⊥)
    (c : G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F) :
    ∃ b : G ⟶ completionTermTower K H, ∀ e : ℕ,
      (completionFunctor X I).map (b.app (op e)) =
        (c.app (op e)).hom ≫ (idealPowerQuotientAdicFunctor I K (e + 1)).map α ≫
          (completionQuotientTowerTermIso I K H e).hom := by
  obtain ⟨b, hb⟩ := exists_whiskerRight_completionFunctor_eq_of_power_annihilated_tower I K G
    (completionTermTower K H) hG
    (fun e => ((completionFunctor X K).obj H).property.idealPowerMultiple_eq_bot e) h
    (c.hom ≫ Functor.whiskerLeft (idealPowerQuotientAdicTower I K)
        ((evaluation (CoherentAdicSystems I) (CoherentAdicSystems I)).map α) ≫
      (completionQuotientTowerIso I K H).hom)
  exact ⟨b, fun e => congrArg (fun φ : G ⋙ completionFunctor X I ⟶
    completionTermTower K H ⋙ completionFunctor X I => φ.app (op e)) hb⟩

/-- **The levelwise kernels and cokernels of the comparison `γ` are annihilated by a power of
`𝒦`.** With the data of `Stacks.Coherent.exists_tower_map_to_completion`, if `𝒦 ᵗ` annihilates
every levelwise kernel and cokernel of `α`, then `𝒦 ²ᵗ⁺¹` annihilates the kernel and the
cokernel of every term of `γ`.

This is the hypothesis Tag 0889 asks of `γ`, and it is the point at which the two halves of the
argument meet: the reduction doubles the exponent ([Stacks, Tag 0888], over sheaves of modules
`Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap`), and
completion reflects the resulting annihilation on the `𝒦`-power-annihilated part
(`Stacks.Coherent.idealPowerMultiple_kernel_cokernel_eq_bot_of_completion`). -/
public theorem idealPowerMultiple_kernel_cokernel_tower_map_eq_bot
    (h : IsCompletionEquivalenceOnPowerThickenings I K)
    (hG : ∀ e : ℕ, idealPowerMultiple K (e + 1) (G.obj (op e)).obj = ⊥)
    (c : G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F)
    (b : G ⟶ completionTermTower K H)
    (hb : ∀ e : ℕ, (completionFunctor X I).map (b.app (op e)) =
      (c.app (op e)).hom ≫ (idealPowerQuotientAdicFunctor I K (e + 1)).map α ≫
        (completionQuotientTowerTermIso I K H e).hom)
    (t : ℕ)
    (hα : ∀ n : ℕ, idealPowerMultiple K t (kernel (C := X.Modules) (α.hom.app (op n))) = ⊥ ∧
      idealPowerMultiple K t (cokernel (C := X.Modules) (α.hom.app (op n))) = ⊥) (e : ℕ) :
    idealPowerMultiple K (2 * t + 1)
        (kernel (C := X.Modules) (b.app (op e)).hom) = ⊥ ∧
      idealPowerMultiple K (2 * t + 1)
        (cokernel (C := X.Modules) (b.app (op e)).hom) = ⊥ := by
  refine idealPowerMultiple_kernel_cokernel_eq_bot_of_completion I K e (2 * t) (h e)
    (b.app (op e)) (hG e)
    (((completionFunctor X K).obj H).property.idealPowerMultiple_eq_bot e) (fun n => ?_)
  have : (F.obj.obj (op n)).IsQuasicoherent := F.property.isQuasicoherent n
  have : (((completionFunctor X I).obj H).obj.obj (op n)).IsQuasicoherent :=
    ((completionFunctor X I).obj H).property.isQuasicoherent n
  have hann := idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap K K
    (α.hom.app (op n)) (hα n).1 (hα n).2 (e + 1)
  let p := ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso (c.app (op e))).app (op n)
  let q := ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso
    (completionQuotientTowerTermIso I K H e).symm).app (op n)
  have w : ((completionFunctor X I).map (b.app (op e))).hom.app (op n) ≫ q.hom =
      p.hom ≫ idealPowerQuotientMap K K (e + 1) (e + 1) le_rfl (α.hom.app (op n)) := by
    have hcancel : (completionQuotientTowerTermIso I K H e).hom.hom.app (op n) ≫ q.hom =
        𝟙 _ :=
      congrArg (fun φ : (idealPowerQuotientAdicFunctor I K (e + 1)).obj
            ((completionFunctor X I).obj H) ⟶
          (idealPowerQuotientAdicFunctor I K (e + 1)).obj ((completionFunctor X I).obj H) =>
        φ.hom.app (op n)) (completionQuotientTowerTermIso I K H e).hom_inv_id
    rw [hb e]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
    erw [ObjectProperty.FullSubcategory.comp_hom]
    simp only [NatTrans.comp_app, Category.assoc, hcancel, Category.comp_id]
    rfl
  exact ⟨idealPowerMultiple_eq_bot_of_iso K (kernel.mapIso _ _ p q w) (2 * t) hann.1,
    idealPowerMultiple_eq_bot_of_iso K (cokernel.mapIso _ _ p q w) (2 * t) hann.2⟩

end Stacks.Coherent

end
