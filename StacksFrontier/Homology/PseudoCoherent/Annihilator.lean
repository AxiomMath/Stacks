module

public import Mathlib
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.Homology.PseudoCoherent.Triangle

/-!
# Kernels of maps of pseudo-coherent modules, and annihilators

The kernel of a surjection of pseudo-coherent modules is pseudo-coherent, by the two-out-of-three
property of pseudo-coherence along a distinguished triangle [stacks 064R]. Consequently, if the
cyclic module `A ⧸ (f)` over a commutative ring `A` is pseudo-coherent, then so are the ideal
`(f)` and the annihilator of `f`, which is in particular finitely generated: the short exact
sequences are `0 → (f) → A → A ⧸ (f) → 0` and `0 → Ann(f) → A → (f) → 0`.

## Main results

* `StacksDraft.PseudoCoherence.isModulePseudoCoherent_ker_of_surjective`: the kernel of a
  surjection of pseudo-coherent modules is pseudo-coherent.
* `StacksDraft.PseudoCoherence.fg_ker_toSpanSingleton_of_isModulePseudoCoherent_quotient`: if
  `A ⧸ (f)` is pseudo-coherent, the annihilator `{a | a • f = 0}` of `f` is finitely generated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace StacksDraft.PseudoCoherence

section Kernel

variable {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{u} R)]

/-- The kernel of a surjection of pseudo-coherent modules is pseudo-coherent. -/
theorem isModulePseudoCoherent_ker_of_surjective {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : M →ₗ[R] N} (hg : Function.Surjective g)
    (hM : IsModulePseudoCoherent (R := R) M) (hN : IsModulePseudoCoherent (R := R) N) :
    IsModulePseudoCoherent (R := R) (LinearMap.ker g) := by
  have hS := LinearMap.shortExact_shortComplexKer hg
  unfold IsModulePseudoCoherent at hM hN ⊢
  rw [pseudoCoherent_iff_all] at hM hN ⊢
  intro m
  have h := _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_three (m - 1)
    hS.singleTriangle hS.singleTriangle_distinguished (by simpa using hM m) (hN (m - 1))
  rw [sub_add_cancel] at h
  exact h

end Kernel

section Annihilator

variable {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]

/-- If the cyclic module `A ⧸ (f)` is pseudo-coherent, then the annihilator of `f`, the kernel
of `a ↦ a • f`, is a finitely generated ideal. -/
theorem fg_ker_toSpanSingleton_of_isModulePseudoCoherent_quotient (f : A)
    (h : IsModulePseudoCoherent (R := A) (A ⧸ Ideal.span {f})) :
    (LinearMap.ker (LinearMap.toSpanSingleton A A f)).FG := by
  have hA : IsModulePseudoCoherent (R := A) A := isModulePseudoCoherent_of_finite_free A
  have h₁ : IsModulePseudoCoherent (R := A) (LinearMap.ker (Ideal.span {f}).mkQ) :=
    isModulePseudoCoherent_ker_of_surjective (Submodule.mkQ_surjective _) hA h
  let e : (LinearMap.ker (Ideal.span {f}).mkQ) ≃ₗ[A]
      (LinearMap.range (LinearMap.toSpanSingleton A A f)) :=
    LinearEquiv.ofEq _ _ (by
      rw [Submodule.ker_mkQ, ← LinearMap.span_singleton_eq_range])
  have h₂ : IsModulePseudoCoherent (R := A)
      (LinearMap.range (LinearMap.toSpanSingleton A A f)) :=
    IsPseudoCoherent.ofIso h₁
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e.toModuleIso)
  have h₃ := isModulePseudoCoherent_ker_of_surjective
    (LinearMap.toSpanSingleton A A f).surjective_rangeRestrict hA h₂
  rw [LinearMap.ker_rangeRestrict] at h₃
  rw [← Module.Finite.iff_fg]
  exact (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small (R := A) _).1.1
    ((pseudoCoherent_iff_all _).mp h₃ 0)

end Annihilator

end StacksDraft.PseudoCoherence

end
