module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Kernels and cokernels of composites

`KernelFork.IsLimit.ofIsPullback`: the kernel of a composite `g ≫ e` is the pullback along `g` of
the kernel of `e`, and conversely (`IsPullback.of_isKernel`) a commutative square between a kernel
of `g ≫ e` and a kernel of `e` is a pullback; dually `CokernelCofork.IsColimit.ofIsPushout`: the
cokernel of `m ≫ g` is the pushout along `g` of the cokernel of `m`, and conversely
(`IsPushout.of_isCokernel`) a commutative square between a cokernel of `m` and a cokernel of
`m ≫ g` is a pushout. All need only zero morphisms. -/

@[expose] public section

add_to_stacks 0106 CategoryTheory.Limits.kernel
add_to_stacks 0106 CategoryTheory.Limits.cokernel

namespace CategoryTheory.Limits.KernelFork.IsLimit

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- If `m` is a kernel of `e` and `(fst, snd)` is a pullback of `(g, m)`, then `fst` is a kernel
of `g ≫ e`: the kernel of a composite is the pullback of the kernel. This generalises the abelian
`Abelian.isLimitKernelForkOfIsPullback` (kernel of `j ≫ cokernel.π i`) to any category with zero
morphisms. -/
noncomputable def ofIsPullback {P X' Y W Z : C} {fst : P ⟶ Y} {snd : P ⟶ X'} {g : Y ⟶ W}
    {m : X' ⟶ W} (sq : IsPullback fst snd g m) {e : W ⟶ Z} {w : m ≫ e = 0}
    (hm : IsLimit (KernelFork.ofι m w)) :
    IsLimit (KernelFork.ofι fst (show fst ≫ g ≫ e = 0 by
      rw [sq.w_assoc, w, comp_zero])) := by
  have : Mono m := mono_of_isLimit_fork hm
  have : Mono fst := PullbackCone.mono_fst_of_is_pullback_of_mono sq.isLimit
  refine KernelFork.IsLimit.ofι' _ _ fun {T} k hk => ?_
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hm (k ≫ g) (by rwa [Category.assoc])
  rw [Fork.ι_ofι] at hl
  exact ⟨sq.lift k l hl.symm, sq.lift_fst _ _ _⟩

end CategoryTheory.Limits.KernelFork.IsLimit

namespace CategoryTheory.Limits.CokernelCofork.IsColimit

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- If `e` is a cokernel of `m` and `(inl, inr)` is a pushout of `(g, e)`, then `inl` is a
cokernel of `m ≫ g`: the cokernel of a composite is the pushout of the cokernel. Dual to
`KernelFork.IsLimit.ofIsPullback`. -/
noncomputable def ofIsPushout {X' W Y Z P : C} {g : W ⟶ Y} {e : W ⟶ Z} {inl : Y ⟶ P}
    {inr : Z ⟶ P} (sq : IsPushout g e inl inr) {m : X' ⟶ W} {w : m ≫ e = 0}
    (he : IsColimit (CokernelCofork.ofπ e w)) :
    IsColimit (CokernelCofork.ofπ inl (show (m ≫ g) ≫ inl = 0 by
      rw [Category.assoc, sq.w, ← Category.assoc, w, zero_comp])) := by
  have : Epi e := epi_of_isColimit_cofork he
  have : Epi inl := PushoutCocone.epi_inl_of_is_pushout_of_epi sq.isColimit
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {T} k hk => ?_
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' he (g ≫ k) (by rwa [← Category.assoc])
  rw [Cofork.π_ofπ] at hl
  exact ⟨sq.desc k l hl.symm, sq.inl_desc _ _ _⟩

end CategoryTheory.Limits.CokernelCofork.IsColimit

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- If `m` is a kernel of `e` and `k` is a kernel of `g ≫ e`, then a commutative square
`k ≫ g = t ≫ m` is a pullback: the converse of `KernelFork.IsLimit.ofIsPullback`. -/
lemma of_isKernel {P X' Y W Z : C} {k : P ⟶ Y} {t : P ⟶ X'} {g : Y ⟶ W} {m : X' ⟶ W}
    (comm : k ≫ g = t ≫ m) {e : W ⟶ Z} {w : m ≫ e = 0} (hm : IsLimit (KernelFork.ofι m w))
    {w' : k ≫ g ≫ e = 0} (hk : IsLimit (KernelFork.ofι k w')) : IsPullback k t g m := by
  have : Mono m := mono_of_isLimit_fork hm
  have : Mono k := mono_of_isLimit_fork hk
  have lift : ∀ s : PullbackCone g m, { l : s.pt ⟶ P // l ≫ k = s.fst } := fun s => by
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk s.fst
      (by rw [← Category.assoc, s.condition, Category.assoc, w, comp_zero])
    exact ⟨l, hl⟩
  refine IsPullback.of_isLimit' ⟨comm⟩ (PullbackCone.IsLimit.mk _ (fun s => (lift s).1)
    (fun s => (lift s).2) (fun s => ?_) (fun s l h₁ _ => ?_))
  · rw [← cancel_mono m, Category.assoc, ← comm, ← Category.assoc, (lift s).2, s.condition]
  · rw [← cancel_mono k, h₁, (lift s).2]

end CategoryTheory.IsPullback

namespace CategoryTheory.IsPushout

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- If `e` is a cokernel of `m` and `p` is a cokernel of `m ≫ g`, then a commutative square
`g ≫ p = e ≫ q` is a pushout: the converse of `CokernelCofork.IsColimit.ofIsPushout`, dual to
`IsPullback.of_isKernel`. -/
lemma of_isCokernel {X' W Y Z P : C} {g : W ⟶ Y} {e : W ⟶ Z} {p : Y ⟶ P} {q : Z ⟶ P}
    (comm : g ≫ p = e ≫ q) {m : X' ⟶ W} {w : m ≫ e = 0}
    (he : IsColimit (CokernelCofork.ofπ e w)) {w' : (m ≫ g) ≫ p = 0}
    (hp : IsColimit (CokernelCofork.ofπ p w')) : IsPushout g e p q := by
  have : Epi e := epi_of_isColimit_cofork he
  have : Epi p := epi_of_isColimit_cofork hp
  have desc : ∀ s : PushoutCocone g e, { l : P ⟶ s.pt // p ≫ l = s.inl } := fun s => by
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hp s.inl
      (by rw [Category.assoc, s.condition, ← Category.assoc, w, zero_comp])
    exact ⟨l, hl⟩
  refine IsPushout.of_isColimit' ⟨comm⟩ (PushoutCocone.IsColimit.mk _ (fun s => (desc s).1)
    (fun s => (desc s).2) (fun s => ?_) (fun s l h₁ _ => ?_))
  · rw [← cancel_epi e, ← Category.assoc, ← comm, Category.assoc, (desc s).2, s.condition]
  · rw [← cancel_epi p, h₁, (desc s).2]

end CategoryTheory.IsPushout
