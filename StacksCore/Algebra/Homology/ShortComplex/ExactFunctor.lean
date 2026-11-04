module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksCore.CategoryTheory.Preadditive.Yoneda.Basic
import StacksCore.Tactic.StacksAttribute

/-! ## Exact Functors -/

add_to_stacks 010N "part 2"
  CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
add_to_stacks 010N "part 3"
  CategoryTheory.Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
add_to_stacks 010N "part 4" CategoryTheory.Functor.exact_tfae

@[expose] public section

universe w u v

open CategoryTheory Preadditive Limits ShortComplex Opposite

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)

lemma map_homLeft_f_apply (N : C) (φ : N ⟶ S.X₁) :
    (S.map (preadditiveCoyoneda.obj (op N))).f φ = φ ≫ S.f := rfl

lemma map_homLeft_g_apply (N : C) (ψ : N ⟶ S.X₂) :
    (S.map (preadditiveCoyoneda.obj (op N))).g ψ = ψ ≫ S.g := rfl

lemma map_homRight_f_apply (N : C) (φ : S.X₃ ⟶ N) :
    (S.op.map (preadditiveYoneda.obj N)).f φ = S.g ≫ φ := rfl

lemma map_homRight_g_apply (N : C) (ψ : S.X₂ ⟶ N) :
    (S.op.map (preadditiveYoneda.obj N)).g ψ = S.f ≫ ψ := rfl

-- `set_option` works around the stricter isDefEq transparency: the underlying type of
-- `(S.map (preadditiveCoyoneda.obj (op N))).X₁` is defeq to `N ⟶ S.X₁` but only after unfolding.
set_option backward.isDefEq.respectTransparency.types false in
@[stacks 05AA "part 2"]
lemma exact_iff_homLeft : S.Exact ∧ Mono S.f ↔ ∀ N : C,
    (S.map (preadditiveCoyoneda.obj (op N))).Exact ∧
    Mono (S.map (preadditiveCoyoneda.obj (op N))).f := by
  refine ⟨fun ⟨hS, hSf⟩ N ↦ ⟨hS.map_of_mono_of_preservesKernel _ hSf inferInstance,
    AddCommGrpCat.mono_iff_injective _|>.2 fun φ1 φ2 h ↦ ?_⟩, fun h ↦ ⟨?_,
    mono_iff_cancel_zero _ |>.2 fun N g hg ↦ ?_⟩⟩
  · have h' : φ1 ≫ S.f = φ2 ≫ S.f := h
    exact cancel_mono S.f |>.1 h'
  · obtain ⟨φ, hφ⟩ := (ShortComplex.ab_exact_iff _|>.1 (h S.cycles).1) S.iCycles
      (show S.iCycles ≫ S.g = 0 from S.iCycles_g)
    have hφ' : φ ≫ S.f = S.iCycles := hφ
    have : IsSplitEpi S.toCycles := .mk' ⟨φ, by rw [← cancel_mono S.iCycles, Category.assoc,
      S.toCycles_i, Category.id_comp, hφ']⟩
    exact S.exact_iff_epi_toCycles.2 inferInstance
  · obtain ⟨hS, hSf⟩ := h N
    have : Function.Injective (· ≫ S.f) := AddCommGrpCat.mono_iff_injective _|>.1 hSf
    exact this.eq_iff.1 <| hg.trans zero_comp.symm

@[stacks 05AA "part 1"]
lemma exact_iff_homRight : S.Exact ∧ Epi S.g ↔ ∀ N : C,
    (S.op.map (preadditiveYoneda.obj N)).Exact ∧
    Mono (S.op.map (preadditiveYoneda.obj N)).f :=
  (and_congr S.exact_op_iff (op_mono_iff S.g)).symm.trans
    ((exact_iff_homLeft S.op).trans
      ⟨fun h N ↦ (exact_and_mono_f_iff_of_iso (S.op.mapNatIso (PreadditiveCoyoneda.objOpOp N))).1
        (h (op N)),
      fun h N ↦ (exact_and_mono_f_iff_of_iso
        (S.op.mapNatIso (PreadditiveCoyoneda.objOpOp N.unop))).2 (h N.unop)⟩)
