module

public import StacksCore.Algebra.Homology.ShortComplex.SnakeLemma
public import StacksCore.Tactic.StacksAttribute

/-!
# The snake lemma for a diagram with exact rows

Mathlib's `CategoryTheory.ShortComplex.SnakeInput.snake_lemma` proves exactness of the six-term
sequence for a `SnakeInput`, a structure bundling the two exact rows together with chosen kernel
and cokernel rows. This file states the snake lemma in the form of Stacks Lemma 010H: starting
from a commutative diagram
```
    X ⟶ Y ⟶ Z ⟶ 0
    |α   |β   |γ
0 ⟶ U ⟶ V ⟶ W
```
with exact rows in an abelian category.

## Main definitions

* `CategoryTheory.ShortComplex.snakeInputOfExactRows`: the `SnakeInput` attached to such a
  diagram, whose zeroth and third rows are the kernels and cokernels of the vertical maps.

## Main results

* `CategoryTheory.ShortComplex.snake_lemma_of_exact_rows`: there is a unique connecting map
  `δ : Ker γ ⟶ Coker α` characterised by the pullback/pushout square of the Stacks statement,
  the sequence `Ker α ⟶ Ker β ⟶ Ker γ ⟶ Coker α ⟶ Coker β ⟶ Coker γ` is exact, the first map
  is a monomorphism when `X ⟶ Y` is, and the last map is an epimorphism when `V ⟶ W` is.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

section SnakeLemma

variable {X Y Z U V W : C} {f : X ⟶ Y} {g : Y ⟶ Z} {k : U ⟶ V} {l : V ⟶ W}
  {α : X ⟶ U} {β : Y ⟶ V} {γ : Z ⟶ W}

/-- The snake input attached to a commutative diagram
```
    X ⟶ Y ⟶ Z ⟶ 0
    |α   |β   |γ
0 ⟶ U ⟶ V ⟶ W
```
with exact rows in an abelian category: the zeroth and third rows are the short complexes of
kernels and cokernels of the vertical maps. -/
noncomputable def snakeInputOfExactRows (comm₁ : α ≫ k = f ≫ β) (comm₂ : β ≫ l = g ≫ γ)
    (hfg : f ≫ g = 0) (hkl : k ≫ l = 0) (h₁ : (ShortComplex.mk f g hfg).Exact) [Epi g]
    (h₂ : (ShortComplex.mk k l hkl).Exact) [Mono k] : SnakeInput C where
  L₀ := (ShortComplex.mk f g hfg).kernelShortComplex comm₁ comm₂
  L₁ := ShortComplex.mk f g hfg
  L₂ := ShortComplex.mk k l hkl
  L₃ := (ShortComplex.mk k l hkl).cokernelShortComplex comm₁ comm₂
  v₀₁ :=
    { τ₁ := kernel.ι α
      τ₂ := kernel.ι β
      τ₃ := kernel.ι γ }
  v₁₂ :=
    { τ₁ := α
      τ₂ := β
      τ₃ := γ
      comm₁₂ := comm₁
      comm₂₃ := comm₂ }
  v₂₃ :=
    { τ₁ := cokernel.π α
      τ₂ := cokernel.π β
      τ₃ := cokernel.π γ }
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2 <;> exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2 <;> exact cokernelIsCokernel _
  L₁_exact := h₁
  epi_L₁_g := by dsimp; infer_instance
  L₂_exact := h₂
  mono_L₂_f := by dsimp; infer_instance

/-- **Snake lemma.** Let
```
    X ⟶ Y ⟶ Z ⟶ 0
    |α   |β   |γ
0 ⟶ U ⟶ V ⟶ W
```
(maps `f, g` in the top row, `k, l` in the bottom row) be a commutative diagram with exact rows
in an abelian category. Then
1. there is a unique `δ : Ker γ ⟶ Coker α` such that, with `π' : Y ×_Z Ker γ ⟶ Y`,
  `π : Y ×_Z Ker γ ⟶ Ker γ` the projections and `ι : Coker α ⟶ Coker α ⊔_U V`,
  `ι' : V ⟶ Coker α ⊔_U V` the coprojections, `π ≫ δ ≫ ι = π' ≫ β ≫ ι'`;
2. the sequence `Ker α ⟶ Ker β ⟶ Ker γ ⟶ Coker α ⟶ Coker β ⟶ Coker γ` (with this `δ`) is
  exact; if `f` is a monomorphism then so is `Ker α ⟶ Ker β`, and if `l` is an epimorphism
  then so is `Coker β ⟶ Coker γ`. -/
@[stacks 010H "complete: (1) existence and uniqueness of `δ`; (2) exactness of the six-term \
sequence and both \"Moreover\" clauses", stacks 07JW "stated in any abelian category; the \
abelian-group case is `C = AddCommGrpCat`; includes both \"Moreover\" clauses"]
theorem snake_lemma_of_exact_rows (comm₁ : α ≫ k = f ≫ β) (comm₂ : β ≫ l = g ≫ γ)
    (hfg : f ≫ g = 0) (hkl : k ≫ l = 0) (h₁ : (ShortComplex.mk f g hfg).Exact) [Epi g]
    (h₂ : (ShortComplex.mk k l hkl).Exact) [Mono k] :
    ∃ δ : kernel γ ⟶ cokernel α,
      (pullback.snd g (kernel.ι γ) ≫ δ ≫ pushout.inl (cokernel.π α) k =
        pullback.fst g (kernel.ι γ) ≫ β ≫ pushout.inr (cokernel.π α) k) ∧
      (∀ δ' : kernel γ ⟶ cokernel α,
        pullback.snd g (kernel.ι γ) ≫ δ' ≫ pushout.inl (cokernel.π α) k =
          pullback.fst g (kernel.ι γ) ≫ β ≫ pushout.inr (cokernel.π α) k → δ' = δ) ∧
      (ComposableArrows.mk₅ (kernel.map α β f k comm₁) (kernel.map β γ g l comm₂) δ
        (cokernel.map α β f k comm₁) (cokernel.map β γ g l comm₂)).Exact ∧
      (Mono f → Mono (kernel.map α β f k comm₁)) ∧
      (Epi l → Epi (cokernel.map β γ g l comm₂)) := by
  let S := snakeInputOfExactRows comm₁ comm₂ hfg hkl h₁ h₂
  let δ : kernel γ ⟶ cokernel α := S.δ
  let φ : pullback g (kernel.ι γ) ⟶ U := S.φ₁
  have hφ : φ ≫ k = pullback.fst g (kernel.ι γ) ≫ β := S.φ₁_L₂_f
  have hsnd : pullback.snd g (kernel.ι γ) ≫ δ = φ ≫ cokernel.π α := S.snd_δ
  have hδ : pullback.snd g (kernel.ι γ) ≫ δ ≫ pushout.inl (cokernel.π α) k =
      pullback.fst g (kernel.ι γ) ≫ β ≫ pushout.inr (cokernel.π α) k := by
    rw [reassoc_of% hsnd, pushout.condition, reassoc_of% hφ]
  refine ⟨δ, hδ, fun δ' hδ' ↦ ?_, S.snake_lemma, fun hf ↦ ?_, fun hl ↦ ?_⟩
  · have h := hδ'.trans hδ.symm
    simp only [← Category.assoc, cancel_mono, cancel_epi] at h
    exact h
  · have : Mono S.L₁.f := hf
    exact S.mono_L₀_f
  · have : Epi S.L₂.g := hl
    exact S.epi_L₃_g

end SnakeLemma

end CategoryTheory.ShortComplex
