module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Idempotent completeness from countable (co)powers

A preadditive category in which every object `Z` has a countable power `∏ₙ Z` and in which every
split epimorphism has a kernel is idempotent complete (Karoubian), and dually a preadditive
category with countable copowers in which every split monomorphism has a cokernel. This is
[Stacks, Tag 05QV](https://stacks.math.columbia.edu/tag/05QV).

The engine is the **Bökstedt–Neeman telescope** `idempotentTelescope` of an idempotent `p : Z ⟶ Z`:
an endomorphism of the countable power `∏ₙ Z` that is a split epimorphism whose kernel is a kernel
of `p`. The copower version is deduced from the power one by passing to the opposite category.

## Main definitions

* `CategoryTheory.Idempotents.idempotentTelescope`: the Bökstedt–Neeman telescope of an idempotent.

## Main results

* `isIdempotentComplete_of_hasCountableProducts` (Stacks 05QV(1)): countable powers together with
  kernels of split epimorphisms imply idempotent completeness.
* `isIdempotentComplete_of_hasCountableCoproducts` (Stacks 05QV(2)): the dual statement, obtained by
  applying the previous result to `Cᵒᵖ`.

## Implementation notes

The source assumes all countable products, whereas the telescope of an idempotent `p : Z ⟶ Z` lives
in the countable power `∏ₙ Z`, so that single power is all either result assumes; the names keep the
source's phrasing. `HasCountableProducts C` discharges the hypothesis by instance search, as does
`HasCoproducts.{w} C` for the dual one.

## Tags

idempotent complete, Karoubian, split idempotent, countable products, Bökstedt–Neeman
-/

@[expose] public section

open CategoryTheory Limits Preadditive Idempotents

variable {C : Type*} [Category* C] [Preadditive C]

namespace CategoryTheory.Idempotents

variable {Z : C} (p : Z ⟶ Z) [HasProduct fun _ : ℕ => Z]

/-- The **Bökstedt–Neeman telescope** of an idempotent `p : Z ⟶ Z`: the endomorphism of the
countable power `∏ₙ Z` carrying `p` on the diagonal and `𝟙 - p` on the superdiagonal,
`(aₙ)ₙ ↦ (p aₙ + (𝟙 - p) aₙ₊₁)ₙ`.

When `p` is idempotent it is a split epimorphism (`isSplitEpi_idempotentTelescope`) whose kernel is
a kernel of `p` (`hasKernel_of_hasKernel_idempotentTelescope`); this is the engine of Stacks
05QV(1), `isIdempotentComplete_of_hasCountableProducts`. -/
noncomputable def idempotentTelescope : (∏ᶜ fun _ : ℕ => Z) ⟶ ∏ᶜ fun _ : ℕ => Z :=
  Pi.lift fun n => Pi.π _ n ≫ p + Pi.π _ (n + 1) ≫ (𝟙 Z - p)

@[reassoc (attr := simp)]
lemma idempotentTelescope_π (n : ℕ) :
    idempotentTelescope p ≫ Pi.π _ n = Pi.π _ n ≫ p + Pi.π _ (n + 1) ≫ (𝟙 Z - p) :=
  Pi.lift_comp_π _ n

/-- Precomposing the telescope with `g` and reading the `n`-th projection. -/
private lemma comp_idempotentTelescope_π {A : C} (g : A ⟶ ∏ᶜ fun _ : ℕ => Z) (n : ℕ) :
    (g ≫ idempotentTelescope p) ≫ Pi.π _ n
      = (g ≫ Pi.π _ n) ≫ p + (g ≫ Pi.π _ (n + 1)) ≫ (𝟙 Z - p) := by
  rw [Category.assoc, idempotentTelescope_π, Preadditive.comp_add, Category.assoc, Category.assoc]

/-- The telescope of an idempotent is a split epimorphism; the section carries `𝟙 - p` on the
subdiagonal and `p` on the diagonal (and is the identity on component `0`). -/
lemma isSplitEpi_idempotentTelescope (hp : p ≫ p = p) : IsSplitEpi (idempotentTelescope p) := by
  obtain ⟨σ, hσ0, hσs⟩ : ∃ σ : (∏ᶜ fun _ : ℕ => Z) ⟶ ∏ᶜ fun _ : ℕ => Z,
      σ ≫ Pi.π _ 0 = Pi.π _ 0 ∧
      ∀ m, σ ≫ Pi.π _ (m + 1) = Pi.π _ m ≫ (𝟙 Z - p) + Pi.π _ (m + 1) ≫ p :=
    ⟨Pi.lift fun n => n.casesOn (Pi.π _ 0) fun m => Pi.π _ m ≫ (𝟙 Z - p) + Pi.π _ (m + 1) ≫ p,
      Pi.lift_comp_π _ 0, fun m => Pi.lift_comp_π _ (m + 1)⟩
  refine .mk' ⟨σ, Pi.hom_ext _ _ fun n => ?_⟩
  rw [comp_idempotentTelescope_π, Category.id_comp]
  cases n with
  | zero => simp [hσ0, hσs, hp]
  | succ m => simp [hσs, hp]

section Kernel

variable [HasKernel (idempotentTelescope p)]

/-- The telescope condition `kernel.ι Φ ≫ Φ = 0` read on the `n`-th projection: writing
`κ i := kernel.ι Φ ≫ πᵢ`, one has `κ n ≫ p + κ (n+1) ≫ (𝟙 - p) = 0`. -/
lemma kernelι_idempotentTelescope_condition (n : ℕ) :
    (kernel.ι (idempotentTelescope p) ≫ Pi.π _ n) ≫ p
      + (kernel.ι (idempotentTelescope p) ≫ Pi.π _ (n + 1)) ≫ (𝟙 Z - p) = 0 := by
  rw [← comp_idempotentTelescope_π, kernel.condition, zero_comp]

/-- Every projection of the kernel of the telescope is annihilated by `p`. -/
lemma kernelι_idempotentTelescope_π_comp (hp : p ≫ p = p) (n : ℕ) :
    (kernel.ι (idempotentTelescope p) ≫ Pi.π _ n) ≫ p = 0 := by
  simpa [hp] using congr((· ≫ p) $(kernelι_idempotentTelescope_condition p n))

/-- The kernel of the telescope is concentrated in degree `0`: its inclusion vanishes on every
projection past the `0`-th. -/
lemma kernelι_idempotentTelescope_π_succ (hp : p ≫ p = p) (m : ℕ) :
    kernel.ι (idempotentTelescope p) ≫ Pi.π _ (m + 1) = 0 := by
  rw [← Category.comp_id (kernel.ι (idempotentTelescope p) ≫ Pi.π _ (m + 1)),
    ← add_sub_cancel p (𝟙 Z), Preadditive.comp_add, kernelι_idempotentTelescope_π_comp p hp]
  nth_rw 1 [← kernelι_idempotentTelescope_π_comp p hp m, kernelι_idempotentTelescope_condition]

/-- On component `0`, the kernel inclusion of the telescope is a monomorphism. -/
lemma mono_kernelι_idempotentTelescope_π_zero (hp : p ≫ p = p) :
    Mono (kernel.ι (idempotentTelescope p) ≫ Pi.π _ 0) := ⟨fun {A} a b hab => by
  rw [← cancel_mono (kernel.ι (idempotentTelescope p))]
  refine Pi.hom_ext _ _ fun n => ?_
  cases n with
  | zero => simpa
  | succ m => simp [kernelι_idempotentTelescope_π_succ p hp]⟩

end Kernel

/-- The kernel of the telescope of an idempotent `p`, read off on component `0`, is a kernel of `p`;
so if the telescope has a kernel, then so does `p`. -/
lemma hasKernel_of_hasKernel_idempotentTelescope (hp : p ≫ p = p)
    [HasKernel (idempotentTelescope p)] : HasKernel p := by
  have := mono_kernelι_idempotentTelescope_π_zero p hp
  refine HasLimit.mk ⟨KernelFork.ofι _ (kernelι_idempotentTelescope_π_comp p hp 0),
    KernelFork.IsLimit.ofι' _ (kernelι_idempotentTelescope_π_comp p hp 0) fun {A} k hk => ?_⟩
  -- The map with `k` in component `0` and `0` elsewhere factors through `kernel Φ`.
  set ψ : A ⟶ ∏ᶜ (fun _ : ℕ => Z) := Pi.lift fun n => n.casesOn k fun _ => 0
  refine ⟨kernel.lift _ ψ (Pi.hom_ext _ _ fun n => ?_), by simp [ψ]⟩
  rw [comp_idempotentTelescope_π, zero_comp]
  cases n with
  | zero => simpa [ψ, Pi.lift_comp_π]
  | succ m => simp +zetaDelta

end CategoryTheory.Idempotents

/-- **Stacks 05QV(1)**: a preadditive category in which every object has a countable power, and in
which every split epimorphism has a kernel, is idempotent complete. A kernel of an idempotent
`p : Z ⟶ Z` is read off a kernel of its telescope `idempotentTelescope p`, an endomorphism of the
single countable power `∏ₙ Z`; that is why no product beyond those powers is assumed. -/
@[stacks 05QV "(1)"]
lemma isIdempotentComplete_of_hasCountableProducts [∀ Z : C, HasProduct fun _ : ℕ => Z]
    (h : ∀ {X Y : C} (f : X ⟶ Y) [IsSplitEpi f], HasKernel f) : IsIdempotentComplete C :=
  Idempotents.isIdempotentComplete_iff_idempotents_have_kernels C |>.2 fun _ p hp ↦
    have : HasKernel (idempotentTelescope p) := @h _ _ _ (isSplitEpi_idempotentTelescope p hp)
    hasKernel_of_hasKernel_idempotentTelescope p hp

/-- **Stacks 05QV(2)**: a preadditive category in which every object has a countable copower, and in
which every split monomorphism has a cokernel, is idempotent complete. This is 05QV(1) in `Cᵒᵖ`,
where the copowers of `C` are the countable powers. -/
@[stacks 05QV "(2)"]
lemma isIdempotentComplete_of_hasCountableCoproducts [∀ Z : C, HasCoproduct fun _ : ℕ => Z]
    (h : ∀ {X Y : C} (f : X ⟶ Y) [IsSplitMono f], HasCokernel f) : IsIdempotentComplete C := by
  rw [← Idempotents.isIdempotentComplete_iff_opposite]
  apply isIdempotentComplete_of_hasCountableProducts
  intro _ _ g _
  have : IsSplitMono g.unop := ⟨⟨⟨(section_ g).unop, by rw [← unop_comp, IsSplitEpi.id, unop_id]⟩⟩⟩
  exact HasLimit.mk ⟨_, CokernelCofork.IsColimit.ofπOp (cokernel.π g.unop)
    (cokernel.condition g.unop) (cokernelIsCokernel g.unop)⟩
