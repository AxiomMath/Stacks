module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The kernel of a composite

Let `C` be an abelian category, `0 ⟶ N ⟶ B ⟶ A ⟶ 0` a short exact sequence with maps `n` and
`a`, and `b : A ⟶ L` a morphism. The kernel of the composite `a ≫ b` sits in a short exact
sequence `0 ⟶ N ⟶ ker (a ≫ b) ⟶ ker b ⟶ 0`.

## Main definitions

* `CategoryTheory.kernelCompSub`: the map `N ⟶ ker (a ≫ b)` induced by `n`.
* `CategoryTheory.kernelCompQuot`: the map `ker (a ≫ b) ⟶ ker b` induced by `a`.

## Main results

* `CategoryTheory.isPullback_kernelCompQuot`: `ker (a ≫ b)` is the pullback of `ker b` along `a`.
* `CategoryTheory.epi_kernelCompQuot`: `ker (a ≫ b) ⟶ ker b` is an epimorphism when `a` is.
* `CategoryTheory.shortExact_kernelComp`: the sequence `0 ⟶ N ⟶ ker (a ≫ b) ⟶ ker b ⟶ 0` is
  short exact.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ### The kernel of a composite -/

section KernelComp

variable [Abelian C]

/-- The factorisation of `n : N ⟶ B` through `ker (a ≫ b)`, available whenever `n ≫ a = 0`. -/
def kernelCompSub {N B A L : C} {n : N ⟶ B} {a : B ⟶ A} (hna : n ≫ a = 0) (b : A ⟶ L) :
    N ⟶ Limits.kernel (a ≫ b) :=
  Limits.kernel.lift (a ≫ b) n (by rw [← Category.assoc, hna, Limits.zero_comp])

/-- The factorisation of `ker (a ≫ b) ⟶ B ⟶ A` through `ker b`: the kernel of a composite maps
to the kernel of its second factor. -/
def kernelCompQuot {B A L : C} (a : B ⟶ A) (b : A ⟶ L) :
    Limits.kernel (a ≫ b) ⟶ Limits.kernel b :=
  Limits.kernel.lift b (Limits.kernel.ι (a ≫ b) ≫ a)
    (by rw [Category.assoc]; exact Limits.kernel.condition _)

/-- The composite of `kernelCompSub hna b` with the inclusion `ker (a ≫ b) ⟶ B` is `n`. -/
@[simp]
theorem kernelCompSub_ι {N B A L : C} {n : N ⟶ B} {a : B ⟶ A} (hna : n ≫ a = 0) (b : A ⟶ L) :
    kernelCompSub hna b ≫ Limits.kernel.ι (a ≫ b) = n :=
  Limits.kernel.lift_ι _ _ _

/-- The composite of `kernelCompQuot a b` with the inclusion `ker b ⟶ A` is the composite
`ker (a ≫ b) ⟶ B ⟶ A`. -/
@[simp]
theorem kernelCompQuot_ι {B A L : C} (a : B ⟶ A) (b : A ⟶ L) :
    kernelCompQuot a b ≫ Limits.kernel.ι b = Limits.kernel.ι (a ≫ b) ≫ a :=
  Limits.kernel.lift_ι _ _ _

/-- The composite `N ⟶ ker (a ≫ b) ⟶ ker b` is zero. -/
theorem kernelCompSub_comp_kernelCompQuot {N B A L : C} {n : N ⟶ B} {a : B ⟶ A}
    (hna : n ≫ a = 0) (b : A ⟶ L) : kernelCompSub hna b ≫ kernelCompQuot a b = 0 := by
  refine zero_of_comp_mono (Limits.kernel.ι b) ?_
  rw [Category.assoc, kernelCompQuot_ι, ← Category.assoc, kernelCompSub_ι, hna]

/-- **The kernel of a composite is the preimage of the kernel of its second factor.** The square
```
ker (a ≫ b) ⟶ ker b
     |            |
     v            v
     B    --a-->  A
```
is a pullback. -/
theorem isPullback_kernelCompQuot {B A L : C} (a : B ⟶ A) (b : A ⟶ L) :
    IsPullback (kernelCompQuot a b) (Limits.kernel.ι (a ≫ b)) (Limits.kernel.ι b) a := by
  have hlift : ∀ s : Limits.PullbackCone (Limits.kernel.ι b) a, s.snd ≫ (a ≫ b) = 0 := by
    intro s
    rw [← Category.assoc, ← s.condition, Category.assoc, Limits.kernel.condition,
      Limits.comp_zero]
  refine IsPullback.of_isLimit' ⟨kernelCompQuot_ι a b⟩ (Limits.PullbackCone.IsLimit.mk _
    (fun s => Limits.kernel.lift (a ≫ b) s.snd (hlift s)) (fun s => ?_)
    (fun s => Limits.kernel.lift_ι _ _ _) (fun s m _ h₂ => ?_))
  · rw [← cancel_mono (Limits.kernel.ι b), Category.assoc, kernelCompQuot_ι, ← Category.assoc,
      Limits.kernel.lift_ι, s.condition]
  · rw [← cancel_mono (Limits.kernel.ι (a ≫ b)), Limits.kernel.lift_ι, h₂]

/-- **The kernel of a composite surjects onto the kernel of its second factor** when the first
factor is an epimorphism. -/
theorem epi_kernelCompQuot {B A L : C} (a : B ⟶ A) [Epi a] (b : A ⟶ L) :
    Epi (kernelCompQuot a b) := by
  have h := isPullback_kernelCompQuot a b
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]
  infer_instance

/-- **The kernel of a composite, as a short exact sequence.** For `0 ⟶ N ⟶ B ⟶ A ⟶ 0` short
exact and `b : A ⟶ L`,
```
0 ⟶ N ⟶ ker (a ≫ b) ⟶ ker b ⟶ 0
```
is short exact, with maps `kernelCompSub hna b` and `kernelCompQuot a b`. -/
theorem shortExact_kernelComp {N B A L : C} {n : N ⟶ B} {a : B ⟶ A} (hna : n ≫ a = 0)
    (hT : (ShortComplex.mk n a hna).ShortExact) (b : A ⟶ L) :
    (ShortComplex.mk (kernelCompSub hna b) (kernelCompQuot a b)
      (kernelCompSub_comp_kernelCompQuot hna b)).ShortExact := by
  have hmn : Mono (ShortComplex.mk n a hna).f := hT.mono_f
  have hea : Epi a := hT.epi_g
  have hmono : Mono (kernelCompSub hna b) := mono_of_mono_fac (kernelCompSub_ι hna b)
  refine { mono_f := hmono
           epi_g := epi_kernelCompQuot a b
           exact := ShortComplex.exact_of_f_is_kernel _ ?_ }
  refine Limits.KernelFork.IsLimit.ofι' _ _ fun {A'} k hk => ⟨hT.exact.lift
    (k ≫ Limits.kernel.ι (a ≫ b)) ?_, ?_⟩
  · change (k ≫ Limits.kernel.ι (a ≫ b)) ≫ a = 0
    rw [Category.assoc, ← kernelCompQuot_ι a b, ← Category.assoc, hk, Limits.zero_comp]
  · rw [← cancel_mono (Limits.kernel.ι (a ≫ b)), Category.assoc, kernelCompSub_ι]
    exact hT.exact.lift_f _ _

end KernelComp

end CategoryTheory

end
