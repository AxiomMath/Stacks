module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# A kernel into a two-step approximation lies in a weak Serre class

Let `C` be an abelian category and let `P` be a weak Serre class in `C` in the sense of
Stacks 0754.  Closure under kernels says that `ker δ` lies in `P` when both the source and the
target of `δ` do.  The target is often *not* known to be in `P`, and what is known instead is a
*two-step approximation* of it: a morphism `b : M ⟶ B` with `B` in `P` whose kernel is in `P`,
equivalently an exact sequence `0 ⟶ A ⟶ M ⟶ B` with `A` and `B` in `P`.  That is enough:

`prop_kernel_of_prop_kernel_comp` shows that for `δ : W ⟶ M` with `W` in `P` the kernel `ker δ`
lies in `P` as soon as `M` carries such an approximation.

This is the step of the source's proof of Stacks 0720 that closure under kernels, cokernels and
extensions does not supply by itself.  There `M` is a higher direct image `R^{n+1} f_*𝒢` which is
only known to sit in an exact `0 ⟶ 𝒜 ⟶ R^{n+1} f_*𝒢 ⟶ ℬ` with `𝒜`, `ℬ` quasi-coherent, and what
is wanted is the quasi-coherence of the kernel of `R^{n+1} f_*g_*ℋ ⟶ R^{n+1} f_*𝒢`.

## Main results

* `CategoryTheory.ObjectProperty.prop_kernel_of_prop_kernel_comp`: for `δ : W ⟶ M` and
  `b : M ⟶ B` in an abelian category, if `W`, `B` and `ker b` lie in the weak Serre class `P`,
  then so does `ker δ`.

## Implementation notes

The proof identifies `ker δ` with a kernel between two objects that *are* known to be in `P`.
Write `K = ker (δ ≫ b)`, which lies in `P` because `W` and `B` do.  The composite
`K ⟶ W ⟶ M` is killed by `b`, so it factors through `A = ker b` by a morphism `k : K ⟶ A`, and
`ker k ⟶ K ⟶ W` is a kernel of `δ`: a morphism into `W` killed by `δ` is killed by `δ ≫ b`,
hence factors through `K`, and the factorisation is killed by `k` because `A ⟶ M` is a
monomorphism.  Since `K` and `A` lie in `P`, so does `ker k`, and `ker δ` is isomorphic to it.

No hypothesis beyond `P.IsWeakSerreClass` is used, and only its closure under kernels is used.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- **A kernel into an object with a two-step `P`-approximation lies in `P`.**  Let `P` be a weak
Serre class in an abelian category, let `δ : W ⟶ M` with `W` in `P`, and let `b : M ⟶ B` be a
morphism with `B` in `P` and `ker b` in `P` — an exact sequence `0 ⟶ ker b ⟶ M ⟶ B` approximating
`M` by two objects of `P`.  Then `ker δ` lies in `P`.

Closure under kernels alone does not give this: `M` itself need not lie in `P`. -/
theorem prop_kernel_of_prop_kernel_comp [P.IsWeakSerreClass] {W M B : C} (δ : W ⟶ M) (b : M ⟶ B)
    (hW : P W) (hB : P B) (hA : P (kernel b)) : P (kernel δ) := by
  let k : kernel (δ ≫ b) ⟶ kernel b :=
    kernel.lift b (kernel.ι (δ ≫ b) ≫ δ) (by rw [Category.assoc, kernel.condition])
  have hki : k ≫ kernel.ι b = kernel.ι (δ ≫ b) ≫ δ := kernel.lift_ι _ _ _
  have hw : (kernel.ι k ≫ kernel.ι (δ ≫ b)) ≫ δ = 0 := by
    rw [Category.assoc, ← hki, ← Category.assoc, kernel.condition k, zero_comp]
  have hlim : IsLimit (KernelFork.ofι (kernel.ι k ≫ kernel.ι (δ ≫ b)) hw) := by
    refine KernelFork.IsLimit.ofι' _ hw fun {A'} t ht ↦ ?_
    have ht' : t ≫ δ ≫ b = 0 := by rw [← Category.assoc, ht, zero_comp]
    refine ⟨kernel.lift k (kernel.lift (δ ≫ b) t ht') ?_, ?_⟩
    · rw [← cancel_mono (kernel.ι b), zero_comp, Category.assoc, hki, ← Category.assoc,
        kernel.lift_ι, ht]
    · rw [← Category.assoc, kernel.lift_ι, kernel.lift_ι]
  exact P.prop_of_iso (hlim.conePointUniqueUpToIso (limit.isLimit (parallelPair δ 0)))
    (P.prop_kernel k (P.prop_kernel (δ ≫ b) hW hB) hA)

end CategoryTheory.ObjectProperty

end
