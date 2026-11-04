module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.BaseChangeAlongSurjection

/-!
# The kernel of a base change along a surjection with square-zero kernel

Let `A → B` be a surjection of commutative rings with kernel `I` and let `M` be an `A`-module
exhibiting a `B`-module `N` as its extension of scalars, that is `f : M →ₗ[A] N` with
`IsBaseChange B f`. Then

* the kernel of `f` is `I • M`, with no hypothesis on `M` beyond the base-change property, and
* if moreover `M` is flat and `I ^ 2 = 0`, that kernel is canonically `I ⊗[A] N`, by an
  isomorphism sending `i ⊗ n` to `i • m` for any `m` with `f m = n`.

The second statement is the form in which a first-order deformation is read off. If `A` is a
square-zero extension `k ⊕ V` of a field `k` by a `k`-vector space `V`, with `B = k`, then `I` is
`V`, a module `M` over `A` which is flat with `M ⊗[A] k = N` has `ker (M → N) ≅ V ⊗[A] N`, and the
right-hand side depends only on the special fibre `N` and on `V`. So a discrepancy that is known
only to vanish in the special fibre — the value at lifted generators of a relation of a
presentation of `N` — becomes an element of a module built from `N` alone, which is what makes a
receptacle for a first-order deformation class independent of the deformation. That is the step
the proof of Stacks 0DVZ makes when it places the first-order variation of the relations of a
graded algebra in `W ⊗[k] V` for `W` the cokernel of the graded Jacobian.

Flatness is what makes the comparison injective: the inclusion `I → A` stays injective after
tensoring with `M`, and its image in `M` is `I • M`. Squaring to zero is what makes it
surjective: `I ⊗[A] (I • M) → I ⊗[A] M` is then the zero map, so right exactness of the tensor
product identifies `I ⊗[A] M` with `I ⊗[A] N`.

## Main definitions

* `IsBaseChange.idealTensorEquivKer`: the identification of the kernel of a flat base change
  along a square-zero surjection with `I ⊗[A] N`.

## Main results

* `IsBaseChange.ker_eq_ker_algebraMap_smul_top`: the kernel of a base change along a surjection
  is the ideal times the module.
* `IsBaseChange.bijective_lTensor_of_mul_self_eq_bot`: tensoring a base change along a
  square-zero surjection with the kernel ideal gives a bijection.
* `IsBaseChange.coe_idealTensorEquivKer_tmul`: the identification sends `i ⊗ f m` to `i • m`.

## Implementation notes

The hypotheses are on `algebraMap A B` rather than on an abstract ideal: the kernel of a base
change is governed by the kernel of the structure map, and stating the square-zero condition for
that ideal avoids carrying an equation between an abstract ideal and `RingHom.ker (algebraMap A B)`
through every application.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open TensorProduct

namespace IsBaseChange

universe u v w t

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {M : Type w} [AddCommGroup M] [Module A M]
  {N : Type t} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {f : M →ₗ[A] N}

/-- The kernel of a base change along a surjection `A → B` is the kernel ideal of `A → B` times
the module: a module and its extension of scalars along a surjection differ exactly by that
ideal. No flatness and no nilpotence are needed. -/
theorem ker_eq_ker_algebraMap_smul_top (h : IsBaseChange B f)
    (hs : Function.Surjective (algebraMap A B)) :
    LinearMap.ker f = RingHom.ker (algebraMap A B) • (⊤ : Submodule A M) := by
  set I : Ideal A := RingHom.ker (algebraMap A B) with hI
  have hex : Function.Exact I.subtype (Algebra.linearMap A B) := by
    intro a
    simp [hI, RingHom.mem_ker, Algebra.linearMap_apply]
  have hone : ∀ m : M,
      (LinearMap.rTensor M (Algebra.linearMap A B)) ((1 : A) ⊗ₜ[A] m) = 0 ↔ f m = 0 := by
    intro m
    rw [LinearMap.rTensor_tmul]
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · simpa [h.equiv_tmul] using congrArg h.equiv hm
    · have hz : h.equiv ((Algebra.linearMap A B) 1 ⊗ₜ[A] m) = 0 := by
        rw [h.equiv_tmul, hm, smul_zero]
      simpa using h.equiv.injective (hz.trans (map_zero h.equiv).symm)
  ext m
  rw [LinearMap.mem_ker, ← hone m, ← LinearMap.mem_ker,
    (rTensor_exact M hex hs).linearMap_ker_eq, ← Ideal.subtype_rTensor_range M I]
  refine exists_congr fun x => ?_
  change _ = _ ↔ (TensorProduct.lid A M) _ = m
  rw [← (TensorProduct.lid A M).injective.eq_iff, TensorProduct.lid_tmul, one_smul]

/-- An element of `I • M` tensored on the left with an element of a square-zero ideal `I`
vanishes in `I ⊗[A] M`: the scalar moves across the tensor and multiplies into the ideal. -/
private theorem tmul_eq_zero_of_mem_smul_top {I : Ideal A} (hI : I * I = ⊥) (i : I) {y : M}
    (hy : y ∈ I • (⊤ : Submodule A M)) : (i ⊗ₜ[A] y : ↥I ⊗[A] M) = 0 := by
  refine Submodule.smul_induction_on hy ?_ fun y z hy hz => ?_
  · intro a ha m _
    rw [← TensorProduct.smul_tmul]
    have h0 : a • i = 0 := Subtype.ext (by simpa [hI] using Ideal.mul_mem_mul ha i.2)
    rw [h0, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hy, hz, add_zero]

/-- Tensoring a base change along a square-zero surjection with the kernel ideal `I` of that
surjection gives a bijection `I ⊗[A] M → I ⊗[A] N`.

Surjectivity is right exactness of the tensor product. Injectivity is right exactness applied to
the inclusion of `ker f = I • M`, whose tensor product with `I` is the zero map because `I` is
square zero. -/
theorem bijective_lTensor_of_mul_self_eq_bot (h : IsBaseChange B f)
    (hs : Function.Surjective (algebraMap A B))
    (hI : RingHom.ker (algebraMap A B) * RingHom.ker (algebraMap A B) = ⊥) :
    Function.Bijective (LinearMap.lTensor ↥(RingHom.ker (algebraMap A B)) f) := by
  set I : Ideal A := RingHom.ker (algebraMap A B)
  have hsurj := h.surjective_of_surjective_algebraMap hs
  have hexact : Function.Exact (LinearMap.lTensor ↥I (LinearMap.ker f).subtype)
      (LinearMap.lTensor ↥I f) :=
    lTensor_exact ↥I f.exact_subtype_ker_map hsurj
  refine ⟨?_, LinearMap.lTensor_surjective ↥I hsurj⟩
  rw [← LinearMap.ker_eq_bot, hexact.linearMap_ker_eq, LinearMap.range_eq_bot]
  refine TensorProduct.ext' fun i x => ?_
  rw [LinearMap.lTensor_tmul]
  exact tmul_eq_zero_of_mem_smul_top hI i ((h.ker_eq_ker_algebraMap_smul_top hs).le x.2)

/-- The kernel of a flat base change along a surjection `A → B` with square-zero kernel `I` is
canonically `I ⊗[A] N`, a module built from the extension of scalars alone.

It is the composition of two comparisons: `I ⊗[A] N ≅ I ⊗[A] M`, which is
`IsBaseChange.bijective_lTensor_of_mul_self_eq_bot`, and `I ⊗[A] M ≅ ker f`, the multiplication
map, which is injective because `M` is flat and has image `I • M = ker f`. -/
noncomputable def idealTensorEquivKer [Module.Flat A M] (h : IsBaseChange B f)
    (hs : Function.Surjective (algebraMap A B))
    (hI : RingHom.ker (algebraMap A B) * RingHom.ker (algebraMap A B) = ⊥) :
    ↥(RingHom.ker (algebraMap A B)) ⊗[A] N ≃ₗ[A] LinearMap.ker f :=
  (LinearEquiv.ofBijective (LinearMap.lTensor ↥(RingHom.ker (algebraMap A B)) f)
        (h.bijective_lTensor_of_mul_self_eq_bot hs hI)).symm.trans
    ((LinearEquiv.ofInjective
        ((TensorProduct.lid A M).toLinearMap ∘ₗ
          LinearMap.rTensor M (RingHom.ker (algebraMap A B)).subtype)
        ((TensorProduct.lid A M).injective.comp
          (Module.Flat.rTensor_preserves_injective_linearMap _
            (Submodule.injective_subtype _)))).trans
      (LinearEquiv.ofEq _ _
        ((Ideal.subtype_rTensor_range M _).trans
          (h.ker_eq_ker_algebraMap_smul_top hs).symm)))

/-- The identification of the kernel of a flat base change along a square-zero surjection with
`I ⊗[A] N` sends `i ⊗ f m` to `i • m`.

This is the characterisation a consumer uses: the first-order class of an element of the kernel
is read by writing that element as `i • m` and taking the image of `m` in the special fibre, and
the class does not depend on which preimage `m` is chosen because two choices differ by an
element of `I • M`, which `i` annihilates. -/
theorem coe_idealTensorEquivKer_tmul [Module.Flat A M] (h : IsBaseChange B f)
    (hs : Function.Surjective (algebraMap A B))
    (hI : RingHom.ker (algebraMap A B) * RingHom.ker (algebraMap A B) = ⊥)
    (i : ↥(RingHom.ker (algebraMap A B))) (m : M) :
    ((h.idealTensorEquivKer hs hI (i ⊗ₜ[A] f m) : LinearMap.ker f) : M) = (i : A) • m := by
  have hpre : (LinearEquiv.ofBijective (LinearMap.lTensor ↥(RingHom.ker (algebraMap A B)) f)
      (h.bijective_lTensor_of_mul_self_eq_bot hs hI)).symm (i ⊗ₜ[A] f m) = i ⊗ₜ[A] m :=
    (LinearEquiv.symm_apply_eq _).2 (LinearMap.lTensor_tmul _ f i m).symm
  rw [idealTensorEquivKer]
  simp only [LinearEquiv.trans_apply, hpre]
  simp

end IsBaseChange

end
