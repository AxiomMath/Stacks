module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Length

/-!
# Lengths of the quotients `M ⧸ aⁿM`

Let `A` be a commutative ring, `M` an `A`-module and `a : A`.

* The length of `M ⧸ aⁿM` grows at most linearly in `n`, with slope the length of `M ⧸ aM`.
* For a module of finite length the `a`-torsion `ker (a • ·)` and the `a`-cotorsion `M ⧸ aM`
  have *equal* length.
* Colength is subadditive along a composite: for `h : M →ₗ[A] N` and `g : N →ₗ[A] P` the colength
  of `g ∘ₗ h` is at most the sum of the colengths of `h` and of `g`.

## Main results

* `Module.length_quotient_range_comp_le`: colength is subadditive along a composite.
* `Module.length_quotient_smul_pow_le`: `length (M ⧸ aⁿM) ≤ n * length (M ⧸ aM)`.
* `Module.length_ker_lsmul_eq_length_quotient_smul`: for `M` of finite length the `a`-torsion
  and `M ⧸ aM` have the same length.

## Implementation notes

Lengths are valued in `ℕ∞`, and the two subadditivity statements need no finiteness hypothesis.

## References

* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
-/

@[expose] public section

open scoped Pointwise

namespace Module

variable {A : Type*} [CommRing A]

section Comp

variable {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

/-- **Colength is subadditive along a composite.** For `h : M →ₗ[A] N` and `g : N →ₗ[A] P` the
length of `P ⧸ range (g ∘ₗ h)` is at most the length of `N ⧸ range h` plus the length of
`P ⧸ range g`, in `ℕ∞`. -/
public theorem length_quotient_range_comp_le (g : N →ₗ[A] P) (h : M →ₗ[A] N) :
    Module.length A (P ⧸ LinearMap.range (g ∘ₗ h)) ≤
      Module.length A (N ⧸ LinearMap.range h) + Module.length A (P ⧸ LinearMap.range g) := by
  have hle : LinearMap.range (g ∘ₗ h) ≤ LinearMap.range g := LinearMap.range_comp_le_range h g
  have hu : LinearMap.range h ≤ Submodule.comap g (LinearMap.range (g ∘ₗ h)) := by
    rw [← Submodule.map_le_iff_le_comap, LinearMap.range_comp]
  set u := Submodule.mapQ (LinearMap.range h) (LinearMap.range (g ∘ₗ h)) g hu with hu_def
  set v := Submodule.factor hle with hv_def
  have hexact : Function.Exact u v := by
    rw [LinearMap.exact_iff, hu_def, hv_def]
    simp [Submodule.factor, Submodule.ker_mapQ, Submodule.range_mapQ]
  have hbound :
      Module.length A ↥(LinearMap.ker v) ≤ Module.length A (N ⧸ LinearMap.range h) := by
    rw [LinearMap.exact_iff.mp hexact]
    exact Module.length_le_of_surjective u.rangeRestrict (LinearMap.surjective_rangeRestrict u)
  calc Module.length A (P ⧸ LinearMap.range (g ∘ₗ h))
      = Module.length A ↥(LinearMap.ker v) + Module.length A (P ⧸ LinearMap.range g) :=
        Module.length_eq_add_of_exact (LinearMap.ker v).subtype v
          (Submodule.subtype_injective _) (Submodule.factor_surjective hle)
          (LinearMap.exact_subtype_ker_map v)
    _ ≤ Module.length A (N ⧸ LinearMap.range h) + Module.length A (P ⧸ LinearMap.range g) :=
        add_le_add hbound le_rfl

end Comp

section SMul

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- The pointwise multiple `a • ⊤` of the whole module is the range of multiplication by `a`. -/
private theorem smul_top_eq_range_lsmul (a : A) :
    a • (⊤ : Submodule A M) = LinearMap.range (LinearMap.lsmul A M a) := by
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists]

/-- **The length of `M ⧸ aⁿM` grows at most linearly in `n`.** The length of `M ⧸ aⁿM` is at
most `n` times the length of `M ⧸ aM`, in `ℕ∞` and with no finiteness hypothesis. -/
public theorem length_quotient_smul_pow_le (a : A) (n : ℕ) :
    Module.length A (M ⧸ (a ^ n • (⊤ : Submodule A M))) ≤
      n * Module.length A (M ⧸ (a • (⊤ : Submodule A M))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcomp : LinearMap.lsmul A M (a ^ (n + 1)) =
        LinearMap.lsmul A M (a ^ n) ∘ₗ LinearMap.lsmul A M a := by
      ext x
      simp [pow_succ, smul_smul, mul_comm]
    calc Module.length A (M ⧸ (a ^ (n + 1) • (⊤ : Submodule A M)))
        = Module.length A (M ⧸ LinearMap.range
            (LinearMap.lsmul A M (a ^ n) ∘ₗ LinearMap.lsmul A M a)) := by
          rw [smul_top_eq_range_lsmul, hcomp]
      _ ≤ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a)) +
            Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M (a ^ n))) :=
          length_quotient_range_comp_le _ _
      _ = Module.length A (M ⧸ (a • (⊤ : Submodule A M))) +
            Module.length A (M ⧸ (a ^ n • (⊤ : Submodule A M))) := by
          rw [smul_top_eq_range_lsmul, smul_top_eq_range_lsmul]
      _ ≤ Module.length A (M ⧸ (a • (⊤ : Submodule A M))) +
            n * Module.length A (M ⧸ (a • (⊤ : Submodule A M))) := by gcongr
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length A (M ⧸ (a • (⊤ : Submodule A M))) := by
          push_cast
          ring

/-- **For a module of finite length the `a`-torsion and the `a`-cotorsion have the same
length.** For `M` of finite length, the kernel of multiplication by `a` on `M` and the quotient
`M ⧸ aM` have the same length. -/
public theorem length_ker_lsmul_eq_length_quotient_smul (hM : IsFiniteLength A M) (a : A) :
    Module.length A ↥(LinearMap.ker (LinearMap.lsmul A M a)) =
      Module.length A (M ⧸ (a • (⊤ : Submodule A M))) := by
  set f := LinearMap.lsmul A M a with hf_def
  have hker : Module.length A M =
      Module.length A ↥(LinearMap.ker f) + Module.length A ↥(LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
      (Submodule.subtype_injective _) f.surjective_rangeRestrict
      (LinearMap.exact_iff.mpr (by simp))
  have hquot : Module.length A M =
      Module.length A ↥(LinearMap.range f) + Module.length A (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hfin : Module.length A ↥(LinearMap.range f) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (IsFiniteLength.of_injective (f := (LinearMap.range f).subtype) hM
        (Submodule.subtype_injective _))
  have hcancel : Module.length A ↥(LinearMap.range f) + Module.length A ↥(LinearMap.ker f) =
      Module.length A ↥(LinearMap.range f) + Module.length A (M ⧸ LinearMap.range f) := by
    rw [← hquot, hker, add_comm]
  rw [smul_top_eq_range_lsmul, ← hf_def]
  exact WithTop.add_left_cancel hfin hcancel

end SMul

end Module

end
