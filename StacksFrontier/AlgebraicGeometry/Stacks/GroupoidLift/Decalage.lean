module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Exactness of a twisted Čech complex from a décalage

Let `A' → C'` be faithfully flat. A *décalage* on a sequence of `A'`-modules `M 0, M 1, …` is
the structure that the Čech complex of a quasi-coherent object along `A' → C'` carries: face
maps `d_i : M n → M (n + 1)`, a zeroth codegeneracy `σ : M (n + 1) → M n`, and isomorphisms
`C' ⊗[A'] M n ≅ M (n + 1)` — in the application `c ⊗ m ↦ c • d₀ m` — under which the face
`d_i` of `M n` corresponds to the face `d_{i+1}` of `M (n + 1)`. Nothing is asked of the face
`d₀` beyond being linear: in the application one face involves a transport along the descent
datum. This file shows that the alternating complex `Σ (-1)^i d_i` of such a structure is exact
in every positive degree.

The argument is the one of Stacks 023M: after the faithfully flat base change along
`A' → C'` the complex becomes the complex of the faces of positive index, which the zeroth
codegeneracy contracts.

## Main definitions

* `Stacks.Decalage`: the structure.
* `Stacks.Decalage.diff`: the alternating sum of the faces.

## Main results

* `Stacks.Decalage.exists_diff_eq`: a cocycle in positive degree is a coboundary.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks

universe u v w

variable (A' : Type u) (C' : Type v) [CommRing A'] [CommRing C'] [Algebra A' C']
  (M : ℕ → Type w) [∀ n, AddCommGroup (M n)] [∀ n, Module A' (M n)]

/-- A décalage on a sequence of `A'`-modules. -/
structure Decalage where
  /-- The face maps. -/
  face : ∀ n : ℕ, Fin (n + 2) → M n →ₗ[A'] M (n + 1)
  /-- The zeroth codegeneracy. -/
  codeg : ∀ n : ℕ, M (n + 1) →ₗ[A'] M n
  /-- The décalage isomorphisms. -/
  decal : ∀ n : ℕ, C' ⊗[A'] M n →ₗ[A'] M (n + 1)
  /-- The décalage maps are bijective. -/
  decal_bijective : ∀ n : ℕ, Function.Bijective (decal n)
  /-- The décalage carries the face `d_i` to the face `d_{i+1}`. -/
  face_succ_decal : ∀ (n : ℕ) (i : Fin (n + 2)) (x : C' ⊗[A'] M n),
    face (n + 1) i.succ (decal n x) = decal (n + 1) (LinearMap.lTensor C' (face n i) x)
  /-- The cosimplicial identity `σ₀ d₁ = id`. -/
  codeg_face_one : ∀ (n : ℕ) (m : M n), codeg n (face n 1 m) = m
  /-- The cosimplicial identity `σ₀ d_{i+2} = d_{i+1} σ₀`. -/
  codeg_face_succ_succ : ∀ (n : ℕ) (i : Fin (n + 1)) (m : M (n + 1)),
    codeg (n + 1) (face (n + 1) i.succ.succ m) = face n i.succ (codeg n m)

variable {A' C' M}

namespace Decalage

variable (D : Decalage A' C' M)

/-- The alternating sum of the faces, the differential of the twisted Čech complex. -/
def diff (n : ℕ) : M n →ₗ[A'] M (n + 1) :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • D.face n i

/-- In degree `0` the differential is `d₀ - d₁`. -/
theorem diff_zero_apply (x : M 0) : D.diff 0 x = D.face 0 0 x - D.face 0 1 x := by
  simp [diff, Fin.sum_univ_two, sub_eq_add_neg]

/-- In degree `1` the differential is `d₀ - d₁ + d₂`. -/
theorem diff_one_apply (x : M 1) : D.diff 1 x = D.face 1 0 x - D.face 1 1 x + D.face 1 2 x := by
  simp [diff, Fin.sum_univ_three, sub_eq_add_neg]

/-- In degree `2` the differential is `d₀ - d₁ + d₂ - d₃`. -/
theorem diff_two_apply (x : M 2) :
    D.diff 2 x = D.face 2 0 x - D.face 2 1 x + D.face 2 2 x - D.face 2 3 x := by
  simp [diff, Fin.sum_univ_four, sub_eq_add_neg]

/-- The alternating sum of the faces of positive index, the base change of `diff`. -/
def shiftDiff (n : ℕ) : M n →ₗ[A'] M (n + 1) :=
  ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) • D.face n i.succ

/-- The base change of the differential is the differential of the faces of positive index. -/
theorem decal_lTensor_diff (n : ℕ) (x : C' ⊗[A'] M n) :
    D.decal (n + 1) (LinearMap.lTensor C' (D.diff n) x) = D.shiftDiff (n + 1) (D.decal n x) := by
  have hsum : ∀ (s : Finset (Fin (n + 2))) (f : Fin (n + 2) → M n →ₗ[A'] M (n + 1)),
      LinearMap.lTensor C' (∑ i ∈ s, f i) = ∑ i ∈ s, LinearMap.lTensor C' (f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.lTensor_add, ih]
  have hsmul : ∀ (k : ℤ) (f : M n →ₗ[A'] M (n + 1)),
      LinearMap.lTensor C' (k • f) = k • LinearMap.lTensor C' f := by
    intro k f
    ext c m
    simp
  simp only [diff, shiftDiff, hsum, hsmul, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_zsmul, D.face_succ_decal]

/-- The zeroth codegeneracy contracts the complex of the faces of positive index. -/
theorem shiftDiff_codeg_add (k : ℕ) (x : M (k + 1)) :
    D.shiftDiff k (D.codeg k x) + D.codeg (k + 1) (D.shiftDiff (k + 1) x) = x := by
  simp only [shiftDiff, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ (n := k + 1)]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.succ_zero_eq_one, D.codeg_face_one,
    Fin.val_succ, D.codeg_face_succ_succ, pow_succ, mul_neg, mul_one, neg_zsmul,
    Finset.sum_neg_distrib]
  abel_nf

/-- **A cocycle of positive degree of a décalage is a coboundary.** -/
theorem exists_diff_eq [Module.FaithfullyFlat A' C'] (n : ℕ) (x : M (n + 1))
    (hx : D.diff (n + 1) x = 0) : ∃ y : M n, D.diff n y = x := by
  have hbij₁ := D.decal_bijective (n + 1)
  have hbij₀ := D.decal_bijective n
  have h₁ : D.shiftDiff (n + 2) (D.decal (n + 1) (1 ⊗ₜ x)) = 0 := by
    rw [← decal_lTensor_diff, LinearMap.lTensor_tmul, hx, TensorProduct.tmul_zero, map_zero]
  have h₂ := D.shiftDiff_codeg_add (n + 1) (D.decal (n + 1) (1 ⊗ₜ x))
  rw [h₁, map_zero, add_zero] at h₂
  obtain ⟨z, hz⟩ := hbij₀.2 (D.codeg (n + 1) (D.decal (n + 1) (1 ⊗ₜ x)))
  have hrange : (1 : C') ⊗ₜ[A'] x ∈ LinearMap.range (LinearMap.lTensor C' (D.diff n)) := by
    refine ⟨z, hbij₁.1 ?_⟩
    rw [decal_lTensor_diff, hz, h₂]
  let π := (LinearMap.range (D.diff n)).mkQ
  have hπ : (1 : C') ⊗ₜ[A'] π x = 0 := by
    obtain ⟨w, hw⟩ := hrange
    have : LinearMap.lTensor C' π (LinearMap.lTensor C' (D.diff n) w) = 0 := by
      rw [← LinearMap.lTensor_comp_apply]
      have hz0 : π ∘ₗ D.diff n = 0 := by
        ext m
        simp [π]
      rw [hz0, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rwa [hw, LinearMap.lTensor_tmul] at this
  have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := A') (B := C')
    (M (n + 1) ⧸ LinearMap.range (D.diff n))
  exact (Submodule.Quotient.mk_eq_zero _).mp (hinj (by simpa using hπ) : π x = 0)

end Decalage

end Stacks

end
