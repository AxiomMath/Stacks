module

public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact

/-!
# Characteristic roots of powers and of block decompositions

Two facts of linear algebra used to read Frobenius weights off a decomposition of the cohomology
into blocks permuted by the Frobenius, as in the zero-dimensional step of the reduction of the
weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves, where
`H⁰(X_k̄, F)` is the sum of the stalks at the `k̄`-points and the Frobenius permutes them.

* The characteristic roots of `f ^ m` (`m ≠ 0`), over an algebraically closed field, are the
  `m`-th powers of those of `f` (the spectral mapping theorem).
* If idempotents `inc_i ∘ pr_i` decompose the identity of `V` and commute with `g`, every
  characteristic root of `g` is one of a diagonal block `pr_i ∘ g ∘ inc_i`.

## Main results

* `Stacks.EtaleCohomology.exists_isRoot_charpoly_map_pow_eq`.
* `Stacks.EtaleCohomology.exists_isRoot_charpoly_map_block`.
* `Stacks.EtaleCohomology.IsCharpolyNormMixedOfWeightLE.of_blocks`: the weight bound from the
  diagonal blocks.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.EtaleCohomology

variable {K : Type*} [Field K] {L : Type*} [Field L]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The characteristic roots of a power are the powers of the characteristic roots**: over an
algebraically closed field `L`, a root of the characteristic polynomial of `f ^ m` (`m ≠ 0`) read
along `ι : K →+* L` is the `m`-th power of a root of that of `f`. -/
public theorem exists_isRoot_charpoly_map_pow_eq [IsAlgClosed L] (ι : K →+* L)
    (f : Module.End K V) {m : ℕ} (hm : m ≠ 0) {z : L}
    (hz : ((f ^ m).charpoly.map ι).IsRoot z) :
    ∃ y : L, (f.charpoly.map ι).IsRoot y ∧ y ^ m = z := by
  let := ι.toAlgebra
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz
  rw [LinearMap.baseChange_pow, Module.End.hasEigenvalue_iff_mem_spectrum,
    spectrum.map_pow_of_pos (f.baseChange L) (Nat.pos_of_ne_zero hm)] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y, (isRoot_charpoly_map_iff_hasEigenvalue_baseChange ι f y).2
    (Module.End.hasEigenvalue_iff_mem_spectrum.2 hy), rfl⟩

section Block

variable {ιB : Type*} {W : ιB → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  [∀ i, FiniteDimensional K (W i)]

/-- **Characteristic roots of a block-diagonal endomorphism.**  Let `pr_i : V → W_i` and
`inc_i : W_i → V` (`i` in a finite set `s`) satisfy `∑ᵢ inc_i ∘ pr_i = id`, `pr_i ∘ inc_i = id`,
and let `g` commute with every idempotent `inc_i ∘ pr_i`.  Then every characteristic root of `g`
read along `ι` is one of some diagonal block `pr_i ∘ g ∘ inc_i`. -/
public theorem exists_isRoot_charpoly_map_block (ι : K →+* L) (s : Finset ιB)
    (pr : ∀ i, V →ₗ[K] W i) (inc : ∀ i, W i →ₗ[K] V)
    (hsum : ∑ i ∈ s, inc i ∘ₗ pr i = LinearMap.id) (hpi : ∀ i, pr i ∘ₗ inc i = LinearMap.id)
    (g : Module.End K V) (hg : ∀ i ∈ s, g ∘ₗ inc i ∘ₗ pr i = inc i ∘ₗ pr i ∘ₗ g) {z : L}
    (hz : (g.charpoly.map ι).IsRoot z) :
    ∃ i ∈ s, ((pr i ∘ₗ g ∘ₗ inc i).charpoly.map ι).IsRoot z := by
  let := ι.toAlgebra
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hgv : g.baseChange L v = z • v := hv.apply_eq_smul
  have hsumL : ∑ i ∈ s, (inc i).baseChange L ∘ₗ (pr i).baseChange L = LinearMap.id := by
    have := congrArg (LinearMap.baseChangeHom K L V V) hsum
    simpa only [map_sum, LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp,
      LinearMap.baseChange_id] using this
  obtain ⟨i, hi, hne⟩ : ∃ i ∈ s, (pr i).baseChange L v ≠ 0 := by
    by_contra! hcon
    have := LinearMap.congr_fun hsumL v
    rw [LinearMap.sum_apply, Finset.sum_eq_zero fun j hj => by simp [hcon j hj]] at this
    exact hv.2 this.symm
  refine ⟨i, hi, (isRoot_charpoly_map_iff_hasEigenvalue_baseChange ι _ z).2
    (Module.End.hasEigenvalue_of_hasEigenvector (x := (pr i).baseChange L v) ⟨?_, hne⟩)⟩
  rw [Module.End.mem_eigenspace_iff]
  have hgL : g.baseChange L ∘ₗ (inc i).baseChange L ∘ₗ (pr i).baseChange L =
      (inc i).baseChange L ∘ₗ (pr i).baseChange L ∘ₗ g.baseChange L := by
    simp only [← LinearMap.baseChange_comp]
    rw [hg i hi]
  have hpiL : (pr i).baseChange L ∘ₗ (inc i).baseChange L = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hpi i, LinearMap.baseChange_id]
  have h₁ := congrArg (fun φ => (pr i).baseChange L (φ v)) hgL
  have h₂ : ∀ w, (pr i).baseChange L ((inc i).baseChange L w) = w := fun w =>
    LinearMap.congr_fun hpiL w
  simp only [LinearMap.comp_apply] at h₁
  rw [h₂, hgv, map_smul] at h₁
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using h₁

/-- **The weight bound from the diagonal blocks**: in the situation of
`Stacks.EtaleCohomology.exists_isRoot_charpoly_map_block`, if every diagonal block satisfies the
absolute-value bound, so does `g`. -/
public theorem IsCharpolyNormMixedOfWeightLE.of_blocks {q : ℕ} {ι : K →+* ℂ} {b : ℤ}
    (s : Finset ιB) (pr : ∀ i, V →ₗ[K] W i) (inc : ∀ i, W i →ₗ[K] V)
    (hsum : ∑ i ∈ s, inc i ∘ₗ pr i = LinearMap.id) (hpi : ∀ i, pr i ∘ₗ inc i = LinearMap.id)
    (g : Module.End K V) (hg : ∀ i ∈ s, g ∘ₗ inc i ∘ₗ pr i = inc i ∘ₗ pr i ∘ₗ g)
    (h : ∀ i ∈ s, IsCharpolyNormMixedOfWeightLE q ι b (pr i ∘ₗ g ∘ₗ inc i)) :
    IsCharpolyNormMixedOfWeightLE q ι b g := fun z hz =>
  let ⟨i, hi, hzi⟩ := exists_isRoot_charpoly_map_block ι s pr inc hsum hpi g hg hz
  h i hi z hzi

end Block

end Stacks.EtaleCohomology

end
