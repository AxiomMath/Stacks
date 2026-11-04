module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EigenvalueAlgebraicity

/-!
# Characteristic roots along exact sequences

Let `f` be an endomorphism of a finite-dimensional vector space over a field `K` and
`ι : K →+* ℂ` a ring homomorphism. The complex characteristic roots of `f` along `ι` are the roots
of `f.charpoly.map ι`, that is, the eigenvalues of the extension of scalars of `f` to `ℂ` along
`ι`. This file shows that these roots, and bounds on their absolute values in terms of weights,
behave well along equivariant exact sequences, as in the weight bound of Weil II,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isRoot_charpoly_map_iff_hasEigenvalue_baseChange`: the complex roots
  of `f.charpoly.map ι` are the eigenvalues of the extension of scalars of `f` to `ℂ`.
* `Stacks.EtaleCohomology.isRoot_charpoly_map_or_of_exact`: in an equivariant exact sequence
  `A → B → C` every complex characteristic root of the middle term is one of an outer term.
* `Stacks.EtaleCohomology.isRoot_charpoly_map_of_injective`,
  `Stacks.EtaleCohomology.isRoot_charpoly_map_of_surjective`: the characteristic roots of an
  equivariant subobject or quotient are characteristic roots of the whole.
* `Stacks.EtaleCohomology.IsCharpolyMixedOfWeightLE.of_exact_of_exact`,
  `Stacks.EtaleCohomology.IsCharpolyMixedOfWeightLE.of_injective`,
  `Stacks.EtaleCohomology.IsCharpolyMixedOfWeightLE.of_surjective`: hence mixedness of weight at
  most `i` passes to middle terms of exact sequences, to subobjects and to quotients.
* `Stacks.EtaleCohomology.IsCharpolyNormMixedOfWeightLE`: the absolute-value half of
  mixedness, with the same closure properties (`of_exact_of_exact`, `of_injective`,
  `of_surjective`).
* `Stacks.EtaleCohomology.IsCharpolyNormMixedOfWeightLE.of_pow`: weights of `f` from weights of
  `f ^ m` measured against `q ^ m`.
* `Stacks.EtaleCohomology.isCharpolyMixedOfWeightLE_of_forall_isCharpolyNormMixedOfWeightLE`: the
  absolute-value bound along every `ι` gives mixedness, algebraicity included.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace Stacks.EtaleCohomology

variable {K : Type*} [Field K] {L : Type*} [Field L]

section BaseChange

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The roots in `L` of the characteristic polynomial of `f` mapped along `ι : K →+* L` are the
eigenvalues of the extension of scalars of `f` to `L` along `ι`. -/
public theorem isRoot_charpoly_map_iff_hasEigenvalue_baseChange (ι : K →+* L)
    (f : Module.End K V) (z : L) :
    letI := ι.toAlgebra
    (f.charpoly.map ι).IsRoot z ↔ Module.End.HasEigenvalue (f.baseChange L) z := by
  let := ι.toAlgebra
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange]
  rfl

end BaseChange

section Exact

variable {A B C : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [FiniteDimensional K A] [FiniteDimensional K B]
  [FiniteDimensional K C] {fA : Module.End K A} {fB : Module.End K B} {fC : Module.End K C}

/-- The extension of scalars of an equivariant linear map is equivariant. -/
private theorem baseChange_comm (ι : K →+* L) {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {fM : Module.End K M} {fN : Module.End K N} {g : M →ₗ[K] N}
    (hg : ∀ m, g (fM m) = fN (g m)) :
    letI := ι.toAlgebra
    ∀ x, g.baseChange L (fM.baseChange L x) = fN.baseChange L (g.baseChange L x) := by
  let := ι.toAlgebra
  have h : g.baseChange L ∘ₗ fM.baseChange L = fN.baseChange L ∘ₗ g.baseChange L := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact LinearMap.ext hg
  exact LinearMap.congr_fun h

/-- **Characteristic roots in an exact sequence.**  If `j : A → B` and `p : B → C` intertwine
`fA`, `fB`, `fC` and `A → B → C` is exact, then every root in `L` of the characteristic
polynomial of `fB` mapped along `ι` is a root of that of `fA` or of that of `fC`. -/
public theorem isRoot_charpoly_map_or_of_exact (ι : K →+* L) {j : A →ₗ[K] B} {p : B →ₗ[K] C}
    (hj : ∀ a, j (fA a) = fB (j a)) (hp : ∀ b, p (fB b) = fC (p b))
    (hexact : Function.Exact j p) {z : L} (hz : (fB.charpoly.map ι).IsRoot z) :
    (fA.charpoly.map ι).IsRoot z ∨ (fC.charpoly.map ι).IsRoot z := by
  let := ι.toAlgebra
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz ⊢
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange]
  have hexL : Function.Exact (j.baseChange L) (p.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact L hexact
  exact hasEigenvalue_or_of_exact (baseChange_comm ι hj) (baseChange_comm ι hp)
    (fun b hb => (hexL b).1 hb) hz

/-- The characteristic roots of an equivariant subobject are characteristic roots of the whole. -/
public theorem isRoot_charpoly_map_of_injective (ι : K →+* L) {j : A →ₗ[K] B}
    (hj : ∀ a, j (fA a) = fB (j a)) (hinj : Function.Injective j) {z : L}
    (hz : (fA.charpoly.map ι).IsRoot z) : (fB.charpoly.map ι).IsRoot z := by
  let := ι.toAlgebra
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz ⊢
  have hinjL : Function.Injective (j.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap j hinj
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := j.baseChange L v) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, ← baseChange_comm ι hj, hv.apply_eq_smul, map_smul]
  · exact fun h => hv.2 (hinjL (h.trans (map_zero _).symm))

/-- The characteristic roots of an equivariant quotient are characteristic roots of the whole. -/
public theorem isRoot_charpoly_map_of_surjective (ι : K →+* L) {p : B →ₗ[K] C}
    (hp : ∀ b, p (fB b) = fC (p b)) (hsurj : Function.Surjective p) {z : L}
    (hz : (fC.charpoly.map ι).IsRoot z) : (fB.charpoly.map ι).IsRoot z := by
  let := ι.toAlgebra
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz ⊢
  have hsurjL : Function.Surjective (p.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective L hsurj
  exact hasEigenvalue_of_surjective hsurjL (baseChange_comm ι hp) hz

/-- **Mixedness along an exact sequence.**  If `A → B → C` is an equivariant exact sequence and
the actions on `A` and `C` are mixed of weight at most `i`, so is the action on `B`. -/
public theorem IsCharpolyMixedOfWeightLE.of_exact_of_exact {q : ℕ} {ι : K →+* ℂ} {i : ℤ}
    {j : A →ₗ[K] B} {p : B →ₗ[K] C} (hA : IsCharpolyMixedOfWeightLE q ι i fA)
    (hC : IsCharpolyMixedOfWeightLE q ι i fC) (hj : ∀ a, j (fA a) = fB (j a))
    (hp : ∀ b, p (fB b) = fC (p b)) (hexact : Function.Exact j p) :
    IsCharpolyMixedOfWeightLE q ι i fB := fun z hz =>
  (isRoot_charpoly_map_or_of_exact ι hj hp hexact hz).elim (hA z) (hC z)

/-- Mixedness passes to equivariant subobjects. -/
public theorem IsCharpolyMixedOfWeightLE.of_injective {q : ℕ} {ι : K →+* ℂ} {i : ℤ}
    {j : A →ₗ[K] B} (hB : IsCharpolyMixedOfWeightLE q ι i fB) (hj : ∀ a, j (fA a) = fB (j a))
    (hinj : Function.Injective j) : IsCharpolyMixedOfWeightLE q ι i fA := fun z hz =>
  hB z (isRoot_charpoly_map_of_injective ι hj hinj hz)

/-- Mixedness passes to equivariant quotients. -/
public theorem IsCharpolyMixedOfWeightLE.of_surjective {q : ℕ} {ι : K →+* ℂ} {i : ℤ}
    {p : B →ₗ[K] C} (hB : IsCharpolyMixedOfWeightLE q ι i fB) (hp : ∀ b, p (fB b) = fC (p b))
    (hsurj : Function.Surjective p) : IsCharpolyMixedOfWeightLE q ι i fC := fun z hz =>
  hB z (isRoot_charpoly_map_of_surjective ι hp hsurj hz)

/-- Mixedness of weight at most `i` implies mixedness of weight at most `i'` for `i ≤ i'`. -/
public theorem IsCharpolyMixedOfWeightLE.mono {q : ℕ} {ι : K →+* ℂ} {i i' : ℤ}
    (h : IsCharpolyMixedOfWeightLE q ι i fA) (hi : i ≤ i') :
    IsCharpolyMixedOfWeightLE q ι i' fA := fun z hz =>
  (h z hz).imp fun _ => And.imp_left (·.trans hi)

end Exact

/-! ### Characteristic roots of powers -/

section Pow

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If `z` is a characteristic root of `f` along `ι`, then `z ^ m` is one of `f ^ m`. -/
public theorem isRoot_charpoly_map_pow (ι : K →+* L) {f : Module.End K V} {z : L}
    (hz : (f.charpoly.map ι).IsRoot z) (m : ℕ) : ((f ^ m).charpoly.map ι).IsRoot (z ^ m) := by
  let := ι.toAlgebra
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz ⊢
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hpow : ∀ n : ℕ, (f ^ n).baseChange L v = z ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, LinearMap.baseChange_mul, Module.End.mul_apply, hv.apply_eq_smul, map_smul,
        ih, smul_smul, pow_succ, mul_comm]
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    ⟨Module.End.mem_eigenspace_iff.2 (hpow m), hv.2⟩

end Pow

/-! ### Mixedness read on absolute values -/

section Norm

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The absolute-value half of `Stacks.EtaleCohomology.IsCharpolyMixedOfWeightLE`: every complex
root of the characteristic polynomial of `f` along `ι` has absolute value `q ^ (w / 2)` for an
integer `w ≤ i`.  Algebraicity of the roots is not asked for; it is recovered when the bound holds
along every `ι` (`Stacks.EtaleCohomology.isCharpolyMixedOfWeightLE_of_forall_norm_eq`). -/
public def IsCharpolyNormMixedOfWeightLE (q : ℕ) (ι : K →+* ℂ) (i : ℤ) (f : Module.End K V) :
    Prop :=
  ∀ z : ℂ, (f.charpoly.map ι).IsRoot z → ∃ w ≤ i, ‖z‖ = (q : ℝ) ^ ((w : ℝ) / 2)

/-- Mixedness gives its absolute-value half. -/
public theorem IsCharpolyMixedOfWeightLE.isCharpolyNormMixedOfWeightLE {q : ℕ} {ι : K →+* ℂ}
    {i : ℤ} {f : Module.End K V} (h : IsCharpolyMixedOfWeightLE q ι i f) :
    IsCharpolyNormMixedOfWeightLE q ι i f := fun z hz =>
  (h z hz).imp fun _ => And.imp_right (·.norm_eq)

/-- The absolute-value bound along every `ι` gives mixedness along every `ι`. -/
public theorem isCharpolyMixedOfWeightLE_of_forall_isCharpolyNormMixedOfWeightLE {K : Type}
    [Field K] [CharZero K] (hK : Cardinal.mk K ≤ Cardinal.mk ℂ) {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {q : ℕ} (hq : 1 ≤ q) {i : ℤ} {f : Module.End K V}
    (h : ∀ ι : K →+* ℂ, IsCharpolyNormMixedOfWeightLE q ι i f) (ι : K →+* ℂ) :
    IsCharpolyMixedOfWeightLE q ι i f :=
  isCharpolyMixedOfWeightLE_of_forall_norm_eq hK hq h ι

/-- Monotonicity in the weight. -/
public theorem IsCharpolyNormMixedOfWeightLE.mono {q : ℕ} {ι : K →+* ℂ} {i i' : ℤ}
    {f : Module.End K V} (h : IsCharpolyNormMixedOfWeightLE q ι i f) (hi : i ≤ i') :
    IsCharpolyNormMixedOfWeightLE q ι i' f := fun z hz =>
  (h z hz).imp fun _ => And.imp_left (·.trans hi)

/-- **Weights from a power.**  If the characteristic roots of `f ^ m` (`m ≠ 0`) have absolute
values `(q ^ m) ^ (w / 2)` with `w ≤ i`, then the characteristic roots of `f` have absolute values
`q ^ (w / 2)` with `w ≤ i`. -/
public theorem IsCharpolyNormMixedOfWeightLE.of_pow {q : ℕ} {ι : K →+* ℂ} {i : ℤ}
    {f : Module.End K V} {m : ℕ} (hm : m ≠ 0)
    (h : IsCharpolyNormMixedOfWeightLE (q ^ m) ι i (f ^ m)) :
    IsCharpolyNormMixedOfWeightLE q ι i f := fun z hz => by
  obtain ⟨w, hw, hzm⟩ := h (z ^ m) (isRoot_charpoly_map_pow ι hz m)
  refine ⟨w, hw, ?_⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hrhs : ((q ^ m : ℕ) : ℝ) ^ ((w : ℝ) / 2) = ((q : ℝ) ^ ((w : ℝ) / 2)) ^ m := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0,
      ← Real.rpow_mul hq0, mul_comm]
  rw [norm_pow, hrhs] at hzm
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hq0 _) hm).1 hzm

end Norm

section NormExact

variable {A B C : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [FiniteDimensional K A] [FiniteDimensional K B]
  [FiniteDimensional K C] {fA : Module.End K A} {fB : Module.End K B} {fC : Module.End K C}
  {q : ℕ} {ι : K →+* ℂ} {i : ℤ}

/-- The absolute-value bound along an exact sequence. -/
public theorem IsCharpolyNormMixedOfWeightLE.of_exact_of_exact {j : A →ₗ[K] B} {p : B →ₗ[K] C}
    (hA : IsCharpolyNormMixedOfWeightLE q ι i fA) (hC : IsCharpolyNormMixedOfWeightLE q ι i fC)
    (hj : ∀ a, j (fA a) = fB (j a)) (hp : ∀ b, p (fB b) = fC (p b))
    (hexact : Function.Exact j p) : IsCharpolyNormMixedOfWeightLE q ι i fB := fun z hz =>
  (isRoot_charpoly_map_or_of_exact ι hj hp hexact hz).elim (hA z) (hC z)

/-- The absolute-value bound passes to equivariant subobjects. -/
public theorem IsCharpolyNormMixedOfWeightLE.of_injective {j : A →ₗ[K] B}
    (hB : IsCharpolyNormMixedOfWeightLE q ι i fB) (hj : ∀ a, j (fA a) = fB (j a))
    (hinj : Function.Injective j) : IsCharpolyNormMixedOfWeightLE q ι i fA := fun z hz =>
  hB z (isRoot_charpoly_map_of_injective ι hj hinj hz)

/-- The absolute-value bound passes to equivariant quotients. -/
public theorem IsCharpolyNormMixedOfWeightLE.of_surjective {p : B →ₗ[K] C}
    (hB : IsCharpolyNormMixedOfWeightLE q ι i fB) (hp : ∀ b, p (fB b) = fC (p b))
    (hsurj : Function.Surjective p) : IsCharpolyNormMixedOfWeightLE q ι i fC := fun z hz =>
  hB z (isRoot_charpoly_map_of_surjective ι hp hsurj hz)

end NormExact

end Stacks.EtaleCohomology

end
