module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerCharpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IrreducibleLieNormalizer
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The normalizer of a semisimple linear Lie algebra

Let `V` be a finite-dimensional vector space over an algebraically closed field `K` of
characteristic zero and let `𝔤 ⊆ 𝔤𝔩(V)` be a Lie subalgebra for which `V` is a semisimple module
(the sum of its irreducible `𝔤`-submodules). Then the normalizer of `𝔤` in `𝔤𝔩(V)` is `𝔤 + 𝔷`,
where `𝔷` is the centralizer of `𝔤`: every endomorphism `n` with `[n, 𝔤] ⊆ 𝔤` is an element of
`𝔤` plus an endomorphism commuting with `𝔤`.

This is the Lie-algebra form of Kedlaya, *Fourier transforms and p-adic Weil II*, Proposition
6.1.3 (Deligne, Weil II 1.3.9), for a module which is semisimple but not necessarily irreducible.

## Main results

* `Stacks.EtaleCohomology.isNilpotent_of_forall_trace_pow_eq_zero`: in characteristic zero an
  endomorphism all of whose powers have trace zero is nilpotent.
* `Stacks.EtaleCohomology.exists_forall_eq_smul_of_mem_traceRadical`: the radical of the trace form
  acts by a scalar on every irreducible submodule.
* `Stacks.EtaleCohomology.exists_mem_centralizer_sub_mem_of_mem_normalizer`: the normalizer of `𝔤`
  is `𝔤 + 𝔷`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.3.9.
* K. Kedlaya, *Fourier transforms and p-adic "Weil II"*, Compos. Math. 142 (2006), Proposition
  6.1.3.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

open LieModule LieAlgebra Module Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [CharZero K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [CharZero K] [IsAlgClosed K] in
/-- The diagonal of a power of an upper triangular matrix. -/
private theorem pow_apply_self_of_isUpperTriangular {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (hA : A.IsUpperTriangular) (k : ℕ) (i : Fin n) : (A ^ k) i i = A i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i, ih, pow_succ]
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · rw [(hA.pow k) h, zero_mul]
      · rw [hA h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

/-- **Trace criterion for nilpotence.** In characteristic zero, an endomorphism `f` of a
finite-dimensional vector space with `tr(fᵏ) = 0` for every `k ≥ 1` is nilpotent. -/
theorem isNilpotent_of_forall_trace_pow_eq_zero {f : Module.End K V}
    (h : ∀ k, 0 < k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_isUpperTriangular_toMatrix f
  set A := LinearMap.toMatrix b b f
  set d : Fin (finrank K V) → K := fun i => A i i
  have hsum : ∀ k, ∑ i, d i ^ (k + 1) = 0 := by
    intro k
    have := h (k + 1) k.succ_pos
    rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.toMatrix_pow, Matrix.trace] at this
    have e : ∀ i, (LinearMap.toMatrix b b f ^ (k + 1)).diag i = d i ^ (k + 1) :=
      fun i => pow_apply_self_of_isUpperTriangular hb (k + 1) i
    simpa only [e] using this
  set S := Finset.univ.image d
  let e : Fin S.card ≃ S := S.equivFin.symm
  let x : Fin S.card → K := fun j => (e j : K)
  have hx : Function.Injective x := fun i j hij => e.injective (Subtype.ext hij)
  let m : K → K := fun s => ((Finset.univ.filter fun i => d i = s).card : K)
  let v : Fin S.card → K := fun j => m (x j) * x j
  have hv : Matrix.vecMul v (Matrix.vandermonde x) = 0 := by
    funext k
    rw [Matrix.vecMul, dotProduct, Pi.zero_apply]
    have h1 : ∑ j, v j * Matrix.vandermonde x j k = ∑ s ∈ S, m s * s ^ ((k : ℕ) + 1) := by
      rw [← Finset.sum_coe_sort S, ← e.sum_comp]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [v, Matrix.vandermonde_apply, x, pow_succ]
      ring
    rw [h1, ← hsum k, Finset.sum_comp (fun s => s ^ ((k : ℕ) + 1)) d]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [nsmul_eq_mul]
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hx) hv
  have hd : ∀ i, d i = 0 := by
    intro i
    have hi : d i ∈ S := Finset.mem_image_of_mem d (Finset.mem_univ i)
    have hj := congrFun hv0 (e.symm ⟨d i, hi⟩)
    simp only [v, x, Equiv.apply_symm_apply, Pi.zero_apply, mul_eq_zero] at hj
    exact hj.resolve_left (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨i, by simp⟩).ne')
  have hchar : f.charpoly = X ^ finrank K V := by
    rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_of_isUpperTriangular _ hb]
    simp [show ∀ i, A i i = 0 from hd]
  refine ⟨finrank K V, ?_⟩
  have := LinearMap.aeval_self_charpoly f
  rwa [hchar, map_pow, aeval_X] at this

/-- The radical of the trace form acts by a scalar on every irreducible submodule. -/
theorem exists_forall_eq_smul_of_mem_traceRadical (g : LieSubalgebra K (Module.End K V))
    {W : LieSubmodule K g V} (hW : IsAtom W) (a : traceRadical g) :
    ∃ c : K, ∀ w ∈ W, ((a : g) : Module.End K V) w = c • w := by
  have : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot K g V).mpr hW.1
  have := isSolvable_traceRadical g
  obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K (traceRadical g) W
  let N : LieSubmodule K g W := weightSpaceOfIsLieTower K W χ
  have hN : N ≠ ⊥ := (LieSubmodule.nontrivial_iff_ne_bot K g W).mp hχ
  have hmap : N.map W.incl = W := by
    refine (hW.le_iff.mp LieSubmodule.map_incl_le).resolve_left fun h => hN ?_
    rw [eq_bot_iff]
    intro w hw
    have : (w : V) ∈ N.map W.incl := (LieSubmodule.mem_map _).mpr ⟨w, hw, rfl⟩
    rw [h, LieSubmodule.mem_bot] at this
    exact (LieSubmodule.mem_bot _).mpr (Subtype.ext this)
  refine ⟨χ a, fun w hw => ?_⟩
  rw [← hmap] at hw
  obtain ⟨w', hw', rfl⟩ := (LieSubmodule.mem_map _).mp hw
  have h1 : ⁅a, w'⁆ = χ a • w' := (mem_weightSpace χ w').mp hw' a
  exact congrArg Subtype.val h1

variable {g : LieSubalgebra K (Module.End K V)}

/-- An element of the radical of the trace form commutes with `𝔤`, when `V` is semisimple. -/
theorem commute_of_mem_traceRadical (hss : sSup {W : LieSubmodule K g V | IsAtom W} = ⊤)
    (a : traceRadical g) {y : Module.End K V} (hy : y ∈ g) :
    Commute ((a : g) : Module.End K V) y := by
  set A := ((a : g) : Module.End K V)
  suffices h : (⊤ : Submodule K V) ≤ LinearMap.ker (A * y - y * A) by
    exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp (top_le_iff.mp h))
  rw [← LieSubmodule.top_toSubmodule (R := K) (L := g), ← hss, LieSubmodule.sSup_toSubmodule,
    sSup_le_iff]
  rintro _ ⟨W, hW, rfl⟩ w hw
  obtain ⟨c, hc⟩ := exists_forall_eq_smul_of_mem_traceRadical g hW a
  have hyw : y w ∈ W := W.lie_mem (x := ⟨y, hy⟩) hw
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    hc _ hyw, hc _ hw, map_smul, sub_self]

/-- A nilpotent element of the radical of the trace form is zero, when `V` is semisimple. -/
theorem eq_zero_of_mem_traceRadical_of_isNilpotent
    (hss : sSup {W : LieSubmodule K g V | IsAtom W} = ⊤) (a : traceRadical g)
    (ha : IsNilpotent ((a : g) : Module.End K V)) : ((a : g) : Module.End K V) = 0 := by
  obtain ⟨k, hk⟩ := ha
  suffices h : (⊤ : Submodule K V) ≤ LinearMap.ker ((a : g) : Module.End K V) by
    exact LinearMap.ker_eq_top.mp (top_le_iff.mp h)
  rw [← LieSubmodule.top_toSubmodule (R := K) (L := g), ← hss, LieSubmodule.sSup_toSubmodule,
    sSup_le_iff]
  rintro _ ⟨W, hW, rfl⟩ w hw
  obtain ⟨c, hc⟩ := exists_forall_eq_smul_of_mem_traceRadical g hW a
  have : Nontrivial W := (LieSubmodule.nontrivial_iff_ne_bot K g V).mpr hW.1
  obtain ⟨⟨w₀, hw₀⟩, hw₀0'⟩ := exists_ne (0 : W)
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀0' (Subtype.ext h)
  have hpow : ∀ j, (((a : g) : Module.End K V) ^ j) w₀ = c ^ j • w₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc _ hw₀, smul_smul, ← pow_succ]
  have hc0 : c = 0 := by
    have := hpow k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    exact eq_zero_of_pow_eq_zero (this.resolve_right hw₀0)
  rw [LinearMap.mem_ker, hc _ hw, hc0, zero_smul]

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K V] in
/-- A functional on a finite-dimensional space vanishing on the common kernel of a family of
functionals lies in their span. -/
private theorem mem_range_of_forall_eq_zero {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] (φ : M →ₗ[K] Module.Dual K N)
    (lam : Module.Dual K N) (h : ∀ y : N, (∀ m, φ m y = 0) → lam y = 0) :
    lam ∈ LinearMap.range φ := by
  by_contra hl
  obtain ⟨F, hF, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hl inferInstance
  set y := (Module.evalEquiv K N).symm F
  have hy : ∀ μ : Module.Dual K N, μ y = F μ := fun μ => by simp [y]
  refine hF ?_
  rw [← hy]
  refine h y fun m => ?_
  rw [hy]
  have : F (φ m) ∈ (LinearMap.range φ).map F :=
    Submodule.mem_map_of_mem (LinearMap.mem_range_self φ m)
  rwa [hmap, Submodule.mem_bot] at this

/-- **The normalizer of a semisimple linear Lie algebra** (the Lie-algebra form of Weil II
1.3.9). If `V` is the sum of its irreducible `𝔤`-submodules, over an algebraically closed field of
characteristic zero, then every `n` normalizing `𝔤` is an element of `𝔤` plus an endomorphism
commuting with `𝔤`. -/
theorem exists_mem_centralizer_sub_mem_of_mem_normalizer
    (hss : sSup {W : LieSubmodule K g V | IsAtom W} = ⊤) {n : Module.End K V}
    (hn : n ∈ g.normalizer) :
    ∃ z ∈ Subalgebra.centralizer K (g : Set (Module.End K V)), n - z ∈ g := by
  rw [LieSubalgebra.mem_normalizer_iff] at hn
  set Z := Subalgebra.centralizer K (g : Set (Module.End K V))
  set R := traceRadical g
  let P : Module.End K V →ₗ[K] Module.End K V →ₗ[K] K :=
    (LinearMap.mul K (Module.End K V)).compr₂ (LinearMap.trace K V)
  have hP : ∀ x y, P x y = LinearMap.trace K V (x * y) := fun _ _ => rfl
  let ιg : g →ₗ[K] Module.End K V := g.toSubmodule.subtype
  let ιR : R →ₗ[K] Module.End K V := ιg ∘ₗ (R : Submodule K g).subtype
  have hRZ : ∀ a : R, ιR a ∈ Z := fun a =>
    (Subalgebra.mem_centralizer_iff K).mpr fun y hy =>
      (commute_of_mem_traceRadical hss a hy).symm.eq
  obtain ⟨z₀, hz₀⟩ := mem_range_of_forall_eq_zero (P.compl₁₂ Z.toSubmodule.subtype ιR)
    (P n ∘ₗ ιR) (fun h hh => by
      have hnil : IsNilpotent (ιR h) := isNilpotent_of_forall_trace_pow_eq_zero fun k hk => by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := hh ⟨ιR h ^ j, Z.pow_mem (hRZ h) j⟩
        change LinearMap.trace K V (ιR h ^ j * ιR h) = 0 at this
        rwa [← pow_succ] at this
      have h0 : ιR h = 0 := eq_zero_of_mem_traceRadical_of_isNilpotent hss h hnil
      rw [LinearMap.comp_apply, h0, map_zero])
  have hz₀' : ∀ h : R, P (n - z₀) (ιR h) = 0 := fun h => by
    have := LinearMap.congr_fun hz₀ h
    rw [LinearMap.compl₁₂_apply, Submodule.subtype_apply, LinearMap.comp_apply] at this
    rw [map_sub, LinearMap.sub_apply, this, sub_self]
  obtain ⟨a, ha⟩ := mem_range_of_forall_eq_zero (P.compl₁₂ ιg ιg) (P (n - z₀) ∘ₗ ιg)
    (fun y hy => by
      have hyR : y ∈ R := mem_traceRadical.mpr fun x => hy x
      exact hz₀' ⟨y, hyR⟩)
  set b := n - (z₀ : Module.End K V) - (a : Module.End K V)
  have hbperp : ∀ y : g, LinearMap.trace K V (b * y) = 0 := fun y => by
    have := LinearMap.congr_fun ha y
    change LinearMap.trace K V ((a : Module.End K V) * y) =
      LinearMap.trace K V ((n - (z₀ : Module.End K V)) * y) at this
    rw [sub_mul, map_sub, this, sub_self]
  have hz₀g : ∀ y ∈ g, ⁅(z₀ : Module.End K V), y⁆ = 0 := fun y hy => by
    rw [LieRing.of_associative_ring_bracket, sub_eq_zero]
    exact ((Subalgebra.mem_centralizer_iff K).mp z₀.2 y hy).symm
  have hbnorm : ∀ y ∈ g, ⁅b, y⁆ ∈ g := fun y hy => by
    rw [sub_lie, sub_lie, hz₀g y hy, sub_zero]
    exact g.sub_mem (hn y hy) (g.lie_mem a.2 hy)
  have hbZ : b ∈ Z := by
    refine (Subalgebra.mem_centralizer_iff K).mpr fun x hx => ?_
    have hcR : (⟨⁅b, x⁆, hbnorm x hx⟩ : g) ∈ R := by
      refine mem_traceRadical.mpr fun y => ?_
      change LinearMap.trace K V ((y : Module.End K V) * (b * x - x * b)) = 0
      rw [LinearMap.trace_mul_comm, sub_mul, map_sub, mul_assoc, mul_assoc,
        LinearMap.trace_mul_comm K x, mul_assoc, ← map_sub, ← mul_sub]
      exact hbperp ⟨⁅x, (y : Module.End K V)⁆, g.lie_mem hx y.2⟩
    set c : R := ⟨_, hcR⟩
    have hcx : Commute (ιR c) x := commute_of_mem_traceRadical hss c hx
    have hc : ιR c = b * x - x * b := rfl
    have hnil : IsNilpotent (ιR c) := isNilpotent_of_forall_trace_pow_eq_zero fun k hk => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ']
      nth_rewrite 1 [hc]
      rw [sub_mul, map_sub, mul_assoc, mul_assoc, ← (hcx.pow_left j).eq,
        LinearMap.trace_mul_comm K x (b * _), mul_assoc, sub_self]
    have h0 : ιR c = 0 := eq_zero_of_mem_traceRadical_of_isNilpotent hss c hnil
    rw [hc, sub_eq_zero] at h0
    exact h0.symm
  refine ⟨z₀ + b, Z.add_mem z₀.2 hbZ, ?_⟩
  have : n - ((z₀ : Module.End K V) + b) = a := by
    simp only [b]
    abel
  rw [this]
  exact a.2

end Stacks.EtaleCohomology
