module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.Defs
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.FiniteSupportReduce
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsFinite

/-!
# Harder's finiteness theorem from reduction theory and the vanishing near the cusps

Let `K` be a global function field over the finite field `k`. We deduce Harder's finiteness
theorem `Stacks.Adeles.GeneralLinear.FiniteSupportModCenter` (every unramified cusp form on
`GL_n(A)` vanishes outside `GL_n(O) · Z(A) · S · GL_n(K)` for a finite set `S`) from reduction
theory `Stacks.Adeles.GeneralLinear.ReductionTheory` and the vanishing of cusp forms near the
cusps `Stacks.Adeles.GeneralLinear.CuspVanishing`.

Write `x = κ b γ` with `b` upper triangular of diagonal `a` and consecutive gaps
`g_m = N(div a_m - div a_{m+1}) ≥ c₀`, and let `c = min c₀ 1`. If a cusp form `f` does not vanish
at `x`, it does not vanish at `b`, so for every `0 < r < n` there are `i < r ≤ j` with
`N(div a_i - div a_j) < M`; since this norm is the product of the gaps `g_i, …, g_{j-1}`, we get
`g_{r-1} < M / c^{n-1}`. Hence all gaps are bounded above and below, and so are the norms
`N(div a_i - div a_{n-1})`. Multiplying `b` by the central idele `a_{n-1}⁻¹` gives an upper
triangular element with diagonal of bounded norms, which lies in finitely many double cosets
`GL_n(O) · s · GL_n(K)` (`Stacks.Adeles.GeneralLinear.exists_finset_upperTriangular`).

## Main results

* `Stacks.Adeles.GeneralLinear.finiteSupportModCenter_of`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField hiding mapO mapK scalarGL coe_scalarGL

section Central

variable {K : Type u} [Field K] {n : ℕ}

/-- The entries of `scalarGL n z * b` are `z` times those of `b`. -/
public theorem scalarGL_mul_apply (z : (AdeleRing K)ˣ) (b : GL (Fin n) (AdeleRing K))
    (i j : Fin n) :
    ((scalarGL n z * b : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) i j =
      z * (b : Matrix (Fin n) (Fin n) (AdeleRing K)) i j := by
  rw [Units.val_mul, coe_scalarGL, Matrix.scalar_apply, Matrix.diagonal_mul]

/-- Multiplying an upper triangular `b` with diagonal `a` by the scalar `z` gives an upper
triangular element with diagonal `z a`. -/
public theorem IsUpperTriangularWith.scalarGL_mul {b : GL (Fin n) (AdeleRing K)}
    {a : Fin n → (AdeleRing K)ˣ} (hb : IsUpperTriangularWith b a) (z : (AdeleRing K)ˣ) :
    IsUpperTriangularWith (scalarGL n z * b) fun i => z * a i :=
  ⟨fun i j hij => by rw [scalarGL_mul_apply, hb.1 i j hij, mul_zero],
    fun i => by rw [scalarGL_mul_apply, hb.2 i, Units.val_mul]⟩

/-- The group `GL_0(R)` is trivial. -/
public theorem subsingleton_gl_fin_zero (R : Type*) [CommRing R] : Subsingleton (GL (Fin 0) R) :=
  ⟨fun _ _ => Units.ext (Matrix.ext fun i => Fin.elim0 i)⟩

end Central

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k

section Norms

/-- `N(D - F) = N(D - E) N(E - F)`. -/
public theorem divNorm_sub_eq_mul (D E F : Place K →₀ ℤ) :
    divNorm K (D - F) = divNorm K (D - E) * divNorm K (E - F) := by
  rw [← divNorm_add k]
  congr 1
  abel

/-- If the consecutive gaps `N(d_m - d_{m+1})`, `p ≤ m < q`, are at least `c > 0`, then
`N(d_p - d_q) ≥ c ^ (q - p)`. -/
public theorem pow_le_divNorm_sub {d : ℕ → Place K →₀ ℤ} {c : ℚ} (hc : 0 ≤ c) {p q : ℕ}
    (hpq : p ≤ q) (hg : ∀ m, p ≤ m → m < q → c ≤ divNorm K (d m - d (m + 1))) :
    c ^ (q - p) ≤ divNorm K (d p - d q) := by
  induction q, hpq using Nat.le_induction with
  | base => simp [divNorm_zero]
  | succ q hpq ih =>
    rw [divNorm_sub_eq_mul k _ (d q), show q + 1 - p = q - p + 1 by omega, pow_succ]
    exact mul_le_mul (ih fun m h1 h2 => hg m h1 (by omega)) (hg q hpq (by omega)) hc
      (divNorm_pos k _).le

/-- If the consecutive gaps `N(d_m - d_{m+1})`, `p ≤ m < q`, are at most `C`, then
`N(d_p - d_q) ≤ C ^ (q - p)`. -/
public theorem divNorm_sub_le_pow {d : ℕ → Place K →₀ ℤ} {C : ℚ} (hC : 0 ≤ C) {p q : ℕ}
    (hpq : p ≤ q) (hg : ∀ m, p ≤ m → m < q → divNorm K (d m - d (m + 1)) ≤ C) :
    divNorm K (d p - d q) ≤ C ^ (q - p) := by
  induction q, hpq using Nat.le_induction with
  | base => simp [divNorm_zero]
  | succ q hpq ih =>
    rw [divNorm_sub_eq_mul k _ (d q), show q + 1 - p = q - p + 1 by omega, pow_succ]
    exact mul_le_mul (ih fun m h1 h2 => hg m h1 (by omega)) (hg q hpq (by omega))
      (divNorm_pos k _).le (pow_nonneg hC _)

/-- If all consecutive gaps `N(d_l - d_{l+1})`, `l < m`, are at least `0 < c ≤ 1`, then for
`i < r ≤ j ≤ m` the gap at `r - 1` is bounded by `c ^ (-m) N(d_i - d_j)`. -/
public theorem pow_mul_le_divNorm_sub {d : ℕ → Place K →₀ ℤ} {c : ℚ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {m : ℕ} (hg : ∀ l, l < m → c ≤ divNorm K (d l - d (l + 1))) {i r j : ℕ} (hir : i < r)
    (hrj : r ≤ j) (hjm : j ≤ m) :
    c ^ m * divNorm K (d (r - 1) - d r) ≤ divNorm K (d i - d j) := by
  have h1 := pow_le_divNorm_sub k (d := d) hc (show i ≤ r - 1 by omega)
    fun l _ hl => hg l (by omega)
  have h2 := pow_le_divNorm_sub k (d := d) hc hrj fun l _ hl => hg l (by omega)
  have hsplit : divNorm K (d i - d j) =
      divNorm K (d i - d (r - 1)) * divNorm K (d (r - 1) - d r) * divNorm K (d r - d j) := by
    rw [divNorm_sub_eq_mul k _ (d (r - 1)), divNorm_sub_eq_mul k (d (r - 1)) (d r), mul_assoc]
  have hpow : c ^ m ≤ c ^ (r - 1 - i) * c ^ (j - r) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hc hc1 (by omega)
  have hA : c ^ (r - 1 - i) * c ^ (j - r) ≤ divNorm K (d i - d (r - 1)) * divNorm K (d r - d j) :=
    mul_le_mul h1 h2 (pow_nonneg hc _) (divNorm_pos k _).le
  have hgpos := (divNorm_pos k (d (r - 1) - d r)).le
  rw [hsplit]
  calc c ^ m * divNorm K (d (r - 1) - d r)
      ≤ (c ^ (r - 1 - i) * c ^ (j - r)) * divNorm K (d (r - 1) - d r) :=
        mul_le_mul_of_nonneg_right hpow hgpos
    _ ≤ (divNorm K (d i - d (r - 1)) * divNorm K (d r - d j)) * divNorm K (d (r - 1) - d r) :=
        mul_le_mul_of_nonneg_right hA hgpos
    _ = _ := by ring

/-- **Bounded gaps**: let `d_0, …, d_m` be divisors whose consecutive gaps `N(d_l - d_{l+1})` are
at least `0 < c ≤ 1`, and such that every `0 < r ≤ m` has `i < r ≤ j ≤ m` with
`N(d_i - d_j) < M`. Then `B⁻¹ ≤ N(d_i - d_m) ≤ B` for all `i ≤ m`, where `B` depends on
`c`, `M` and `m` alone. -/
public theorem divNorm_sub_mem_Icc {d : ℕ → Place K →₀ ℤ} {c M : ℚ} (hc : 0 < c) (hc1 : c ≤ 1)
    {m : ℕ} (hg : ∀ l, l < m → c ≤ divNorm K (d l - d (l + 1)))
    (hM : ∀ r, 0 < r → r ≤ m → ∃ i j, i < r ∧ r ≤ j ∧ j ≤ m ∧ divNorm K (d i - d j) < M)
    {i : ℕ} (hi : i ≤ m) :
    (max (max 1 (M / c ^ m) ^ m) (c ^ m)⁻¹)⁻¹ ≤ divNorm K (d i - d m) ∧
      divNorm K (d i - d m) ≤ max (max 1 (M / c ^ m) ^ m) (c ^ m)⁻¹ := by
  set C := max 1 (M / c ^ m)
  have hcm : 0 < c ^ m := pow_pos hc m
  have hC1 : 1 ≤ C := le_max_left _ _
  have hgC : ∀ l, l < m → divNorm K (d l - d (l + 1)) ≤ C := by
    intro l hl
    obtain ⟨i, j, hir, hrj, hjm, hlt⟩ := hM (l + 1) (by omega) (by omega)
    have h := pow_mul_le_divNorm_sub k hc.le hc1 hg hir hrj hjm
    rw [show l + 1 - 1 = l by omega] at h
    have : divNorm K (d l - d (l + 1)) < M / c ^ m := by
      rw [lt_div_iff₀ hcm]
      linarith
    exact this.le.trans (le_max_right _ _)
  have hlow : c ^ m ≤ divNorm K (d i - d m) :=
    (pow_le_pow_of_le_one hc.le hc1 (by omega : m - i ≤ m)).trans
      (pow_le_divNorm_sub k hc.le hi fun l _ hl => hg l hl)
  have hup : divNorm K (d i - d m) ≤ C ^ m :=
    (divNorm_sub_le_pow k (by linarith) hi fun l _ hl => hgC l hl).trans
      (pow_le_pow_right₀ hC1 (by omega))
  refine ⟨?_, hup.trans (le_max_left _ _)⟩
  have h := inv_anti₀ (inv_pos.2 hcm) (le_max_right (C ^ m) (c ^ m)⁻¹)
  rw [inv_inv] at h
  exact h.trans hlow

end Norms

/-- **Harder's finiteness theorem** from reduction theory and the vanishing of cusp forms near
the cusps: there is a finite set `S ⊆ GL_n(A)` such that every unramified cusp form vanishes
outside `GL_n(O) · Z(A) · S · GL_n(K)`. -/
public theorem finiteSupportModCenter_of (n : ℕ) (hR : ReductionTheory K n k)
    (hV : CuspVanishing.{u, w} K n k) : FiniteSupportModCenter.{u, w} K n := by
  rcases n with _ | m
  · refine ⟨{1}, fun Λ _ f _ x _ => ⟨1, Finset.mem_singleton_self _, 1, 1, 1, ?_⟩⟩
    have := subsingleton_gl_fin_zero (AdeleRing K)
    exact Subsingleton.elim _ _
  obtain ⟨c₀, hc₀, hR⟩ := hR
  obtain ⟨M, hV⟩ := hV
  set c := min c₀ 1
  have hc : 0 < c := lt_min hc₀ one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  obtain ⟨S, hS⟩ := exists_finset_upperTriangular k (K := K) (n := m + 1)
    (max (max 1 (M / c ^ m) ^ m) (c ^ m)⁻¹)
  refine ⟨S, fun Λ _ f hf x hfx => ?_⟩
  obtain ⟨κ, γ, b, a, hx, hb, hgap⟩ := hR x
  have hfb : f b ≠ 0 := by
    rwa [hx, hf.right_invariant, hf.left_invariant] at hfx
  let d : ℕ → Place K →₀ ℤ := fun i => if h : i < m + 1 then idelDiv k K (a ⟨i, h⟩) else 0
  have hd : ∀ i : Fin (m + 1), d i = idelDiv k K (a i) := fun i => by
    simp only [d, i.isLt, ↓reduceDIte, Fin.eta]
  have hg : ∀ l, l < m → c ≤ divNorm K (d l - d (l + 1)) := by
    intro l hl
    have h := hgap ⟨l, by omega⟩ ⟨l + 1, by omega⟩ rfl
    rw [← hd, ← hd] at h
    exact (min_le_left _ _).trans h
  have hM : ∀ r, 0 < r → r ≤ m → ∃ i j, i < r ∧ r ≤ j ∧ j ≤ m ∧ divNorm K (d i - d j) < M := by
    intro r hr hrm
    by_contra hcon
    push Not at hcon
    refine hfb (hV Λ f hf b a hb r hr (by omega) fun i j hi hj => ?_)
    rw [← hd, ← hd]
    exact hcon i j hi hj (by omega)
  set z := (a (Fin.last m))⁻¹
  have hb' := hb.scalarGL_mul z
  have hbound : ∀ i, (max (max 1 (M / c ^ m) ^ m) (c ^ m)⁻¹)⁻¹ ≤
      divNorm K (idelDiv k K (z * a i)) ∧
        divNorm K (idelDiv k K (z * a i)) ≤ max (max 1 (M / c ^ m) ^ m) (c ^ m)⁻¹ := by
    intro i
    have hdiv : idelDiv k K (z * a i) = d i - d m := by
      have hm := hd (Fin.last m)
      rw [Fin.val_last] at hm
      rw [idelDiv_mul, idelDiv_inv, hd i, hm]
      abel
    rw [hdiv]
    exact divNorm_sub_mem_Icc k hc hc1 hg hM (Nat.lt_succ_iff.1 i.isLt)
  obtain ⟨s, hs, υ, ν, hsb⟩ := hS _ _ hb' hbound
  have hbz : b = scalarGL (m + 1) z⁻¹ * (scalarGL (m + 1) z * b) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  refine ⟨s, hs, κ * υ, z⁻¹, ν * γ, ?_⟩
  rw [hx, hbz, hsb, map_mul, map_mul]
  calc mapO K (m + 1) κ * (scalarGL (m + 1) z⁻¹ * (mapO K (m + 1) υ * s * mapK K (m + 1) ν)) *
        mapK K (m + 1) γ =
      mapO K (m + 1) κ * (scalarGL (m + 1) z⁻¹ * mapO K (m + 1) υ) * s *
        (mapK K (m + 1) ν * mapK K (m + 1) γ) := by simp only [mul_assoc]
    _ = _ := by rw [scalarGL_mul_comm]; simp only [mul_assoc]

end Stacks.Adeles.GeneralLinear

end
