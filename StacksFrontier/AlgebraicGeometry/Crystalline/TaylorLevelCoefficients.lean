module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# The Taylor coefficients of a crystal at one level

In the proof of [Stacks, Lemma 60.17.3, Tag 07JG] a crystal `ℱ` is evaluated on the objects
`T_e = Spec(D_e)`, `T(1)_e = Spec(D(1)_e)` and `T(2)_e = Spec(D(2)_e)`.  Writing
`M_e = Γ(T_e, ℱ)` and `r_φ` for the restriction maps of `ℱ` along the cosimplicial maps, the
crystal property identifies `Γ(T(1)_e, ℱ)` with `D(1)_e ⊗_{D_e, p₀} M_e`, and `D(1)_e` is free
over `D_e` on the divided power monomials `ξ^{[K]}`.  So every section over `T(1)_e` is uniquely
`∑_K ξ^{[K]} · r_{p₀}(m_K)`, and applied to `r_{p₁}(m)` this defines the operators `θ_K` of the
source:

`r_{p₁}(m) = ∑_K ξ^{[K]} · r_{p₀}(θ_K(m))`.

This module isolates the algebra of that step, at one level and with no geometry: three modules
`M₀`, `M₁`, `M₂`, the restriction maps between them, and the two bijectivity statements.

* `Crystalline.TaylorExpansion` — a pair of maps `a₀, a₁ : M₀ → M₁` and a family `ξ_K` of scalars
  such that `(m_K)_K ↦ ∑_K ξ_K · a₀(m_K)` is bijective; its operators
  `Crystalline.TaylorExpansion.theta` are read off `a₁`.
* `Crystalline.TaylorExpansion.theta_zero` — `θ_0 = id`, from a common retraction of `a₀` and `a₁`
  (the restriction along the diagonal).
* `Crystalline.TaylorExpansion.theta_theta` — **`θ_L ∘ θ_K = θ_{K + L}`**, from the restrictions
  to `M₂` along the three cofaces `D(1) → D(2)`, when `M₂` is free over `M₀` on the monomials
  `v^{[K]} u^{[L]}` in `u = x ⊗ 1 ⊗ 1 - 1 ⊗ x ⊗ 1` and `v = 1 ⊗ x ⊗ 1 - 1 ⊗ 1 ⊗ x`.  This is the
  comparison of coefficients of the source's cocycle condition `q₀₂^* c = q₁₂^* c ∘ q₀₁^* c`.
* `Crystalline.TaylorExpansion.theta_single_smul` — the Leibniz rule
  `θ_i(f m) = f θ_i(m) + δ_i(f) m` for the first-order operators, where `δ_i(f)` is the
  coefficient of `ξ_i` in `p₁(f)`.
* `Crystalline.TaylorExpansion.theta_naturality` — the operators commute with any map of such data,
  semilinear for a ring map preserving the `ξ_K`: this covers both the restrictions between the
  levels and the morphisms of crystals.
* `Crystalline.bijective_taylorSum_of_basis` — the bijectivity hypothesis from a basis of
  the ring of `T(1)_e` over that of `T_e` together with the crystal base change.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
-/

@[expose] public section

open scoped TensorProduct

namespace Crystalline

variable {ι : Type*}

/-! ### Sums over the monomials -/

section TaylorSum

variable {R : Type*} [CommRing R] {X M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N]

/-- The map `(m_K)_K ↦ ∑_K ξ_K · a(m_K)`, for an additive map `a : N → M` and a family `ξ` of
scalars indexed by `X`. -/
noncomputable def taylorSum (a : N →+ M) (xi : X → R) : (X →₀ N) →+ M :=
  Finsupp.liftAddHom fun K ↦ (smulAddHom R M (xi K)).comp a

/-- The value `taylorSum a ξ g = ∑_K ξ_K • a(g_K)`. -/
theorem taylorSum_apply (a : N →+ M) (xi : X → R) (g : X →₀ N) :
    taylorSum a xi g = g.sum fun K m ↦ xi K • a m := by
  rw [taylorSum, Finsupp.liftAddHom_apply]
  rfl

/-- The map `taylorSum a ξ` sends `single K m` to `ξ_K • a(m)`. -/
@[simp] theorem taylorSum_single (a : N →+ M) (xi : X → R) (K : X) (m : N) :
    taylorSum a xi (Finsupp.single K m) = xi K • a m := by
  rw [taylorSum_apply, Finsupp.sum_single_index (by rw [map_zero, smul_zero])]

end TaylorSum

/-! ### Products of divided power monomials -/

/-- The coefficient of `ξ^{[K + L]}` in `ξ^{[K]} ξ^{[L]}`, `∏_i binom(k_i + l_i, k_i)`. -/
noncomputable def dpMulCoeff (K L : ι →₀ ℕ) : ℕ :=
  (K + L).prod fun i n ↦ n.choose (K i)

/-- The coefficient `dpMulCoeff 0 L` equals `1`. -/
@[simp] theorem dpMulCoeff_zero_left (L : ι →₀ ℕ) : dpMulCoeff 0 L = 1 := by
  simp [dpMulCoeff, Finsupp.prod]

/-- The coefficient `dpMulCoeff K 0` equals `1`. -/
@[simp] theorem dpMulCoeff_zero_right (K : ι →₀ ℕ) : dpMulCoeff K 0 = 1 := by
  simp [dpMulCoeff, Finsupp.prod]

/-- If multi-indices satisfy `K + L = e_i`, then one of `K, L` is `0` and the other is `e_i`. -/
theorem eq_zero_or_eq_single_of_add_eq_single {K L : ι →₀ ℕ} {i : ι}
    (h : K + L = Finsupp.single i 1) :
    (K = 0 ∧ L = Finsupp.single i 1) ∨ (K = Finsupp.single i 1 ∧ L = 0) := by
  classical
  have aux : ∀ {K L : ι →₀ ℕ}, K + L = Finsupp.single i 1 → K i = 0 →
      K = 0 ∧ L = Finsupp.single i 1 := fun {K L} h h0 ↦ by
    have hK : K = 0 := Finsupp.ext fun j ↦ by
      by_cases hj : j = i
      · simpa [hj] using h0
      · have := congrArg (· j) h
        simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne' (Ne.symm hj)] at this
        simpa using (by omega : K j = 0)
    exact ⟨hK, by simpa [hK] using h⟩
  have hi : K i + L i = 1 := by simpa using congrArg (· i) h
  rcases Nat.add_eq_one_iff.mp hi with ⟨h0, -⟩ | ⟨-, h0⟩
  · exact Or.inl (aux h h0)
  · exact Or.inr (aux (add_comm K L ▸ h) h0).symm

/-- Summing `F K (x K)` over the support of `x` against the indicator of `K = m` leaves only the
`m`-th term. -/
private theorem sum_ite_eq_apply_of_map_zero {X A C : Type*} [DecidableEq X] [Zero A]
    [AddCommMonoid C] (x : X →₀ A) (F : X → A → C) (hF : ∀ K, F K 0 = 0) (m : X) :
    (x.sum fun K a ↦ if K = m then F K a else 0) = F m (x m) := by
  rw [Finsupp.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hm, hF]

/-- The double sum over the products of two multi-indices adding up to `e_i` has the two terms
`(0, e_i)` and `(e_i, 0)`. -/
theorem sum_sum_ite_add_eq_single [DecidableEq ι] {A B C : Type*} [Zero A] [Zero B]
    [AddCommMonoid C] (δ : (ι →₀ ℕ) →₀ A) (g : (ι →₀ ℕ) →₀ B)
    (h : (ι →₀ ℕ) → (ι →₀ ℕ) → A → B → C) (h₁ : ∀ K L y, h K L 0 y = 0)
    (h₂ : ∀ K L a, h K L a 0 = 0) (i : ι) :
    (δ.sum fun K a ↦ g.sum fun L y ↦ if K + L = Finsupp.single i 1 then h K L a y else 0) =
      h 0 (Finsupp.single i 1) (δ 0) (g (Finsupp.single i 1)) +
        h (Finsupp.single i 1) 0 (δ (Finsupp.single i 1)) (g 0) := by
  set e : ι →₀ ℕ := Finsupp.single i 1 with he
  have hne : e ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
  have hin : ∀ (K : ι →₀ ℕ) (a : A), (g.sum fun L y ↦ if K + L = e then h K L a y else 0) =
      (if K = 0 then h 0 e a (g e) else 0) + (if K = e then h e 0 a (g 0) else 0) := by
    intro K a
    by_cases hK0 : K = 0
    · subst hK0
      simp only [zero_add, if_neg (Ne.symm hne), add_zero]
      exact sum_ite_eq_apply_of_map_zero g (fun L y ↦ h 0 L a y) (h₂ 0 · a) e
    · by_cases hKe : K = e
      · subst hKe
        have : ∀ L : ι →₀ ℕ, (e + L = e) ↔ L = 0 := fun L ↦ by simp
        simp only [this, if_neg hK0, zero_add]
        exact sum_ite_eq_apply_of_map_zero g (fun L y ↦ h e L a y) (h₂ e · a) 0
      · rw [if_neg hK0, if_neg hKe, add_zero]
        refine Finset.sum_eq_zero fun L _ ↦ if_neg fun h ↦ ?_
        rcases eq_zero_or_eq_single_of_add_eq_single h with ⟨h', -⟩ | ⟨h', -⟩
        · exact hK0 h'
        · exact hKe h'
  simp only [hin]
  rw [Finsupp.sum_add, sum_ite_eq_apply_of_map_zero δ (fun _ a ↦ h 0 e a (g e))
      (fun _ ↦ h₁ 0 e _) 0,
    sum_ite_eq_apply_of_map_zero δ (fun _ a ↦ h e 0 a (g 0)) (fun _ ↦ h₁ e 0 _) e]

/-! ### The expansion datum -/

variable (R : Type*) [CommRing R] (M₀ M₁ : Type*) [AddCommGroup M₀] [AddCommGroup M₁]
  [Module R M₁]

/-- **A Taylor expansion datum at one level.**  Two additive maps `a₀, a₁ : M₀ → M₁` — the
restrictions of a crystal along the two projections `T(1)_e → T_e` — and a family `ξ_K` of scalars
of `M₁`, indexed by the multi-indices `K : ι →₀ ℕ`, such that every element of `M₁` is uniquely a
finite sum `∑_K ξ_K · a₀(m_K)`. -/
structure TaylorExpansion (ι : Type*) where
  /-- The restriction along the first projection. -/
  a₀ : M₀ →+ M₁
  /-- The restriction along the second projection. -/
  a₁ : M₀ →+ M₁
  /-- The divided power monomials `ξ^{[K]}`. -/
  xi : (ι →₀ ℕ) → R
  /-- Every element of `M₁` is uniquely `∑_K ξ_K · a₀(m_K)`. -/
  bijective : Function.Bijective (taylorSum a₀ xi)

namespace TaylorExpansion

variable {R M₀ M₁} (T : TaylorExpansion R M₀ M₁ ι)

/-- The identification `((ι →₀ ℕ) →₀ M₀) ≃ M₁` of a Taylor expansion datum. -/
noncomputable def sumEquiv : ((ι →₀ ℕ) →₀ M₀) ≃+ M₁ :=
  AddEquiv.ofBijective (taylorSum T.a₀ T.xi) T.bijective

/-- The equivalence `T.sumEquiv` is the map `taylorSum T.a₀ T.xi`. -/
@[simp] theorem sumEquiv_apply (g : (ι →₀ ℕ) →₀ M₀) :
    T.sumEquiv g = taylorSum T.a₀ T.xi g := rfl

/-- **The Taylor coefficients of an element**: the unique family `(θ_K(m))_K` with
`a₁(m) = ∑_K ξ_K · a₀(θ_K(m))`. -/
noncomputable def coeffs : M₀ →+ ((ι →₀ ℕ) →₀ M₀) :=
  T.sumEquiv.symm.toAddMonoidHom.comp T.a₁

/-- **The operator `θ_K` of [Stacks, Tag 07JG]**: the `K`-th Taylor coefficient. -/
noncomputable def theta (K : ι →₀ ℕ) : M₀ →+ M₀ :=
  (Finsupp.applyAddHom K).comp T.coeffs

/-- The value `θ_K(m)` is the `K`-th entry of `T.coeffs m`. -/
theorem theta_apply (K : ι →₀ ℕ) (m : M₀) : T.theta K m = T.coeffs m K := rfl

/-- **The first-order Taylor coefficients** `(θ_{e_i}(m))_i`, as a finitely supported family. -/
noncomputable def firstOrderCoeffs : M₀ →+ (ι →₀ M₀) :=
  (Finsupp.comapDomain.addMonoidHom (Finsupp.single_left_injective one_ne_zero)).comp T.coeffs

/-- The `i`-th first-order Taylor coefficient of `m` is `θ_{e_i}(m)`, with `e_i = single i 1`. -/
@[simp] theorem firstOrderCoeffs_apply (m : M₀) (i : ι) :
    T.firstOrderCoeffs m i = T.theta (Finsupp.single i 1) m := rfl

/-- **The Taylor expansion** `a₁(m) = ∑_K ξ_K · a₀(θ_K(m))`. -/
theorem taylorSum_coeffs (m : M₀) : taylorSum T.a₀ T.xi (T.coeffs m) = T.a₁ m :=
  T.sumEquiv.apply_symm_apply (T.a₁ m)

/-- The Taylor expansion, written as a finite sum. -/
theorem a₁_eq_sum (m : M₀) : T.a₁ m = (T.coeffs m).sum fun K y ↦ T.xi K • T.a₀ y := by
  rw [← taylorSum_apply, taylorSum_coeffs]

/-- **Uniqueness of the Taylor coefficients.** -/
theorem coeffs_eq_of_taylorSum {m : M₀} {g : (ι →₀ ℕ) →₀ M₀}
    (h : taylorSum T.a₀ T.xi g = T.a₁ m) : T.coeffs m = g :=
  T.bijective.1 ((T.taylorSum_coeffs m).trans h.symm)

/-! ### The unit: `θ_0 = id` -/

section Unit

variable {R₀ : Type*} [CommRing R₀] [Module R₀ M₀]

/-- **`θ_0 = id`.**  Given the restriction `s` along the diagonal `T_e → T(1)_e`, semilinear over
a ring map `ε` sending `ξ_K` to `1` for `K = 0` and to `0` otherwise, and retracting both `a₀` and
`a₁`, the coefficient of `ξ_0` in `a₁(m)` is `m`. -/
theorem theta_zero (ε : R →+* R₀) (s : M₁ →+ M₀) (hs : ∀ (r : R) (y : M₁), s (r • y) = ε r • s y)
    (hsa₀ : ∀ m, s (T.a₀ m) = m) (hsa₁ : ∀ m, s (T.a₁ m) = m)
    (hε₀ : ε (T.xi 0) = 1) (hε : ∀ K, K ≠ 0 → ε (T.xi K) = 0) (m : M₀) :
    T.theta 0 m = m := by
  classical
  have h := hsa₁ m
  rw [a₁_eq_sum, map_finsuppSum] at h
  simp only [hs, hsa₀] at h
  rw [Finsupp.sum, Finset.sum_eq_single (0 : ι →₀ ℕ)] at h
  · rwa [hε₀, one_smul] at h
  · intro K _ hK
    rw [hε K hK, zero_smul]
  · intro h0
    rw [Finsupp.notMem_support_iff.mp h0, smul_zero]

end Unit

/-! ### Two evaluations of finitely supported families -/

section Evaluation

variable {M : Type*} [AddCommMonoid M]

/-- The family `(x, y) ↦ c(g_x)_y` of the double expansion. -/
theorem sum_sum_single_pair_apply {X : Type*} (g : X →₀ M) (c : M →+ (X →₀ M))
    (a b : X) :
    (g.sum fun K y ↦ (c y).sum fun L z ↦ Finsupp.single (K, L) z) (a, b) = c (g a) b := by
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single a]
  · rw [Finsupp.sum_apply, Finsupp.sum_eq_single b]
    · exact Finsupp.single_eq_same
    · intro L _ hL
      exact Finsupp.single_eq_of_ne' (fun h ↦ hL (congrArg Prod.snd h))
    · intro _
      simp
  · intro K _ hK
    rw [Finsupp.sum_apply]
    exact Finset.sum_eq_zero fun L _ ↦
      Finsupp.single_eq_of_ne' (fun h ↦ hK (congrArg Prod.fst h))
  · intro _
    rw [map_zero, Finsupp.sum_zero_index, Finsupp.zero_apply]

/-- The family `(x, y) ↦ g_{x + y}` of the expansion of `(u + v)^{[N]}`. -/
theorem sum_antidiagonal_single_apply [DecidableEq ι] (g : (ι →₀ ℕ) →₀ M)
    (a b : ι →₀ ℕ) :
    (g.sum fun N y ↦ ∑ x ∈ Finset.antidiagonal N, Finsupp.single x y) (a, b) = g (a + b) := by
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single (a + b)]
  · rw [Finsupp.finset_sum_apply, Finset.sum_eq_single (a, b)]
    · exact Finsupp.single_eq_same
    · intro x _ hx
      exact Finsupp.single_eq_of_ne' hx
    · intro h
      simp at h
  · intro N _ hN
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun x hx ↦ Finsupp.single_eq_of_ne' fun h ↦ hN ?_
    have hx' := Finset.mem_antidiagonal.mp hx
    rw [h] at hx'
    exact hx'.symm
  · intro _
    simp

end Evaluation

/-! ### The cocycle: `θ_L ∘ θ_K = θ_{K + L}` -/

section Cocycle

variable {R₂ : Type*} [CommRing R₂] {M₂ : Type*} [AddCommGroup M₂] [Module R₂ M₂]

/-- **`θ_L ∘ θ_K = θ_{K + L}`**, the comparison of coefficients in the cocycle condition of
[Stacks, Tag 07JG].

The data are the restrictions `b₀₁, b₁₂, b₀₂ : M₁ → M₂` along the three cofaces
`T(2)_e → T(1)_e`, semilinear over ring maps `σ₀₁, σ₁₂, σ₀₂`, and the restriction `c₀` along the
first coprojection `T(2)_e → T_e`; the relations `hb₀₁`–`hb₀₂` are the cosimplicial identities
between the coprojections.  The family `η (K, L) = v^{[K]} u^{[L]}` is such that `σ₀₁` carries
`ξ_L` to `u^{[L]}`, `σ₁₂` carries `ξ_K` to `v^{[K]}` and `σ₀₂` carries `ξ_N` to
`(u + v)^{[N]} = ∑_{K + L = N} v^{[K]} u^{[L]}`, and the hypothesis `hinj` is the freeness of
`M₂` over `M₀` on these monomials. -/
theorem theta_theta [DecidableEq ι] (c₀ : M₀ →+ M₂) (b₀₁ b₁₂ b₀₂ : M₁ →+ M₂)
    (σ₀₁ σ₁₂ σ₀₂ : R →+* R₂)
    (hσ₀₁ : ∀ (r : R) (y : M₁), b₀₁ (r • y) = σ₀₁ r • b₀₁ y)
    (hσ₁₂ : ∀ (r : R) (y : M₁), b₁₂ (r • y) = σ₁₂ r • b₁₂ y)
    (hσ₀₂ : ∀ (r : R) (y : M₁), b₀₂ (r • y) = σ₀₂ r • b₀₂ y)
    (hb₀₁ : ∀ m, b₀₁ (T.a₀ m) = c₀ m) (hb₀₂ : ∀ m, b₀₂ (T.a₀ m) = c₀ m)
    (hb₁₂ : ∀ m, b₁₂ (T.a₀ m) = b₀₁ (T.a₁ m)) (hb₁₂' : ∀ m, b₁₂ (T.a₁ m) = b₀₂ (T.a₁ m))
    (eta : (ι →₀ ℕ) × (ι →₀ ℕ) → R₂)
    (hη₀₁ : ∀ L, σ₀₁ (T.xi L) = eta (0, L)) (hη₁₂ : ∀ K, σ₁₂ (T.xi K) = eta (K, 0))
    (hη₀₂ : ∀ N, σ₀₂ (T.xi N) = ∑ x ∈ Finset.antidiagonal N, eta x)
    (hηmul : ∀ K L, eta (K, 0) * eta (0, L) = eta (K, L))
    (hinj : Function.Injective (taylorSum c₀ eta)) (K L : ι →₀ ℕ) (m : M₀) :
    T.theta L (T.theta K m) = T.theta (K + L) m := by
  -- the two expansions of the restriction of `m` along the third coprojection
  let G₁ : ((ι →₀ ℕ) × (ι →₀ ℕ)) →₀ M₀ :=
    (T.coeffs m).sum fun K y ↦ (T.coeffs y).sum fun L z ↦ Finsupp.single (K, L) z
  let G₂ : ((ι →₀ ℕ) × (ι →₀ ℕ)) →₀ M₀ :=
    (T.coeffs m).sum fun N y ↦ ∑ x ∈ Finset.antidiagonal N, Finsupp.single x y
  have h₁ : taylorSum c₀ eta G₁ = b₁₂ (T.a₁ m) := by
    simp only [G₁, map_finsuppSum, taylorSum_single]
    rw [T.a₁_eq_sum m, map_finsuppSum]
    refine Finsupp.sum_congr fun K _ ↦ ?_
    rw [hσ₁₂, hη₁₂, hb₁₂, T.a₁_eq_sum, map_finsuppSum, Finsupp.smul_sum]
    refine Finsupp.sum_congr fun L _ ↦ ?_
    rw [hσ₀₁, hη₀₁, hb₀₁, smul_smul, hηmul]
  have h₂ : taylorSum c₀ eta G₂ = b₀₂ (T.a₁ m) := by
    simp only [G₂, map_finsuppSum, map_sum, taylorSum_single]
    rw [T.a₁_eq_sum m, map_finsuppSum]
    refine Finsupp.sum_congr fun N _ ↦ ?_
    rw [hσ₀₂, hη₀₂, hb₀₂, Finset.sum_smul]
  have h := congrArg (fun G ↦ G (K, L)) (hinj (h₁.trans ((hb₁₂' m).trans h₂.symm)))
  simp only [G₁, G₂, sum_sum_single_pair_apply, sum_antidiagonal_single_apply] at h
  exact h

end Cocycle

/-! ### The Leibniz rule for the first-order operators -/

section Leibniz

variable {R₀ : Type*} [CommRing R₀] [Module R₀ M₀]

/-- **The Leibniz rule for the first-order Taylor operators**: if `p₁(f)` acts on `M₁` as
`∑_K p₀(δ_K) ξ_K` and the monomials multiply as divided power monomials, then
`θ_i(f m) = δ_0 θ_i(m) + δ_i θ_0(m)`, where `θ_i = θ_{e_i}` and `δ_i = δ_{e_i}`.  With
`Crystalline.TaylorExpansion.theta_zero` and `δ_0 = f` this is `θ_i(f m) = f θ_i(m) + δ_i m`. -/
theorem theta_single_smul (p₀ p₁ : R₀ →+* R)
    (hp₀ : ∀ (a : R₀) (m : M₀), T.a₀ (a • m) = p₀ a • T.a₀ m)
    (hp₁ : ∀ (a : R₀) (m : M₀), T.a₁ (a • m) = p₁ a • T.a₁ m)
    (hxi : ∀ K L, T.xi K * T.xi L = (dpMulCoeff K L : R) * T.xi (K + L))
    (f : R₀) (δ : (ι →₀ ℕ) →₀ R₀)
    (hf : ∀ y : M₁, p₁ f • y = (δ.sum fun K a ↦ p₀ a * T.xi K) • y) (i : ι) (m : M₀) :
    T.theta (Finsupp.single i 1) (f • m) =
      δ 0 • T.theta (Finsupp.single i 1) m + δ (Finsupp.single i 1) • T.theta 0 m := by
  classical
  set g := T.coeffs m with hg
  let G : (ι →₀ ℕ) →₀ M₀ :=
    δ.sum fun K a ↦ g.sum fun L y ↦ Finsupp.single (K + L) ((dpMulCoeff K L : ℕ) • (a • y))
  have key : ∀ K a L y, T.xi (K + L) • T.a₀ ((dpMulCoeff K L : ℕ) • (a • y)) =
      (p₀ a * T.xi K) • (T.xi L • T.a₀ y) := by
    intro K a L y
    rw [map_nsmul, hp₀, ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_smul, smul_smul,
      mul_assoc (p₀ a), hxi]
    congr 1
    ring
  have hG : taylorSum T.a₀ T.xi G = T.a₁ (f • m) := by
    rw [hp₁, hf, T.a₁_eq_sum m]
    simp only [G, map_finsuppSum, taylorSum_single, key]
    simp only [Finsupp.sum, Finset.sum_smul, Finset.smul_sum]
    exact Finset.sum_comm
  rw [theta_apply, T.coeffs_eq_of_taylorSum hG]
  simp only [G, Finsupp.sum_apply, Finsupp.single_apply]
  rw [sum_sum_ite_add_eq_single δ g (fun K L a y ↦ (dpMulCoeff K L : ℕ) • (a • y))
    (fun _ _ _ ↦ by rw [zero_smul, smul_zero]) (fun _ _ _ ↦ by rw [smul_zero, smul_zero]) i]
  simp only [dpMulCoeff_zero_left, dpMulCoeff_zero_right, one_smul, theta_apply, hg]

end Leibniz

/-! ### Naturality -/

section Naturality

variable {R' : Type*} [CommRing R'] {M₀' M₁' : Type*} [AddCommGroup M₀'] [AddCommGroup M₁']
  [Module R' M₁'] (T' : TaylorExpansion R' M₀' M₁' ι)

/-- **The Taylor coefficients are natural**: a pair of additive maps `φ₀ : M₀ → M₀'` and
`φ₁ : M₁ → M₁'`, semilinear over a ring map `τ` carrying `ξ_K` to `ξ'_K` and intertwining the two
restrictions, carries the coefficients of `m` to those of `φ₀(m)`.  For the restrictions between
the levels `τ` is the reduction `D(1)_{e+1} → D(1)_e`; for a morphism of crystals it is the
identity. -/
theorem coeffs_naturality (φ₀ : M₀ →+ M₀') (φ₁ : M₁ →+ M₁') (τ : R →+* R')
    (hφ₁ : ∀ (r : R) (y : M₁), φ₁ (r • y) = τ r • φ₁ y) (hτ : ∀ K, τ (T.xi K) = T'.xi K)
    (h₀ : ∀ m, φ₁ (T.a₀ m) = T'.a₀ (φ₀ m)) (h₁ : ∀ m, φ₁ (T.a₁ m) = T'.a₁ (φ₀ m)) (m : M₀) :
    T'.coeffs (φ₀ m) = (T.coeffs m).mapRange φ₀ (map_zero φ₀) := by
  refine T'.coeffs_eq_of_taylorSum ?_
  rw [taylorSum_apply, Finsupp.sum_mapRange_index (fun _ ↦ by rw [map_zero, smul_zero]),
    ← h₁, T.a₁_eq_sum, map_finsuppSum]
  refine Finsupp.sum_congr fun K _ ↦ ?_
  rw [hφ₁, hτ, h₀]

/-- The operators `θ_K` are natural, in the sense of
`Crystalline.TaylorExpansion.coeffs_naturality`. -/
theorem theta_naturality (φ₀ : M₀ →+ M₀') (φ₁ : M₁ →+ M₁') (τ : R →+* R')
    (hφ₁ : ∀ (r : R) (y : M₁), φ₁ (r • y) = τ r • φ₁ y) (hτ : ∀ K, τ (T.xi K) = T'.xi K)
    (h₀ : ∀ m, φ₁ (T.a₀ m) = T'.a₀ (φ₀ m)) (h₁ : ∀ m, φ₁ (T.a₁ m) = T'.a₁ (φ₀ m))
    (K : ι →₀ ℕ) (m : M₀) :
    T'.theta K (φ₀ m) = φ₀ (T.theta K m) := by
  rw [theta_apply, T.coeffs_naturality T' φ₀ φ₁ τ hφ₁ hτ h₀ h₁, Finsupp.mapRange_apply,
    theta_apply]

end Naturality

end TaylorExpansion

/-! ### Bijectivity from a basis and the crystal base change -/

section Basis

variable {M₀ M₁} {R₀ : Type*} [CommRing R₀] [Module R₀ M₀] {X : Type*} {R₁ : Type*} [CommRing R₁]
  [Module R₁ M₁] {B : Type*} [AddCommGroup B] [Module R₀ B]

/-- **The bijectivity of a Taylor expansion datum from a basis and a base change.**  If the ring
`B` of `T(1)_e` is free over the ring `R₀` of `T_e` on a basis `b`, and the crystal identifies
`B ⊗_{R₀} M₀` with `M₁` through `t ⊗ m ↦ κ(t) · a₀(m)`, then every element of `M₁` is uniquely
`∑_K κ(b_K) · a₀(m_K)`.  The map `κ` reads an element of `B` as a scalar of `M₁`; it is the
identity up to spelling in the application. -/
theorem bijective_taylorSum_of_basis (a₀ : M₀ →+ M₁) (κ : B → R₁)
    (b : Module.Basis X R₀ B) (β : B ⊗[R₀] M₀ →+ M₁)
    (hβ : Function.Bijective β) (hβt : ∀ (t : B) (m : M₀), β (t ⊗ₜ m) = κ t • a₀ m) :
    Function.Bijective (taylorSum a₀ fun K ↦ κ (b K)) := by
  classical
  let Ψ : (X →₀ M₀) ≃+ B ⊗[R₀] M₀ :=
    ((TensorProduct.finsuppScalarLeft R₀ M₀ X).symm.trans
      (LinearEquiv.rTensor M₀ b.repr.symm)).toAddEquiv
  have h : taylorSum a₀ (fun K ↦ κ (b K)) = β.comp Ψ.toAddMonoidHom := by
    refine Finsupp.addHom_ext fun K m ↦ ?_
    rw [taylorSum_single, AddMonoidHom.coe_comp, Function.comp_apply]
    show _ = β ((LinearEquiv.rTensor M₀ b.repr.symm)
      ((TensorProduct.finsuppScalarLeft R₀ M₀ X).symm (Finsupp.single K m)))
    rw [TensorProduct.finsuppScalarLeft_symm_apply_single, LinearEquiv.rTensor_tmul,
      Module.Basis.repr_symm_single_one, hβt]
  rw [h, AddMonoidHom.coe_comp]
  exact hβ.comp Ψ.bijective

/-- The basis of an `R₀`-module `B` on a family `ξ` for which `(c_K)_K ↦ ∑_K c_K • ξ_K` is
bijective. -/
noncomputable def basisOfBijective (xi : X → B)
    (h : Function.Bijective (Finsupp.linearCombination R₀ xi)) : Module.Basis X R₀ B :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective _ h).symm

/-- The basis `basisOfBijective ξ h` sends the index `K` to `ξ_K`. -/
@[simp] theorem basisOfBijective_apply (xi : X → B)
    (h : Function.Bijective (Finsupp.linearCombination R₀ xi)) (K : X) :
    basisOfBijective xi h K = xi K := by
  rw [basisOfBijective, Module.Basis.coe_ofRepr, LinearEquiv.symm_symm]
  show Finsupp.linearCombination R₀ xi (Finsupp.single K 1) = xi K
  rw [Finsupp.linearCombination_single, one_smul]

end Basis

/-! ### Freeness passes to a quotient by a principal ideal -/

section Quotient

variable {R B R' B' X : Type*} [CommRing R] [CommRing B] [CommRing R'] [CommRing B']

/-- **Freeness on a family passes to the quotients by `c`.**  If `B` is free over `R` through
`σ` on `ξ`, and `π_R : R → R'`, `π_B : B → B'` are surjections compatible with `σ` and
`σ' : R' → B'`, with `π_R(c) = 0` and the kernel of `π_B` contained in `(c)`, then `B'` is free
over `R'` through `σ'` on `π_B ∘ ξ`.  This is how the freeness of `E(n)` over `E(0)` gives the
freeness of the ring of `T(n)_e` over that of `T_e`, `c = p^{N + e}`. -/
theorem bijective_taylorSum_quotient (σ : R →+* B) (xi : X → B)
    (hfree : Function.Bijective (taylorSum σ.toAddMonoidHom xi))
    (πR : R →+* R') (πB : B →+* B') (σ' : R' →+* B') (hcomm : ∀ r, σ' (πR r) = πB (σ r))
    (hπR : Function.Surjective πR) (hπB : Function.Surjective πB) (c : ℕ)
    (hcR : πR c = 0) (hcB : ∀ y, πB y = 0 → ∃ z, y = (c : B) * z) :
    Function.Bijective (taylorSum σ'.toAddMonoidHom fun K ↦ πB (xi K)) := by
  classical
  have hmap : ∀ g : X →₀ R, taylorSum σ'.toAddMonoidHom (fun K ↦ πB (xi K))
      (g.mapRange πR (map_zero πR)) = πB (taylorSum σ.toAddMonoidHom xi g) := by
    intro g
    rw [taylorSum_apply, taylorSum_apply, Finsupp.sum_mapRange_index (fun _ ↦ by simp),
      map_finsuppSum]
    refine Finsupp.sum_congr fun K _ ↦ ?_
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, smul_eq_mul, map_mul,
      hcomm]
  refine ⟨fun g₁' g₂' h ↦ ?_, fun y' ↦ ?_⟩
  · obtain ⟨g₁, rfl⟩ := Finsupp.mapRange_surjective πR (map_zero πR) hπR g₁'
    obtain ⟨g₂, rfl⟩ := Finsupp.mapRange_surjective πR (map_zero πR) hπR g₂'
    have h0 : πB (taylorSum σ.toAddMonoidHom xi (g₁ - g₂)) = 0 := by
      rw [map_sub, map_sub, ← hmap, ← hmap, h, sub_self]
    obtain ⟨z, hz⟩ := hcB _ h0
    obtain ⟨g₃, rfl⟩ := hfree.2 z
    have hsmul : (c : B) * taylorSum σ.toAddMonoidHom xi g₃ =
        taylorSum σ.toAddMonoidHom xi (g₃.mapRange (fun a ↦ (c : R) * a) (mul_zero _)) := by
      rw [taylorSum_apply, taylorSum_apply, Finsupp.sum_mapRange_index (fun _ ↦ by simp),
        Finsupp.mul_sum]
      refine Finsupp.sum_congr fun K _ ↦ ?_
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, smul_eq_mul, map_mul,
        map_natCast]
      ring
    refine sub_eq_zero.mp ?_
    rw [← Finsupp.mapRange_sub (map_sub πR), hfree.1 (hz.trans hsmul)]
    ext K
    simp [hcR]
  · obtain ⟨y, rfl⟩ := hπB y'
    obtain ⟨g, rfl⟩ := hfree.2 y
    exact ⟨g.mapRange πR (map_zero πR), hmap g⟩

end Quotient

end Crystalline

end
