module

public import Mathlib.Data.Finsupp.Antidiagonal
public import StacksFrontier.AlgebraicGeometry.Crystalline.TwistedBaseChange

/-!
# The Taylor map of a module with composite coordinate operators, at one level

Fix a commutative ring `D`, a `D`-module `M`, a family of additive operators `θ_K` of `M` indexed
by the multi-indices `K : ι →₀ ℕ`, and the corresponding family `δ_K` of additive operators of `D`.
Let `q₀, q₁ : D →+* R` be two ring maps and `ξ_K ∈ R` a family of "divided power monomials",
multiplying as `ξ_A ξ_B = c(A, B) ξ_{A + B}`.  The **Taylor map** is

`E(m) = ∑_K ξ_K ⊗ θ_K(m) ∈ R ⊗_{D, q₀} M`,

a finite sum as soon as only finitely many of its terms are nonzero.  This file proves that `E` is
`q₁`-semilinear, given the general Leibniz rule
`θ_K(d m) = ∑_{A + B = K} c(A, B) δ_A(d) θ_B(m)` and Taylor's formula
`q₁(d) = ∑_A q₀(δ_A(d)) ξ_A` in `R`.

This is the one-level form of the semilinearity in the proof of
[Stacks, Proposition 60.17.4, Tag 07JH]: the map `m ⊗ 1 ↦ ∑_K θ_K(m) ⊗ ξ^{[K]}` is well defined on
`M ⊗_{D, g} B` because Taylor's formula holds in `B`.
-/

@[expose] public section

open scoped TensorProduct

open Finset.HasAntidiagonal

namespace Crystalline.TaylorStratification

variable {ι : Type*} {D : Type*} [CommRing D] {M : Type*} [AddCommGroup M] [Module D M]
  {R : Type*} [CommRing R] (q₀ : D →+* R) (ξ : (ι →₀ ℕ) → R) (θ : (ι →₀ ℕ) → M →+ M)

/-- The `K`-th term `ξ_K ⊗ θ_K(m)` of the Taylor map, in `R ⊗_{D, q₀} M`. -/
noncomputable def term (m : M) (K : ι →₀ ℕ) : TwistedScalars q₀ ⊗[D] M :=
  TwistedScalars.mk q₀ (ξ K) ⊗ₜ[D] θ K m

/-- **The Taylor map** `m ↦ ∑_K ξ_K ⊗ θ_K(m)`, as a `finsum`; it is the honest sum when only
finitely many terms are nonzero, which is the hypothesis of every statement below. -/
noncomputable def taylorMap (m : M) : TwistedScalars q₀ ⊗[D] M :=
  ∑ᶠ K, term q₀ ξ θ m K

variable {q₀ ξ θ}

/-- The Taylor map is the sum of its terms over any finite set containing their support. -/
theorem taylorMap_eq_sum {m : M} (s : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, term q₀ ξ θ m K = 0) :
    taylorMap q₀ ξ θ m = ∑ K ∈ s, term q₀ ξ θ m K :=
  finsum_eq_sum_of_support_subset _ (Function.support_subset_iff'.2 hs)

/-- **The Taylor map is additive**, given that each of the two arguments has finitely many
nonzero terms. -/
theorem taylorMap_add {m n : M} (hm : (Function.support (term q₀ ξ θ m)).Finite)
    (hn : (Function.support (term q₀ ξ θ n)).Finite) :
    taylorMap q₀ ξ θ (m + n) = taylorMap q₀ ξ θ m + taylorMap q₀ ξ θ n := by
  have h : term q₀ ξ θ (m + n) = term q₀ ξ θ m + term q₀ ξ θ n := by
    funext K
    simp only [term, map_add, TensorProduct.tmul_add, Pi.add_apply]
  rw [taylorMap, h]
  exact finsum_add_distrib hm hn

/-- A term whose operator lands in a submodule killed in the base change vanishes. -/
theorem term_eq_zero_of_smul {m : M} {K : ι →₀ ℕ} {d : D} (hd : q₀ d = 0) {y : M}
    (hy : θ K m = d • y) : term q₀ ξ θ m K = 0 := by
  rw [term, hy, ← TensorProduct.smul_tmul]
  change (TwistedScalars.mk q₀ (q₀ d * ξ K)) ⊗ₜ[D] y = 0
  rw [hd, zero_mul]
  exact TensorProduct.zero_tmul _ _

variable [DecidableEq ι] (c : (ι →₀ ℕ) → (ι →₀ ℕ) → ℕ) (δ : (ι →₀ ℕ) → D →+ D) (q₁ : D →+* R)

/-- Summing `F` over the antidiagonals of the elements of `s` is summing over a finset `T`, when
`F` vanishes outside `T` and at the points of `T` whose sum is not in `s`. -/
private theorem sum_antidiagonal_eq_sum {N : Type*} [AddCommMonoid N] (s : Finset (ι →₀ ℕ))
    (T : Finset ((ι →₀ ℕ) × (ι →₀ ℕ))) (F : (ι →₀ ℕ) × (ι →₀ ℕ) → N) (hT : ∀ x ∉ T, F x = 0)
    (hs : ∀ x ∈ T, x.1 + x.2 ∉ s → F x = 0) :
    ∑ K ∈ s, ∑ x ∈ antidiagonal K, F x = ∑ x ∈ T, F x := by
  rw [← Finset.sum_filter_of_ne fun x hx hne ↦ by_contra fun h ↦ hne (hs x hx h),
    ← Finset.sum_fiberwise_of_maps_to (s := T.filter fun x ↦ x.1 + x.2 ∈ s)
      (g := fun x ↦ x.1 + x.2) (t := s) fun x hx ↦ (Finset.mem_filter.mp hx).2]
  refine Finset.sum_congr rfl fun K hK ↦ (Finset.sum_subset (fun x hx ↦ ?_) fun x hx hx' ↦ ?_).symm
  · exact mem_antidiagonal.mpr (Finset.mem_filter.mp hx).2
  · refine hT x fun hxT ↦ hx' (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxT, ?_⟩, ?_⟩)
    · rw [mem_antidiagonal.mp hx]
      exact hK
    · exact mem_antidiagonal.mp hx

/-- **The Taylor map is `q₁`-semilinear.**

Hypotheses: the monomials multiply as `ξ_A ξ_B = c(A, B) ξ_{A + B}` (`hξ`); the general Leibniz
rule `θ_K(d m) = ∑_{A + B = K} c(A, B) δ_A(d) θ_B(m)` (`hleib`); Taylor's formula
`q₁(d) = ∑_{A ∈ t} q₀(δ_A(d)) ξ_A` over a finite set `t` outside of which the terms vanish (`ht`,
`htay`); and the finiteness of the terms of `m` (`hm`). -/
theorem taylorMap_smul (hξ : ∀ A B, ξ A * ξ B = (c A B : R) * ξ (A + B))
    (hleib : ∀ (K : ι →₀ ℕ) (d : D) (m : M),
      θ K (d • m) = ∑ P ∈ antidiagonal K, c P.1 P.2 • (δ P.1 d • θ P.2 m))
    (d : D) (m : M) (s t : Finset (ι →₀ ℕ)) (hs : ∀ K ∉ s, term q₀ ξ θ m K = 0)
    (ht : ∀ A ∉ t, q₀ (δ A d) * ξ A = 0)
    (htay : q₁ d = ∑ A ∈ t, q₀ (δ A d) * ξ A) :
    taylorMap q₀ ξ θ (d • m) = q₁ d • taylorMap q₀ ξ θ m := by
  set F : (ι →₀ ℕ) × (ι →₀ ℕ) → TwistedScalars q₀ ⊗[D] M := fun P ↦
    TwistedScalars.mk q₀ (q₀ (δ P.1 d) * ξ P.1 * ξ P.2) ⊗ₜ[D] θ P.2 m with hF
  have hterm : ∀ A B : ι →₀ ℕ, TwistedScalars.mk q₀ (ξ (A + B)) ⊗ₜ[D]
      (c A B • (δ A d • θ B m)) = F (A, B) := by
    intro A B
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul]
    change (c A B : ℕ) • (TwistedScalars.mk q₀ (q₀ (δ A d) * ξ (A + B)) ⊗ₜ[D] θ B m) = F (A, B)
    rw [← Nat.cast_smul_eq_nsmul R, TensorProduct.smul_tmul', hF]
    congr 1
    change ((c A B : ℕ) : R) * (q₀ (δ A d) * ξ (A + B)) = q₀ (δ A d) * ξ A * ξ B
    rw [mul_assoc, hξ]
    ring
  have hsmul : ∀ A B, F (A, B) = (q₀ (δ A d) * ξ A) • term q₀ ξ θ m B := fun A B ↦ by
    rw [term, TensorProduct.smul_tmul']
    rfl
  have hFvan : ∀ P : (ι →₀ ℕ) × (ι →₀ ℕ), P ∉ t ×ˢ s → F P = 0 := by
    rintro ⟨A, B⟩ hP
    rw [Finset.mem_product, not_and_or] at hP
    rcases hP with hA | hB
    · simp only [hF, ht A hA, zero_mul]
      exact TensorProduct.zero_tmul _ _
    · rw [hsmul, hs B hB, smul_zero]
  set sK : Finset (ι →₀ ℕ) := (t ×ˢ s).image fun P ↦ P.1 + P.2
  have hlhs : taylorMap q₀ ξ θ (d • m) = ∑ P ∈ t ×ˢ s, F P := by
    have hvan : ∀ K ∉ sK, term q₀ ξ θ (d • m) K = 0 := by
      intro K hK
      rw [term, hleib, TensorProduct.tmul_sum]
      refine Finset.sum_eq_zero fun P hP ↦ ?_
      rw [← mem_antidiagonal.mp hP, hterm P.1 P.2]
      exact hFvan P fun hmem ↦ hK (Finset.mem_image.mpr ⟨P, hmem, mem_antidiagonal.mp hP⟩)
    rw [taylorMap_eq_sum sK hvan]
    simp only [term, hleib, TensorProduct.tmul_sum]
    have hcongr : ∀ K ∈ sK, ∑ P ∈ antidiagonal K, TwistedScalars.mk q₀ (ξ K) ⊗ₜ[D]
        (c P.1 P.2 • (δ P.1 d • θ P.2 m)) = ∑ P ∈ antidiagonal K, F P := by
      intro K _
      refine Finset.sum_congr rfl fun P hP ↦ ?_
      rw [← mem_antidiagonal.mp hP]
      exact hterm P.1 P.2
    rw [Finset.sum_congr rfl hcongr]
    exact sum_antidiagonal_eq_sum sK _ F (hFvan) fun P hP hK ↦
      absurd (Finset.mem_image_of_mem _ hP) hK
  have hrhs : q₁ d • taylorMap q₀ ξ θ m = ∑ P ∈ t ×ˢ s, F P := by
    rw [taylorMap_eq_sum s hs, htay, Finset.sum_product, Finset.sum_smul]
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun B _ ↦ ?_
    exact (hsmul A B).symm
  rw [hlhs, hrhs]

/-! ### Pushing the Taylor map along a ring map -/

section Push

variable {R' : Type*} [CommRing R']

/-- **The base change of the twisted tensor product along a ring map** `σ : R → R'`, onto the twist
by a prescribed ring map `r` with `σ ∘ q₀ = r`: the `σ`-semilinear map `b ⊗ m ↦ σ(b) ⊗ m`.
Naming the target twist `r` rather than computing it as `σ ∘ q₀` keeps casts out of the
statements below. -/
noncomputable def push (σ : R →+* R') (r : D →+* R') (h : σ.comp q₀ = r) :
    TwistedScalars q₀ ⊗[D] M →ₛₗ[σ] TwistedScalars r ⊗[D] M where
  toFun := LinearMap.rTensor M
    { toFun := fun b : TwistedScalars q₀ ↦ TwistedScalars.mk r (σ b.val)
      map_add' := fun b b' ↦ map_add σ b.val b'.val
      map_smul' := fun d b ↦ by
        change TwistedScalars.mk r (σ (q₀ d * b.val)) = TwistedScalars.mk r (r d * σ b.val)
        rw [map_mul, ← h]
        rfl }
  map_add' := map_add _
  map_smul' b z := by
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
        rw [TensorProduct.smul_tmul']
        change TwistedScalars.mk r (σ (b * c.val)) ⊗ₜ[D] m =
          σ b • (TwistedScalars.mk r (σ c.val) ⊗ₜ[D] m)
        rw [TensorProduct.smul_tmul', map_mul]
        rfl
    | add x y hx hy =>
        simp only [smul_add, map_add] at hx hy ⊢
        rw [hx, hy]

/-- `push σ r h` sends `b ⊗ m` to `σ b ⊗ m`. -/
@[simp] theorem push_tmul (σ : R →+* R') (r : D →+* R') (h : σ.comp q₀ = r)
    (b : TwistedScalars q₀) (m : M) :
    push σ r h (b ⊗ₜ[D] m) = TwistedScalars.mk r (σ b.val) ⊗ₜ[D] m := rfl

omit [DecidableEq ι] in
/-- **The Taylor map pushed along a ring map is the Taylor map of the pushed monomials.** -/
theorem push_taylorMap (σ : R →+* R') (r : D →+* R') (h : σ.comp q₀ = r) (m : M)
    (s : Finset (ι →₀ ℕ)) (hs : ∀ K ∉ s, term q₀ ξ θ m K = 0) :
    push σ r h (taylorMap q₀ ξ θ m) = ∑ K ∈ s, TwistedScalars.mk r (σ (ξ K)) ⊗ₜ[D] θ K m := by
  rw [taylorMap_eq_sum s hs, map_sum]
  rfl

omit [DecidableEq ι] in
/-- **The unit law.**  If `σ` sends `ξ_0` to `1` and every other `ξ_K` to `0`, and `θ_0 = id`, the
pushed Taylor map is `m ↦ 1 ⊗ m`. -/
theorem push_taylorMap_of_unit (σ : R →+* R') (r : D →+* R') (h : σ.comp q₀ = r)
    (h0 : σ (ξ 0) = 1) (hK : ∀ K, K ≠ 0 → σ (ξ K) = 0) (hθ0 : ∀ m, θ 0 m = m) (m : M)
    (s : Finset (ι →₀ ℕ)) (hs : ∀ K ∉ s, term q₀ ξ θ m K = 0) :
    push σ r h (taylorMap q₀ ξ θ m) = (1 : TwistedScalars r) ⊗ₜ[D] m := by
  classical
  rw [push_taylorMap σ r h m (insert 0 s) (fun K hK' ↦ hs K fun h' ↦ hK' (by simp [h'])),
    Finset.sum_eq_single_of_mem 0 (Finset.mem_insert_self _ _)]
  · rw [h0, hθ0]
    rfl
  · intro K _ hK0
    rw [hK K hK0]
    exact TensorProduct.zero_tmul _ _

end Push

/-! ### Vanishing of the terms modulo a power of `p` -/

section Vanish

/-- **A generator `b ⊗ p^n z` vanishes in a twisted tensor product whose ring is killed by `p^n`.**
This is the source's "the sum is finite!": the operators `θ_K(m)` lie in `p^n M` for all but
finitely many `K`, and `p^n = 0` in the section ring of a level. -/
theorem tmul_nsmul_eq_zero {R' : Type*} [CommRing R'] (r : D →+* R') {p n : ℕ}
    (hp : (p : R') ^ n = 0) (b : TwistedScalars r) (z : M) :
    b ⊗ₜ[D] ((p ^ n : ℕ) • z) = 0 := by
  rw [← Nat.cast_smul_eq_nsmul D, ← TensorProduct.smul_tmul]
  have : ((p ^ n : ℕ) : D) • b = 0 := by
    change TwistedScalars.mk r (r ((p ^ n : ℕ) : D) * b.val) = 0
    rw [map_natCast, Nat.cast_pow, hp, zero_mul]
    rfl
  rw [this, TensorProduct.zero_tmul]

/-- A generator `b ⊗ y` vanishes if `y` is `p^n` times an element and `p^n = 0` in the ring. -/
private theorem tmul_eq_zero_of_nsmul {R' : Type*} [CommRing R'] (r : D →+* R') {p n : ℕ}
    (hp : (p : R') ^ n = 0) (b : TwistedScalars r) {y : M} (hy : ∃ z, y = (p ^ n : ℕ) • z) :
    b ⊗ₜ[D] y = 0 := by
  obtain ⟨z, rfl⟩ := hy
  exact tmul_nsmul_eq_zero r hp b z

end Vanish

/-! ### The cocycle law -/

section Cocycle

variable {R₂ : Type*} [CommRing R₂] {p n : ℕ}

/-- **The cocycle law of the Taylor map**, the computation in the proof of
[Stacks, Proposition 60.17.4, Tag 07JH] showing `c_{g,h} ∘ c_{f,g} = c_{f,h}`.

The three ring maps `σ₀₁, σ₁₂, σ₀₂ : R → R₂` are the three cofaces, `r₀, r₁` the first two
vertices, and `η (K, L) = v^{[K]} u^{[L]}` with `σ₀₁ ξ_L = u^{[L]}`, `σ₁₂ ξ_K = v^{[K]}` and
`σ₀₂ ξ_N = ∑_{K + L = N} v^{[K]} u^{[L]}`.  If `θ_{K + L} = θ_L ∘ θ_K`, `p^n = 0` in `R₂` and for
each `m` only finitely many `θ_K(m)` lie outside `p^n M`, then pushing the Taylor map along `σ₁₂`
and applying the base change of its push along `σ₀₁` is pushing it along `σ₀₂`.  The base change
is formed from the `r₁`-semilinear map `E₀₁`, given as data together with its values. -/
theorem cocycle (σ₀₁ σ₁₂ σ₀₂ : R →+* R₂) (r₀ r₁ : D →+* R₂)
    (h₀₁ : σ₀₁.comp q₀ = r₀) (h₁₂ : σ₁₂.comp q₀ = r₁) (h₀₂ : σ₀₂.comp q₀ = r₀)
    (η : (ι →₀ ℕ) × (ι →₀ ℕ) → R₂)
    (hη₀₁ : ∀ L, σ₀₁ (ξ L) = η (0, L)) (hη₁₂ : ∀ K, σ₁₂ (ξ K) = η (K, 0))
    (hη₀₂ : ∀ N, σ₀₂ (ξ N) = ∑ x ∈ antidiagonal N, η x)
    (hηmul : ∀ K L, η (K, 0) * η (0, L) = η (K, L))
    (hθ : ∀ K L m, θ L (θ K m) = θ (K + L) m)
    (hpR : (p : R) ^ n = 0) (hp : (p : R₂) ^ n = 0)
    (hfin : ∀ m : M, ∃ s : Finset (ι →₀ ℕ), ∀ K ∉ s, ∃ z, θ K m = (p ^ n : ℕ) • z)
    (E₀₁ : M →ₛₗ[r₁] TwistedScalars r₀ ⊗[D] M)
    (hE₀₁ : ∀ m, E₀₁ m = push σ₀₁ r₀ h₀₁ (taylorMap q₀ ξ θ m)) (m : M) :
    semilinearBaseChange E₀₁ (push σ₁₂ r₁ h₁₂ (taylorMap q₀ ξ θ m)) =
      push σ₀₂ r₀ h₀₂ (taylorMap q₀ ξ θ m) := by
  obtain ⟨s, hs⟩ := hfin m
  set S : Finset (ι →₀ ℕ) := s.biUnion Finset.Iic with hS
  have hmemS : ∀ {K N : ι →₀ ℕ}, N ∈ s → K ≤ N → K ∈ S := fun hN hK ↦
    Finset.mem_biUnion.mpr ⟨_, hN, Finset.mem_Iic.mpr hK⟩
  set G : (ι →₀ ℕ) × (ι →₀ ℕ) → TwistedScalars r₀ ⊗[D] M := fun x ↦
    TwistedScalars.mk r₀ (η x) ⊗ₜ[D] θ (x.1 + x.2) m with hG
  have hGvan : ∀ x, x.1 + x.2 ∉ s → G x = 0 := fun x hx ↦ tmul_eq_zero_of_nsmul r₀ hp _ (hs _ hx)
  have hlhs : semilinearBaseChange E₀₁ (push σ₁₂ r₁ h₁₂ (taylorMap q₀ ξ θ m)) =
      ∑ x ∈ S ×ˢ S, G x := by
    rw [push_taylorMap σ₁₂ r₁ h₁₂ m S fun K hK ↦
      tmul_eq_zero_of_nsmul q₀ hpR _ (hs K fun hKs ↦ hK (hmemS hKs le_rfl)), map_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    rw [semilinearBaseChange_mk_tmul, hE₀₁, push_taylorMap σ₀₁ r₀ h₀₁ (θ K m) S, Finset.smul_sum]
    · refine Finset.sum_congr rfl fun L _ ↦ ?_
      rw [TensorProduct.smul_tmul', hG, hθ]
      change TwistedScalars.mk r₀ (σ₁₂ (ξ K) * σ₀₁ (ξ L)) ⊗ₜ[D] _ = _
      rw [hη₁₂, hη₀₁, hηmul]
    · intro L hL
      refine tmul_eq_zero_of_nsmul q₀ hpR _ ?_
      rw [hθ]
      exact hs _ fun hKL ↦ hL (hmemS hKL le_add_self)
  have hrhs : push σ₀₂ r₀ h₀₂ (taylorMap q₀ ξ θ m) = ∑ x ∈ S ×ˢ S, G x := by
    rw [push_taylorMap σ₀₂ r₀ h₀₂ m s fun K hK ↦ tmul_eq_zero_of_nsmul q₀ hpR _ (hs K hK),
      ← sum_antidiagonal_eq_sum s (S ×ˢ S) G
        (fun x hx ↦ hGvan x fun hxs ↦ hx (Finset.mem_product.mpr
          ⟨hmemS hxs le_self_add, hmemS hxs le_add_self⟩)) fun x _ ↦ hGvan x]
    refine Finset.sum_congr rfl fun N _ ↦ ?_
    rw [hη₀₂]
    change (∑ x ∈ antidiagonal N, TwistedScalars.mk r₀ (η x)) ⊗ₜ[D] θ N m = _
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    change _ = TwistedScalars.mk r₀ (η x) ⊗ₜ[D] θ (x.1 + x.2) m
    rw [mem_antidiagonal.mp hx]
  rw [hlhs, hrhs]

end Cocycle

end Crystalline.TaylorStratification

end
