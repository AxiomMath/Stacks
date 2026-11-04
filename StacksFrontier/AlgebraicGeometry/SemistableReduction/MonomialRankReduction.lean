module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ExceptionalFiltration

/-!
# Spanning and independence of the monomials are one condition once the rank is known

Let `A` be a commutative ring with a multiplicative filtration `A = I₀ ⊇ I₁ ⊇ ⋯` by ideals, let
`φ : A ⟶ k` be a surjection onto a field with kernel `I₁`, and let `x, y ∈ I₁`. Two of the five
geometric inputs that
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration` asks for are
statements about the degree-`n` monomials `x^{n-j} y^j`:

* `hspanPow`, that `Iₙ` is spanned by them modulo `Iₙ₊₁`;
* `hindep`, that they are independent over `A / I₁`.

This file shows that **the two are equivalent as soon as the `n`-th graded piece is known to have
rank `n + 1`**, so that only one of them has to be proved.

The reason is a dimension count. Because `I₁ · Iₙ ⊆ Iₙ₊₁`, the ideal `I₁` annihilates `Iₙ / Iₙ₊₁`,
so the `A`-span of a family in that quotient is its `k`-span and the monomials define a `k`-linear
map `k^{n+1} ⟶ Iₙ / Iₙ₊₁`. Spanning says that map is surjective, independence says it is
injective, and between `k`-spaces of the same finite dimension those are the same condition,
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`.

## How the graded piece is presented

The quotient `Iₙ / Iₙ₊₁` is not formed here. Instead the hypotheses name a `k`-vector space `W`
and a bare function `π : A ⟶ W` whose axioms are guarded by membership in `Iₙ` — `π` is additive
there, semilinear over `φ`, vanishes exactly on `Iₙ₊₁` and is onto `W`. That is the same
discipline as `AlgebraicGeometry.SemistableReduction.MonomialSymbol`, whose symbol is likewise a
bare function with guarded axioms, and it is the shape in which the geometry delivers the piece:
`W` is `Γ(𝐏¹_k, 𝒪(n))`, `π` is the composite of the kernel description of the graded piece with a
comparison of the twisted ideal sheaf with the `n`-th twist, and the rank is
`AlgebraicGeometry.projectiveLineProjTwistSectionsBasis`. Presenting the piece this way means no
quotient module and no `IsField.toField` enter, and in particular the `k`-structure is carried by
`hsmul` rather than built.

**What this does and does not reduce.** It removes one of the three outstanding monomial inputs of
[Stacks, Tag 0C2K], at the price of the rank of the graded piece. That price is worth paying
because the rank needs only the *degreewise* comparison of `𝒪_X(-nE)|_E` with `𝒪(n)`, of which the
library has one for each `n` separately
(`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf`), whereas `hspanPow` and `hindep` were
being approached through a single family of comparisons compatible with multiplication across all
pairs of degrees, which the library does not have and which
`StacksFrontier/AlgebraicGeometry/Divisors/IdealPowerGradedAlgebra.lean` records as open. Nothing
here carries a `@[stacks]` attribute: this is a reduction between two of the inputs, not a proof
of either.

## Main definitions

* `AlgebraicGeometry.SemistableReduction.monomialClassMap` — the `k`-linear map on coefficient
  vectors induced by the degree-`n` monomials.

## Main results

* `AlgebraicGeometry.SemistableReduction.surjective_monomialClassMap_iff` — surjectivity of that
  map is the `hspanPow` input in degree `n`.
* `AlgebraicGeometry.SemistableReduction.injective_monomialClassMap_iff` — injectivity of that map
  is the `hindep` input in degree `n`.
* `AlgebraicGeometry.SemistableReduction.le_span_pow_sup_iff_coeff_mem_ideal_one` — **the two
  inputs are equivalent in degree `n`**, given a basis of the graded piece indexed by
  `Fin (n + 1)`.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.SemistableReduction

/-- The `k`-linear map on coefficient vectors induced by the degree-`n` monomials in `x` and `y`:
the `j`-th coordinate is scaled by the value of `π` on the `j`-th monomial.

Only linearity in the coefficients is used in the definition, so no axiom on `π` is required
here. -/
public def monomialClassMap (k : Type u) [Field k] {A : Type u} [CommRing A] {W : Type u}
    [AddCommGroup W] [Module k W] (π : A → W) (x y : A) (n : ℕ) :
    (Fin (n + 1) → k) →ₗ[k] W where
  toFun v := ∑ j : Fin (n + 1), v j • π (genMonomial x y n (j : ℕ))
  map_add' v w := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum]

section MonomialRank

variable {A : Type u} [CommRing A] {k : Type u} [Field k] {W : Type u} [AddCommGroup W]
  [Module k W] (I : ℕ → Ideal A) (φ : A →+* k) (π : A → W)

/-! ### Elementary consequences of a multiplicative filtration -/

/-- A power of an element of the first step of a multiplicative filtration lies in the
corresponding step. -/
public theorem pow_mem_of_mem_ideal_one (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) {z : A} (hz : z ∈ I 1) : ∀ p : ℕ, z ^ p ∈ I p := by
  intro p
  induction p with
  | zero => rw [pow_zero, hzero]; trivial
  | succ p ih => exact pow_succ z p ▸ hmul p 1 (Ideal.mul_mem_mul ih hz)

/-- A degree-`n` monomial in two elements of the first step lies in the `n`-th step. -/
public theorem genMonomial_mem_of_mem_ideal_one (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    {n j : ℕ} (hj : j ≤ n) : genMonomial x y n j ∈ I n := by
  have h := hmul (n - j) j (Ideal.mul_mem_mul
    (pow_mem_of_mem_ideal_one I hzero hmul hx (n - j))
    (pow_mem_of_mem_ideal_one I hzero hmul hy j))
  rwa [Nat.sub_add_cancel hj] at h

/-! ### The graded piece, presented by a guarded function -/

variable {n : ℕ}

/-- A function additive on the `n`-th step kills zero. -/
public theorem map_zero_of_add_mem
    (hadd : ∀ {a b : A}, a ∈ I n → b ∈ I n → π (a + b) = π a + π b) : π 0 = 0 := by
  have h := hadd (zero_mem (I n)) (zero_mem (I n))
  rw [add_zero] at h
  have h' : π 0 + 0 = π 0 + π 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/-- A function additive on the `n`-th step is additive on finite sums of its elements. -/
public theorem map_sum_range_of_mem
    (hadd : ∀ {a b : A}, a ∈ I n → b ∈ I n → π (a + b) = π a + π b) :
    ∀ (N : ℕ) (f : ℕ → A), (∀ j ∈ Finset.range N, f j ∈ I n) →
      π (∑ j ∈ Finset.range N, f j) = ∑ j ∈ Finset.range N, π (f j) := by
  intro N
  induction N with
  | zero => intro f _; simpa using map_zero_of_add_mem I π hadd
  | succ N ih =>
    intro f hf
    have hsub : ∀ j ∈ Finset.range N, f j ∈ I n := fun j hj =>
      hf j (Finset.mem_range.2 ((Finset.mem_range.1 hj).trans (Nat.lt_succ_self N)))
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      hadd (Submodule.sum_mem _ hsub) (hf N (Finset.mem_range.2 (Nat.lt_succ_self N))), ih f hsub]

/-- Each term of a combination of degree-`n` monomials lies in the `n`-th step. -/
private theorem mul_genMonomial_mem (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    (c : ℕ → A) {j : ℕ} (hj : j ∈ Finset.range (n + 1)) : c j * genMonomial x y n j ∈ I n :=
  Ideal.mul_mem_left _ _ (genMonomial_mem_of_mem_ideal_one I hzero hmul hx hy
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))

/-- A combination of degree-`n` monomials lies in the `n`-th step. -/
private theorem sum_mul_genMonomial_mem (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    (c : ℕ → A) : (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) ∈ I n :=
  Submodule.sum_mem _ fun _ hj => mul_genMonomial_mem I hzero hmul hx hy c hj

/-- Every coefficient vector over `k` is the image under `φ` of a sequence of elements of `A`. -/
private theorem exists_comp_eq_of_surjective (hφ : Function.Surjective φ) (v : Fin (n + 1) → k) :
    ∃ c : ℕ → A, (fun j : Fin (n + 1) => φ (c (j : ℕ))) = v := by
  choose cf hcf using fun j : Fin (n + 1) => hφ (v j)
  refine ⟨fun j => if h : j < n + 1 then cf ⟨j, h⟩ else 0, funext fun j => ?_⟩
  simpa [j.2] using hcf j

/-- **The linear map evaluates to the value of `π` on the corresponding combination of
monomials.** This is the one computation that ties the formal `k`-linear map to the filtration. -/
public theorem monomialClassMap_apply_eq (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    (hadd : ∀ {a b : A}, a ∈ I n → b ∈ I n → π (a + b) = π a + π b)
    (hsmul : ∀ (a : A) {z : A}, z ∈ I n → π (a * z) = φ a • π z) (c : ℕ → A) :
    monomialClassMap k π x y n (fun j => φ (c (j : ℕ))) =
      π (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) := by
  rw [map_sum_range_of_mem I π hadd (n + 1) _
    fun _ hj => mul_genMonomial_mem I hzero hmul hx hy c hj]
  rw [show (∑ j ∈ Finset.range (n + 1), π (c j * genMonomial x y n j)) =
      ∑ j ∈ Finset.range (n + 1), φ (c j) • π (genMonomial x y n j) from
    Finset.sum_congr rfl fun j hj => hsmul (c j)
      (genMonomial_mem_of_mem_ideal_one I hzero hmul hx hy
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))]
  exact (Fin.sum_univ_eq_sum_range (fun j => φ (c j) • π (genMonomial x y n j)) (n + 1))

/-! ### Spanning is surjectivity and independence is injectivity -/

/-- **Surjectivity of the monomial map is the `hspanPow` input in degree `n`**: that `Iₙ` is
spanned by the degree-`n` monomials in `x` and `y` modulo `Iₙ₊₁`. -/
public theorem surjective_monomialClassMap_iff (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) (hanti : ∀ m, I (m + 1) ≤ I m)
    (hφ : Function.Surjective φ) {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    (hadd : ∀ {a b : A}, a ∈ I n → b ∈ I n → π (a + b) = π a + π b)
    (hsmul : ∀ (a : A) {z : A}, z ∈ I n → π (a * z) = φ a • π z)
    (hkerπ : ∀ {a : A}, a ∈ I n → (π a = 0 ↔ a ∈ I (n + 1)))
    (hsurjπ : ∀ w : W, ∃ a ∈ I n, π a = w) :
    Function.Surjective (monomialClassMap k π x y n) ↔
      I n ≤ Ideal.span {x, y} ^ n ⊔ I (n + 1) := by
  constructor
  · intro hsurj a ha
    obtain ⟨v, hv⟩ := hsurj (π a)
    obtain ⟨c, hcv⟩ := exists_comp_eq_of_surjective φ hφ v
    have hw : π (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) = π a := by
      rw [← monomialClassMap_apply_eq I φ π hzero hmul hx hy hadd hsmul c, hcv, hv]
    have hsum := sum_mul_genMonomial_mem I hzero hmul hx hy c (n := n)
    have hsubeq : π (a - ∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) =
        π a - π (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) := by
      have h := hadd (sub_mem ha hsum) hsum
      rw [sub_add_cancel] at h
      rw [h, add_sub_cancel_right]
    have hrem : a - ∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j ∈ I (n + 1) :=
      (hkerπ (sub_mem ha hsum)).1 (by rw [hsubeq, hw, sub_self])
    exact Submodule.mem_sup.2
      ⟨_, sum_genMonomial_mem_span_pow x y n c, _, hrem, by ring⟩
  · intro hspan w
    obtain ⟨a, ha, hπa⟩ := hsurjπ w
    obtain ⟨s, hs, r, hr, hsr⟩ := Submodule.mem_sup.1 (hspan ha)
    obtain ⟨c, hcs⟩ := exists_repr_of_mem_span_pow x y hs
    have hsmem : s ∈ I n := hcs ▸ sum_mul_genMonomial_mem I hzero hmul hx hy c
    refine ⟨fun j => φ (c (j : ℕ)), ?_⟩
    rw [monomialClassMap_apply_eq I φ π hzero hmul hx hy hadd hsmul c, ← hcs, ← hπa, ← hsr,
      hadd hsmem (hanti n hr), (hkerπ (hanti n hr)).2 hr, add_zero]

/-- **Injectivity of the monomial map is the `hindep` input in degree `n`**: that the degree-`n`
monomials in `x` and `y` are independent over `A / I₁`. -/
public theorem injective_monomialClassMap_iff (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = I 1) {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    (hadd : ∀ {a b : A}, a ∈ I n → b ∈ I n → π (a + b) = π a + π b)
    (hsmul : ∀ (a : A) {z : A}, z ∈ I n → π (a * z) = φ a • π z)
    (hkerπ : ∀ {a : A}, a ∈ I n → (π a = 0 ↔ a ∈ I (n + 1))) :
    Function.Injective (monomialClassMap k π x y n) ↔
      ∀ c : ℕ → A, (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) ∈ I (n + 1) →
        ∀ j ≤ n, c j ∈ I 1 := by
  have hmem := sum_mul_genMonomial_mem I hzero hmul hx hy (n := n)
  constructor
  · intro hinj c hc j hj
    have hzeroval : monomialClassMap k π x y n (fun i => φ (c (i : ℕ))) = 0 := by
      rw [monomialClassMap_apply_eq I φ π hzero hmul hx hy hadd hsmul c]
      exact (hkerπ (hmem c)).2 hc
    have hv : (fun i : Fin (n + 1) => φ (c (i : ℕ))) = 0 :=
      (injective_iff_map_eq_zero (monomialClassMap k π x y n)).1 hinj _ hzeroval
    rw [← hker, RingHom.mem_ker]
    exact congrFun hv ⟨j, Nat.lt_succ_of_le hj⟩
  · intro hindep
    refine (injective_iff_map_eq_zero (monomialClassMap k π x y n)).2 fun v hv => ?_
    obtain ⟨c, hcv⟩ := exists_comp_eq_of_surjective φ hφ v
    have hmemsucc : (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) ∈ I (n + 1) := by
      refine (hkerπ (hmem c)).1 ?_
      rw [← monomialClassMap_apply_eq I φ π hzero hmul hx hy hadd hsmul c, hcv, hv]
    funext j
    have := hindep c hmemsucc (j : ℕ) (Nat.lt_succ_iff.1 j.2)
    rw [← hcv]
    simpa [RingHom.mem_ker] using (hker ▸ this : c (j : ℕ) ∈ RingHom.ker φ)

/-! ### The two inputs are the same condition -/

/-- **Spanning and independence of the degree-`n` monomials are equivalent, given the rank of the
`n`-th graded piece.**

`Iₙ` is spanned modulo `Iₙ₊₁` by the degree-`n` monomials in `x` and `y` exactly when those
monomials are independent over `A / I₁`, as soon as the graded piece has a basis indexed by
`Fin (n + 1)`. Both conditions are the same statement about one `k`-linear map between spaces of
dimension `n + 1`: the first that it is onto, the second that it is injective.

These are the `hspanPow` and `hindep` inputs of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration` in degree `n`, so
whichever of the two is easier to prove suffices. -/
public theorem le_span_pow_sup_iff_coeff_mem_ideal_one (hzero : I 0 = ⊤)
    (hmul : ∀ m n, I m * I n ≤ I (m + n)) (hanti : ∀ m, I (m + 1) ≤ I m)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = I 1)
    {x y : A} (hx : x ∈ I 1) (hy : y ∈ I 1)
    (hadd : ∀ {a b : A}, a ∈ I n → b ∈ I n → π (a + b) = π a + π b)
    (hsmul : ∀ (a : A) {z : A}, z ∈ I n → π (a * z) = φ a • π z)
    (hkerπ : ∀ {a : A}, a ∈ I n → (π a = 0 ↔ a ∈ I (n + 1)))
    (hsurjπ : ∀ w : W, ∃ a ∈ I n, π a = w)
    (b : Module.Basis (Fin (n + 1)) k W) :
    I n ≤ Ideal.span {x, y} ^ n ⊔ I (n + 1) ↔
      ∀ c : ℕ → A, (∑ j ∈ Finset.range (n + 1), c j * genMonomial x y n j) ∈ I (n + 1) →
        ∀ j ≤ n, c j ∈ I 1 := by
  have : FiniteDimensional k W := Module.Finite.of_basis b
  have hrank : Module.finrank k (Fin (n + 1) → k) = Module.finrank k W := by
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [← surjective_monomialClassMap_iff I φ π hzero hmul hanti hφ hx hy hadd hsmul hkerπ hsurjπ,
    ← injective_monomialClassMap_iff I φ π hzero hmul hφ hker hx hy hadd hsmul hkerπ,
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank]

end MonomialRank

end AlgebraicGeometry.SemistableReduction

end
