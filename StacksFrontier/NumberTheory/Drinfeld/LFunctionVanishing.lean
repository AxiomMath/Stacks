module

public import StacksFrontier.NumberTheory.Drinfeld.LFunctionFrobenius
public import StacksFrontier.NumberTheory.Drinfeld.LFunctionPolynomial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport

/-!
# Towards rational `H⁰ = H²_c = 0` for `ℱ_{ρ ⊗ χ}`: uniform bounds at the finite levels

In Drinfeld's proof of [Tag 03VU](https://stacks.math.columbia.edu/tag/03VU), the cohomology
`H⁰(X_k̄, ℱ)` and `H²_c(X_k̄, ℱ)` of the sheaf `ℱ = ℱ_{ρ ⊗ χ}` vanish rationally: at the level
`n` they are the invariants `(M_n)^N` and (twisted) coinvariants `(M_n)_N` of the image `N` of
`π₁(X_k̄)` acting on `M_n = O_E^r / ℓ^n`, and neither vanishes at a finite level in general. What
does hold is that **they are killed by a power `ℓ^c` independent of `n`**, because the
`ℚ_ℓ`-invariants and coinvariants vanish. Then the limit over `n` is killed by `ℓ^c`, and so its
rationalisation vanishes.

This file proves these steps.

* Clearing denominators: an integral vector in the `ℚ_ℓ`-span of the image of a set `S` of
  integral vectors has a multiple `ℓ^c v` in the `ℤ_ℓ`-span of `S`.
* Invariants: if a representation `τ : G → GL_m(ℤ_ℓ)` has no nonzero `ℚ_ℓ`-vector fixed by `N`,
  then there is `c` such that `ℓ^c` kills the `N`-invariants of `(ℤ/ℓ^n)^m` for every `n`.
* Coinvariants: if the vectors `τ(g) w - w`, `g ∈ N`, span `ℚ_ℓ^m`, then there is `c` such that
  `ℓ^c (ℤ/ℓ^n)^m` lies in the span of the `τ(g) w - w` for every `n`, so `ℓ^c` kills the
  coinvariants.
* Transport: for `τ` the restriction of scalars of an integral model `σ_O = P σ P⁻¹` of an
  absolutely irreducible `σ : π₁(X) → GL₂(E)`, and `N` a normal subgroup containing every
  commutator, both hypotheses hold.
* Limits: if every level of the inverse system `n ↦ Hⁱ_c(X_k̄, ℱ_n)` is killed by `ℓ^c`, then
  `Hⁱ_c(X_k̄, ℱ ⊗ ℚ_ℓ) = 0`.

## Main results

* `Stacks.Drinfeld.exists_pow_smul_mem_span_of_mem_span_rat`
* `Stacks.Drinfeld.exists_pow_smul_eq_zero_of_invariants`
* `Stacks.Drinfeld.exists_pow_smul_mem_span_of_coinvariants`
* `Stacks.Drinfeld.restrictScalars_invariants_eq_zero`,
  `Stacks.Drinfeld.restrictScalars_span_coinvariants_eq_top`
* `Stacks.Drinfeld.subsingleton_rationalGeometricCompactlySupportedCohomology_of_pow_smul`

## References

* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Matrix Module Stacks.EtaleCohomology

universe u

namespace Stacks.Drinfeld

/-! ### Clearing denominators in `ℚ_ℓ` -/

section Denominators

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Every element of `ℚ_ℓ` becomes integral after multiplication by a power of `ℓ`, and stays
integral for every larger power. -/
public theorem exists_pow_mul_norm_le_one (x : ℚ_[ℓ]) :
    ∃ c : ℕ, ∀ c' ≥ c, ‖(ℓ : ℚ_[ℓ]) ^ c' * x‖ ≤ 1 := by
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt ‖x‖
    (show (1 : ℝ) < ℓ by exact_mod_cast (Fact.out : ℓ.Prime).one_lt)
  refine ⟨c, fun c' hc' => ?_⟩
  have hℓ : (1 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) ^ c' := pow_pos (by linarith) _
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hℓ0, mul_one]
  exact hc.le.trans (pow_le_pow_right₀ hℓ hc')

/-- A finite family of elements of `ℚ_ℓ` becomes integral after multiplication by one power of
`ℓ`. -/
public theorem exists_pow_mul_norm_le_one_of_finite {ι : Type*} [Finite ι] (x : ι → ℚ_[ℓ]) :
    ∃ c : ℕ, ∀ i, ‖(ℓ : ℚ_[ℓ]) ^ c * x i‖ ≤ 1 := by
  have := Fintype.ofFinite ι
  choose c hc using fun i => exists_pow_mul_norm_le_one (x i)
  exact ⟨Finset.univ.sup c, fun i => hc i _ (Finset.le_sup (Finset.mem_univ i))⟩

variable {m : ℕ}

/-- **Clearing denominators in a span.** If the image in `ℚ_ℓ^m` of an integral vector `v` lies
in the `ℚ_ℓ`-span of the images of a set `S` of integral vectors, then some `ℓ^c v` lies in the
`ℤ_ℓ`-span of `S`. -/
public theorem exists_pow_smul_mem_span_of_mem_span_rat (S : Set (Fin m → ℤ_[ℓ]))
    (v : Fin m → ℤ_[ℓ])
    (hv : (fun i => (v i : ℚ_[ℓ])) ∈ Submodule.span ℚ_[ℓ]
      ((fun s : Fin m → ℤ_[ℓ] => fun i => (s i : ℚ_[ℓ])) '' S)) :
    ∃ c : ℕ, ((ℓ : ℤ_[ℓ]) ^ c) • v ∈ Submodule.span ℤ_[ℓ] S := by
  suffices h : ∀ y ∈ Submodule.span ℚ_[ℓ]
      ((fun s : Fin m → ℤ_[ℓ] => fun i => (s i : ℚ_[ℓ])) '' S),
      ∃ c : ℕ, ∃ z ∈ Submodule.span ℤ_[ℓ] S, ∀ i, (z i : ℚ_[ℓ]) = (ℓ : ℚ_[ℓ]) ^ c * y i by
    obtain ⟨c, z, hz, hzv⟩ := h _ hv
    refine ⟨c, ?_⟩
    convert hz using 1
    funext i
    apply PadicInt.ext
    rw [hzv i, Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨0, s, Submodule.subset_span hs, fun i => by simp⟩
  | zero => exact ⟨0, 0, Submodule.zero_mem _, fun i => by simp⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, z₁, hz₁, e₁⟩ := h₁
    obtain ⟨c₂, z₂, hz₂, e₂⟩ := h₂
    refine ⟨c₁ + c₂, ((ℓ : ℤ_[ℓ]) ^ c₂) • z₁ + ((ℓ : ℤ_[ℓ]) ^ c₁) • z₂,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hz₁) (Submodule.smul_mem _ _ hz₂), fun i => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PadicInt.coe_add, PadicInt.coe_mul,
      PadicInt.coe_pow, PadicInt.coe_natCast, e₁, e₂]
    ring
  | smul a y _ h =>
    obtain ⟨c, z, hz, e⟩ := h
    obtain ⟨c', hc'⟩ := exists_pow_mul_norm_le_one a
    let a' : ℤ_[ℓ] := ⟨(ℓ : ℚ_[ℓ]) ^ c' * a, hc' c' le_rfl⟩
    refine ⟨c + c', a' • z, Submodule.smul_mem _ _ hz, fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, e]
    show (ℓ : ℚ_[ℓ]) ^ c' * a * ((ℓ : ℚ_[ℓ]) ^ c * y i) = _
    ring

end Denominators

/-! ### Uniform bounds on invariants and coinvariants modulo `ℓ^n` -/

section Uniform

variable {ℓ : ℕ} [Fact ℓ.Prime] {m : ℕ} {G : Type*} [Group G] (τ : G →* GL (Fin m) ℤ_[ℓ])
  (N : Subgroup G)

/-- The rows of the matrices `τ(g) - 1`, `g ∈ N`. -/
public def invariantRows : Set (Fin m → ℤ_[ℓ]) :=
  {d | ∃ g ∈ N, ∃ i, d = ((τ g).val - 1) i}

/-- The integral vectors `τ(g) w - w`, `g ∈ N`. -/
public def coinvariantVectors : Set (Fin m → ℤ_[ℓ]) :=
  {d | ∃ g ∈ N, ∃ w, d = (τ g).val *ᵥ w - w}

/-- A `ℚ_ℓ`-linear functional on `ℚ_ℓ^m` is the dot product with its values on the standard
basis. -/
theorem dual_apply_eq_dotProduct (φ : Module.Dual ℚ_[ℓ] (Fin m → ℚ_[ℓ])) (w : Fin m → ℚ_[ℓ]) :
    φ w = w ⬝ᵥ fun j => φ (Pi.single j 1) := by
  conv_lhs => rw [← (Pi.basisFun ℚ_[ℓ] (Fin m)).sum_equivFun w]
  simp [map_sum, dotProduct, Pi.basisFun_apply]

/-- **No rational invariants means the rows of `τ(g) - 1` span.** -/
public theorem span_invariantRows_eq_top
    (h : ∀ v : Fin m → ℚ_[ℓ], (∀ g ∈ N, (τ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ v = v) → v = 0) :
    Submodule.span ℚ_[ℓ] ((fun s : Fin m → ℤ_[ℓ] => fun i => (s i : ℚ_[ℓ])) ''
      invariantRows τ N) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set v : Fin m → ℚ_[ℓ] := fun j => φ (Pi.single j 1)
  have hv : v = 0 := by
    refine h v fun g hg => ?_
    funext i
    have hrow := hle (Submodule.subset_span ⟨((τ g).val - 1) i, ⟨g, hg, i, rfl⟩, rfl⟩)
    rw [LinearMap.mem_ker, dual_apply_eq_dotProduct] at hrow
    have : ((τ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ v) i - v i =
        (fun j => ((((τ g).val - 1) i j : ℤ_[ℓ]) : ℚ_[ℓ])) ⬝ᵥ v := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply]
      have hx : ∀ x, ((((τ g).val i x - if i = x then 1 else 0 : ℤ_[ℓ])) : ℚ_[ℓ]) * v x =
          ((τ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ])) i x * v x - if i = x then v x else 0 := by
        intro x
        split_ifs
        · simp only [PadicInt.coe_sub, PadicInt.coe_one, sub_mul, one_mul, sub_left_inj,
            mul_eq_mul_right_iff]
          exact Or.inl rfl
        · simp only [sub_zero, mul_eq_mul_right_iff]
          exact Or.inl rfl
      rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ _)]
    exact sub_eq_zero.1 (this.trans hrow)
  apply hφ0
  refine LinearMap.ext fun w => ?_
  rw [dual_apply_eq_dotProduct, show (fun j => φ (Pi.single j 1)) = v from rfl, hv,
    dotProduct_zero, LinearMap.zero_apply]

/-- If the images of `S` span `ℚ_ℓ^m`, one power of `ℓ` pushes every integral vector into the
`ℤ_ℓ`-span of `S`. -/
private theorem exists_pow_smul_mem_span_of_span_eq_top (S : Set (Fin m → ℤ_[ℓ]))
    (hspan : Submodule.span ℚ_[ℓ] ((fun s : Fin m → ℤ_[ℓ] => fun i => (s i : ℚ_[ℓ])) '' S) = ⊤) :
    ∃ c : ℕ, ∀ v : Fin m → ℤ_[ℓ], ((ℓ : ℤ_[ℓ]) ^ c) • v ∈ Submodule.span ℤ_[ℓ] S := by
  have hi : ∀ i, ∃ c : ℕ, ((ℓ : ℤ_[ℓ]) ^ c) • (Pi.single i 1 : Fin m → ℤ_[ℓ]) ∈
      Submodule.span ℤ_[ℓ] S := fun i =>
    exists_pow_smul_mem_span_of_mem_span_rat _ _ (by simp [hspan])
  choose c hc using hi
  refine ⟨Finset.univ.sup c, fun v => ?_⟩
  rw [← (Pi.basisFun ℤ_[ℓ] (Fin m)).sum_equivFun v, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm, Pi.basisFun_apply,
    ← Nat.sub_add_cancel (Finset.le_sup (f := c) (Finset.mem_univ i)), pow_add, mul_smul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hc i))

/-- Every vector over `ℤ/ℓ^n` is the reduction of an integral vector. -/
private theorem exists_toZModPow_eq (n : ℕ) (w : Fin m → ZMod (ℓ ^ n)) :
    ∃ v : Fin m → ℤ_[ℓ], (fun j => PadicInt.toZModPow n (v j)) = w :=
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  (ZMod.ringHom_surjective (PadicInt.toZModPow n)).comp_left w

/-- **Invariants modulo `ℓ^n` are killed by a fixed power of `ℓ`.** If no nonzero vector of
`ℚ_ℓ^m` is fixed by `N`, there is `c` such that for every `n`, every vector of `(ℤ/ℓ^n)^m` fixed
by the reduction of `τ(N)` is killed by `ℓ^c`. -/
public theorem exists_pow_smul_eq_zero_of_invariants
    (h : ∀ v : Fin m → ℚ_[ℓ], (∀ g ∈ N, (τ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ v = v) → v = 0) :
    ∃ c : ℕ, ∀ (n : ℕ) (w : Fin m → ZMod (ℓ ^ n)),
      (∀ g ∈ N, (τ g).val.map (PadicInt.toZModPow n) *ᵥ w = w) → (ℓ ^ c : ℕ) • w = 0 := by
  have hspan := span_invariantRows_eq_top τ N h
  obtain ⟨c, hc⟩ := exists_pow_smul_mem_span_of_span_eq_top _ hspan
  refine ⟨c, fun n w hw => ?_⟩
  obtain ⟨v, rfl⟩ := exists_toZModPow_eq n w
  -- every vector of the span pairs with `v` into `ℓ^n ℤ_ℓ`
  have hrow : ∀ z ∈ Submodule.span ℤ_[ℓ] (invariantRows τ N),
      PadicInt.toZModPow n (z ⬝ᵥ v) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, i, rfl⟩ := hz
      have hgi := congrFun (hw g hg) i
      show PadicInt.toZModPow n ((((τ g).val - 1) *ᵥ v) i) = 0
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub, RingHom.map_mulVec]
      exact sub_eq_zero.2 hgi
    | zero => simp
    | add z₁ z₂ _ _ h₁ h₂ => rw [add_dotProduct, map_add, h₁, h₂, add_zero]
    | smul a z _ h => rw [smul_dotProduct, smul_eq_mul, map_mul, h, mul_zero]
  funext i
  have hci := hrow _ (hc (Pi.single i 1))
  rw [smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, map_mul, map_pow,
    map_natCast] at hci
  simpa [nsmul_eq_mul] using hci

/-- **No rational coinvariants means the integral vectors `τ(g) w - w` span rationally.** -/
public theorem span_coinvariantVectors_eq_top
    (h : Submodule.span ℚ_[ℓ] {d | ∃ g ∈ N, ∃ w : Fin m → ℚ_[ℓ],
      d = (τ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ w - w} = ⊤) :
    Submodule.span ℚ_[ℓ] ((fun s : Fin m → ℤ_[ℓ] => fun i => (s i : ℚ_[ℓ])) ''
      coinvariantVectors τ N) = ⊤ := by
  refine eq_top_iff.2 (h ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨g, hg, w, rfl⟩
  let L : (Fin m → ℚ_[ℓ]) →ₗ[ℚ_[ℓ]] (Fin m → ℚ_[ℓ]) :=
    ((τ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ])).mulVecLin - LinearMap.id
  have hL : ∀ j, L (Pi.single j 1) = fun i => ((((τ g).val *ᵥ Pi.single j 1 -
      Pi.single j 1 : Fin m → ℤ_[ℓ]) i : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp [L, Matrix.mulVec_single]
      try rfl
    · simp [L, Matrix.mulVec_single, hij]
      try rfl
  show L w ∈ _
  rw [← (Pi.basisFun ℚ_[ℓ] (Fin m)).sum_equivFun w, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, Pi.basisFun_apply, hL j]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨g, hg, Pi.single j 1, rfl⟩, rfl⟩)

/-- Reduction modulo `ℓ^n` carries the `ℤ_ℓ`-span of the vectors `τ(g) w - w` into the span of
the vectors `τ(g) u - u` over `ℤ/ℓ^n`. -/
public theorem toZModPow_mem_span_of_mem_span_coinvariantVectors (n : ℕ) {z : Fin m → ℤ_[ℓ]}
    (hz : z ∈ Submodule.span ℤ_[ℓ] (coinvariantVectors τ N)) :
    (fun j => PadicInt.toZModPow n (z j)) ∈ Submodule.span (ZMod (ℓ ^ n))
      {d | ∃ g ∈ N, ∃ u, d = (τ g).val.map (PadicInt.toZModPow n) *ᵥ u - u} := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, u, rfl⟩ := hz
    refine Submodule.subset_span ⟨g, hg, fun j => PadicInt.toZModPow n (u j), ?_⟩
    funext i
    rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, Pi.sub_apply]
    rfl
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext j
    simp
  | add z₁ z₂ _ _ h₁ h₂ =>
    convert Submodule.add_mem _ h₁ h₂ using 1
    funext j
    simp [map_add]
  | smul a z _ h =>
    convert Submodule.smul_mem _ (PadicInt.toZModPow n a) h using 1
    funext j
    simp [map_mul]

/-- **Coinvariants modulo `ℓ^n` are killed by a fixed power of `ℓ`.** If the vectors
`τ(g) w - w`, `g ∈ N`, span `ℚ_ℓ^m`, there is `c` such that for every `n`, `ℓ^c (ℤ/ℓ^n)^m` lies in
the span of the vectors `τ(g) u - u` over `ℤ/ℓ^n`, so `ℓ^c` kills the `N`-coinvariants. -/
public theorem exists_pow_smul_mem_span_of_coinvariants
    (h : Submodule.span ℚ_[ℓ] {d | ∃ g ∈ N, ∃ w : Fin m → ℚ_[ℓ],
      d = (τ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ w - w} = ⊤) :
    ∃ c : ℕ, ∀ (n : ℕ) (w : Fin m → ZMod (ℓ ^ n)), (ℓ ^ c : ℕ) • w ∈
      Submodule.span (ZMod (ℓ ^ n))
        {d | ∃ g ∈ N, ∃ u, d = (τ g).val.map (PadicInt.toZModPow n) *ᵥ u - u} := by
  have hspan := span_coinvariantVectors_eq_top τ N h
  obtain ⟨c, hc⟩ := exists_pow_smul_mem_span_of_span_eq_top _ hspan
  refine ⟨c, fun n w => ?_⟩
  obtain ⟨v, rfl⟩ := exists_toZModPow_eq n w
  convert toZModPow_mem_span_of_mem_span_coinvariantVectors τ N n (hc v) using 1
  funext j
  simp [nsmul_eq_mul, map_mul, map_pow]

end Uniform

/-! ### Transport from `E` to the restriction of scalars -/

section Transport

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E] [Algebra ℤ_[ℓ] E] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E] {d r : ℕ}
  (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) {G : Type*} [Group G]
  (σO : G →* GL (Fin r) (integralClosure ℤ_[ℓ] E)) (σ : G →* GL (Fin r) E) (P : GL (Fin r) E)
  (hP : ∀ g, Matrix.GeneralLinearGroup.map (algebraMap (integralClosure ℤ_[ℓ] E) E) (σO g) =
    P * σ g * P⁻¹)
  (N : Subgroup G)

/-- The restriction of scalars `G →* GL_{rd}(ℤ_ℓ)` of `σ_O` along `b`. -/
public abbrev restrictScalarsHom : G →* GL (Fin (r * d)) ℤ_[ℓ] :=
  (Units.map (coefficientMatrixRingHom b r).toMonoidHom).comp σO

include hP in
/-- Read over `ℚ_ℓ`, the restriction of scalars of `σ_O` is that of `P σ P⁻¹` along the
`ℚ_ℓ`-basis of `E` given by `b`. -/
public theorem restrictScalarsHom_map (g : G) :
    (restrictScalarsHom b σO g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) =
      coefficientMatrixRingHom (rationalBasis b) r (P * σ g * P⁻¹ : GL (Fin r) E).val := by
  rw [← hP g]
  exact map_coefficientMatrixRingHom b r (σO g).val

include hP in
/-- **No invariants over `E` gives no invariants over `ℚ_ℓ`** for the restriction of scalars. -/
public theorem restrictScalars_invariants_eq_zero
    (h : ∀ v : Fin r → E, (∀ g ∈ N, (σ g : Matrix (Fin r) (Fin r) E) *ᵥ v = v) → v = 0)
    (v : Fin (r * d) → ℚ_[ℓ])
    (hv : ∀ g ∈ N, (restrictScalarsHom b σO g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ v = v) :
    v = 0 := by
  set e := coefficientVecEquiv (rationalBasis b) r
  have hu : ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ e v = 0 := by
    refine h _ fun g hg => ?_
    have h1 := congrArg e (hv g hg)
    rw [restrictScalarsHom_map b σO σ P hP, coefficientVecEquiv_mulVec] at h1
    have key : P⁻¹ * (P * σ g * P⁻¹) = σ g * P⁻¹ := by group
    calc (σ g : Matrix (Fin r) (Fin r) E) *ᵥ
          (((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ e v)
        = ((σ g * P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ e v := by
          rw [Units.val_mul, Matrix.mulVec_mulVec]
      _ = ((P⁻¹ * (P * σ g * P⁻¹) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ e v := by
          rw [key]
      _ = ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
          (((P * σ g * P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ e v) := by
          rw [Units.val_mul P⁻¹ (P * σ g * P⁻¹), Matrix.mulVec_mulVec]
      _ = _ := by rw [h1]
  have : e v = 0 := by
    have := congrArg (fun x => (P : Matrix (Fin r) (Fin r) E) *ᵥ x) hu
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact e.map_eq_zero_iff.1 this

/-- If the vectors `σ(g) w - w`, `g ∈ N`, span `E^r`, so do the vectors `(P σ(g) P⁻¹) y - y`. -/
public theorem span_conj_mulVec_sub_eq_top
    (h : Submodule.span E {w | ∃ g ∈ N, ∃ v, w = (σ g : Matrix (Fin r) (Fin r) E) *ᵥ v - v} = ⊤) :
    Submodule.span E {x | ∃ g ∈ N, ∃ y, x = (P * σ g * P⁻¹ : GL (Fin r) E).val *ᵥ y - y} = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x ∈
      Submodule.span E {w | ∃ g ∈ N, ∃ v, w = (σ g : Matrix (Fin r) (Fin r) E) *ᵥ v - v} := by
    simp [h]
  have hmap : ∀ y ∈ Submodule.span E {w | ∃ g ∈ N, ∃ v,
      w = (σ g : Matrix (Fin r) (Fin r) E) *ᵥ v - v},
      (P : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Submodule.span E
        {x | ∃ g ∈ N, ∃ y, x = (P * σ g * P⁻¹ : GL (Fin r) E).val *ᵥ y - y} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, hg, v, rfl⟩ := hy
      refine Submodule.subset_span ⟨g, hg, (P : Matrix (Fin r) (Fin r) E) *ᵥ v, ?_⟩
      have key : P * σ g * P⁻¹ * P = P * σ g := by group
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp only [← Units.val_mul, key]
    | zero => simp
    | add x y _ _ hx hy => simpa [Matrix.mulVec_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa [Matrix.mulVec_smul] using Submodule.smul_mem _ a hx
  have := hmap _ hx
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at this

/-- A set stable under the scalars of `S` has the same span over `S` as over `R`. -/
public theorem mem_span_of_mem_span_of_smul_mem {R S V : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] [AddCommMonoid V] [Module R V] [Module S V] [IsScalarTower R S V] {A : Set V}
    (hA : ∀ (a : S), ∀ x ∈ A, a • x ∈ A) {x : V} (hx : x ∈ Submodule.span S A) :
    x ∈ Submodule.span R A := by
  have hsmul : ∀ (a : S), ∀ x ∈ Submodule.span R A, a • x ∈ Submodule.span R A := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hA a x hx)
    | zero => simp
    | add x y _ _ hx hy => simpa [smul_add] using Submodule.add_mem _ hx hy
    | smul q x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ q hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact hsmul a x hx

include hP in
/-- **No coinvariants over `E` gives no coinvariants over `ℚ_ℓ`** for the restriction of
scalars: the set of the `σ(g) w - w` is stable under `E`, so its `ℚ_ℓ`-span is its `E`-span. -/
public theorem restrictScalars_span_coinvariants_eq_top
    (h : Submodule.span E {w | ∃ g ∈ N, ∃ v, w = (σ g : Matrix (Fin r) (Fin r) E) *ᵥ v - v} = ⊤) :
    Submodule.span ℚ_[ℓ] {w | ∃ g ∈ N, ∃ v : Fin (r * d) → ℚ_[ℓ],
      w = (restrictScalarsHom b σO g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ v - v} = ⊤ := by
  set e := coefficientVecEquiv (rationalBasis b) r
  set A : Set (Fin r → E) := {x | ∃ g ∈ N, ∃ y, x = (P * σ g * P⁻¹ : GL (Fin r) E).val *ᵥ y - y}
  set W := Submodule.span ℚ_[ℓ] {w | ∃ g ∈ N, ∃ v : Fin (r * d) → ℚ_[ℓ],
      w = (restrictScalarsHom b σO g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ v - v}
  -- the image of `W` is the `ℚ_ℓ`-span of `A`
  have hWA : ∀ x ∈ Submodule.span ℚ_[ℓ] A, e.symm x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, y, rfl⟩ := hx
      refine Submodule.subset_span ⟨g, hg, e.symm y, ?_⟩
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, map_sub, restrictScalarsHom_map b σO σ P hP,
        coefficientVecEquiv_mulVec, LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simpa using W.add_mem hx hy
    | smul a x _ hx => simpa using W.smul_mem a hx
  have hAsmul : ∀ (a : E), ∀ x ∈ A, a • x ∈ A := by
    rintro a _ ⟨g, hg, y, rfl⟩
    exact ⟨g, hg, a • y, by rw [Matrix.mulVec_smul, smul_sub]⟩
  have hAtop : Submodule.span E A = ⊤ := span_conj_mulVec_sub_eq_top σ P N h
  refine eq_top_iff.2 fun w _ => ?_
  have hw : e w ∈ Submodule.span ℚ_[ℓ] A :=
    mem_span_of_mem_span_of_smul_mem hAsmul (hAtop ▸ Submodule.mem_top)
  simpa using hWA _ hw

end Transport

/-! ### The twist `ρ ⊗ χ` -/

section Twist

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E] [Algebra ℤ_[ℓ] E] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E]
  [TopologicalSpace E] [IsModuleTopology ℚ_[ℓ] E] {d : ℕ}
  (b : Basis (Fin d) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] (ρ : G →* GL (Fin 2) E)
  (hρ : Continuous fun g => (ρ g : Matrix (Fin 2) (Fin 2) E)) (χ : G →* Eˣ)
  (hχ : Continuous fun g => (χ g : E)) (hirr : Stacks.Adeles.IsAbsolutelyIrreducible ρ)
  (N : Subgroup G) [N.Normal] (hN : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N)

/-- The `ℤ_ℓ`-representation of rank `2 [E : ℚ_ℓ]` underlying `ρ_O ⊗ χ_O`, whose reductions
modulo `ℓ^n` are the finite levels of `ℱ_{ρ ⊗ χ}`. -/
public abbrev twistRestrictScalarsHom : G →* GL (Fin (2 * d)) ℤ_[ℓ] :=
  restrictScalarsHom b (characterTwist (integralClosureModel ℓ ρ hρ)
    (integralClosureCharacter ℓ χ hχ))

include hirr hN in
/-- **The invariants of `N` on the levels of `ρ_O ⊗ χ_O` are killed by a fixed power of `ℓ`**:
for `ρ` absolutely irreducible and `N` normal containing every commutator (the image of
`π₁(X_k̄)` in `π₁(X)`), there is `c` such that `ℓ^c` kills the `N`-invariants of
`(ℤ/ℓ^n)^{2d}` for every `n`. -/
public theorem exists_pow_smul_eq_zero_of_invariants_twist :
    ∃ c : ℕ, ∀ (n : ℕ) (w : Fin (2 * d) → ZMod (ℓ ^ n)),
      (∀ g ∈ N, (twistRestrictScalarsHom b ρ hρ χ hχ g).val.map (PadicInt.toZModPow n) *ᵥ w = w) →
        (ℓ ^ c : ℕ) • w = 0 := by
  have hσ := Stacks.Drinfeld.IsAbsolutelyIrreducible.of_smul hirr χ
    (ρ' := characterTwist ρ χ) fun g => characterTwist_val ρ χ g
  exact exists_pow_smul_eq_zero_of_invariants _ N fun v hv =>
    restrictScalars_invariants_eq_zero b _ (characterTwist ρ χ) _
      (map_characterTwist_integralClosureModel ρ hρ χ hχ) N
      (fun v hv => Stacks.Drinfeld.IsAbsolutelyIrreducible.eq_zero_of_forall_mulVec_eq hσ N hN hv)
      v hv

include hirr hN in
/-- **The coinvariants of `N` on the levels of `ρ_O ⊗ χ_O` are killed by a fixed power of
`ℓ`**: there is `c` such that for every `n`, `ℓ^c (ℤ/ℓ^n)^{2d}` lies in the span of the vectors
`τ(g) u - u`, `g ∈ N`. -/
public theorem exists_pow_smul_mem_span_of_coinvariants_twist :
    ∃ c : ℕ, ∀ (n : ℕ) (w : Fin (2 * d) → ZMod (ℓ ^ n)), (ℓ ^ c : ℕ) • w ∈
      Submodule.span (ZMod (ℓ ^ n)) {x | ∃ g ∈ N, ∃ u,
        x = (twistRestrictScalarsHom b ρ hρ χ hχ g).val.map (PadicInt.toZModPow n) *ᵥ u - u} := by
  have hσ := Stacks.Drinfeld.IsAbsolutelyIrreducible.of_smul hirr χ
    (ρ' := characterTwist ρ χ) fun g => characterTwist_val ρ χ g
  exact exists_pow_smul_mem_span_of_coinvariants _ N
    (restrictScalars_span_coinvariants_eq_top b _ (characterTwist ρ χ) _
      (map_characterTwist_integralClosureModel ρ hρ χ hχ) N
      (Stacks.Drinfeld.IsAbsolutelyIrreducible.span_mulVec_sub_eq_top hσ N hN))

end Twist

/-! ### Limits -/

section Limit

open _root_.Stacks.AlgebraicGeometry AlgebraicGeometry.SmallEtale

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (AlgebraicGeometry.SmallEtale.topology B S.1 S.property)
      (AlgebraicGeometry.SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.1 T.property),
    HasWeakSheafify ((AlgebraicGeometry.SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (AlgebraicGeometry.SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ AlgebraicGeometry.Spec (.of k))
  [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.IsSeparated f]
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

omit [Fintype k] [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.IsSeparated f] in
/-- **A limit killed by `ℓ^c` vanishes rationally.** If every level `Hⁱ_c(X_k̄, F_n)` of the
inverse system defining `Hⁱ_c(X_k̄, F)` is killed by one power `ℓ^c`, then so is the limit, and
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) = Hⁱ_c(X_k̄, F) ⊗ ℚ_ℓ = 0`. -/
public theorem subsingleton_rationalGeometricCompactlySupportedCohomology_of_pow_smul
    (F : LAdicSheaf B X ℓ) (i : ℤ) (c : ℕ)
    (h : ∀ (n : ℕ) (y : (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n)), ((ℓ : ℤ_[ℓ]) ^ c) • y = 0) :
    Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have hL0 : ((ℓ : ℤ_[ℓ]) ^ c) •
      𝟙 (limit (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)) =
        0 := by
    refine limit.hom_ext fun n => ?_
    rw [Linear.smul_comp, Category.id_comp, zero_comp]
    ext y
    exact h n.unop _
  have hL : ∀ x : (limit (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar
      F i) : ModuleCat ℤ_[ℓ]), ((ℓ : ℤ_[ℓ]) ^ c) • x = 0 := fun x => by
    have := congrArg (fun φ => ModuleCat.Hom.hom φ x) hL0
    simpa only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply] using this
  refine subsingleton_of_forall_eq 0 fun z => ?_
  have hℓ : ((ℓ : ℚ_[ℓ]) ^ c) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul s m =>
    let s' : (ModuleCat.restrictScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℚ_[ℓ] ℚ_[ℓ]) := ((ℓ : ℚ_[ℓ]) ^ c)⁻¹ * (show ℚ_[ℓ] from s)
    have hs : s = ((ℓ : ℤ_[ℓ]) ^ c) • s' := by
      show (show ℚ_[ℓ] from s) = algebraMap ℤ_[ℓ] ℚ_[ℓ] ((ℓ : ℤ_[ℓ]) ^ c) *
        (((ℓ : ℚ_[ℓ]) ^ c)⁻¹ * (show ℚ_[ℓ] from s))
      rw [map_pow, map_natCast, ← mul_assoc, mul_inv_cancel₀ hℓ, one_mul]
    have hm : ((ℓ : ℤ_[ℓ]) ^ c) • m = 0 := hL m
    rw [hs, TensorProduct.smul_tmul, hm, TensorProduct.tmul_zero]
    rfl
  | add x y hx hy => rw [hx, hy]; exact add_zero _

end Limit

end Stacks.Drinfeld

end
