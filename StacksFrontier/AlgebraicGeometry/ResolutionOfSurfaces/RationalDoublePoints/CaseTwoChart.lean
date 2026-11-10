module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseTwoInvariant

/-!
# Case II of Section 54.12 on a chart

Let `(A, 𝔪, κ)` be a Noetherian local ring with `𝔪 = (x₁, x₂, x₃)`, let `A' = A[𝔪/x₁]` with
`yᵢ = xᵢ/x₁`, and suppose the chart relation reads `y₃² = x₁G` for some `G ∈ A'` which, modulo
`(x₁, y₃)`, is a polynomial `H(y₂)` of degree at most three. This is the situation of the source's
"Resolution in case II", where `G = Σ aᵢⱼₖ yᵢyⱼyₖ` and `H` is the source's `h`, and also of the
blowup of a ring satisfying the exact case II invariant `x₃² = x₁F`, `F ∈ 𝔪²`, where `H` has
degree at most two.

At a maximal ideal `𝔪'` of `A'` containing `𝔪A'` at which `B = A'_{𝔪'}` is a singular normal
two-dimensional local ring in case II, the analysis of the source gives
(`AlgebraicGeometry.exists_hasDoubleLineRelation_of_chart`):

* `y₃ ∈ 𝔪'`, so the point lies on the line `C : x₁ = y₃ = 0`, at a prime `π` of `κ[y₂]`;
* `H ≠ 0` modulo `𝔪` ("`h` must be nonzero in the residue field of `ξ`"): otherwise `y₃/x₁` would
  be integral over `B`, so `y₃ ∈ x₁B` and `B` would be regular;
* `π² ∣ H` modulo `𝔪`, for otherwise `B` is in case I (the source's footnote); as `deg H ≤ 3`, `π`
  is linear and the point is `κ`-rational ("at most one singular point `p ∈ C` falling into case
  II which is moreover `κ`-rational");
* at the point, after completing the square, the exact invariant
  `AlgebraicGeometry.HasDoubleLineRelation` holds for `x₁, y₂ - c, y₃ + μx₁`, and
  `AlgebraicGeometry.HasDoubleLineRelationUnit` holds when the `(y₂ - c)²`-coefficient of `H` is
  a unit.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public section

open IsLocalRing Polynomial

universe u

namespace AlgebraicGeometry

/-! ### Integral closure -/

/-- **The integrality step of case II.** In an integrally closed domain, `u² = v(vα + uβ)` forces
`u ∈ vB`: the fraction `u/v` is a root of `T² - βT - α`. -/
theorem mem_span_singleton_of_sq_eq_mul {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] {u v α β : B} (h : u * u = v * (v * α + u * β)) :
    u ∈ Ideal.span {v} := by
  by_cases hv : v = 0
  · rw [hv, zero_mul] at h
    rw [mul_self_eq_zero.mp h]
    exact zero_mem _
  have hv' : algebraMap B (FractionRing B) v ≠ 0 :=
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hv))
  set s : (FractionRing B) := algebraMap B (FractionRing B) u / algebraMap B (FractionRing B) v
      with hs
  have hint : _root_.IsIntegral B s := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X - Polynomial.C α, ?_, ?_⟩
    · have : (Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X - Polynomial.C α : B[X]) =
        Polynomial.X ^ 2 - (Polynomial.C β * Polynomial.X + Polynomial.C α) := by ring
      rw [this]
      exact monic_X_pow_sub (by
        refine (degree_add_le _ _).trans_lt ?_
        refine max_lt ((degree_C_mul_X_le β).trans_lt (by norm_num)) ?_
        exact (degree_C_le).trans_lt (by norm_num))
    · simp only [eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
      have hh := congrArg (algebraMap B (FractionRing B)) h
      simp only [map_mul, map_add] at hh
      rw [hs]
      field_simp [hv']
      linear_combination hh
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hu : u = v * t := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul, ht, hs, mul_div_cancel₀ _ hv']
  rw [hu]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-! ### Polynomials over the residue field -/

/-- **Taylor expansion to second order** at an arbitrary point, over any commutative ring. -/
theorem exists_eq_taylor_two {R : Type*} [CommRing R] (H : R[X]) (c : R) :
    ∃ c₀ d₀ : R, ∃ T : R[X], H = Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C
        c) + (Polynomial.X - Polynomial.C c) ^ 2 * T := by
  have h1 := modByMonic_add_div H (Polynomial.X - Polynomial.C c)
  have h2 := modByMonic_add_div (H /ₘ (Polynomial.X - Polynomial.C c)) (Polynomial.X - Polynomial.C
      c)
  rw [modByMonic_X_sub_C_eq_C_eval] at h1 h2
  refine ⟨H.eval c, (H /ₘ (Polynomial.X - Polynomial.C c)).eval c, (H /ₘ (Polynomial.X -
      Polynomial.C c)) /ₘ (Polynomial.X - Polynomial.C c), ?_⟩
  conv_lhs => rw [← h1, ← h2]
  ring

/-- **A prime whose square divides a nonzero polynomial of degree at most three is linear.** -/
theorem exists_dvd_iff_X_sub_C_dvd {k : Type*} [Field k] {π h : k[X]} (hπ : Irreducible π)
    (hh : h ≠ 0) (hdeg : h.natDegree ≤ 3) (hdvd : π ^ 2 ∣ h) :
    ∃ c : k, ∀ P : k[X], π ∣ P ↔ (Polynomial.X - Polynomial.C c) ∣ P := by
  obtain ⟨ψ, rfl⟩ := hdvd
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hψ0 : ψ ≠ 0 := fun h => hh (by rw [h, mul_zero])
  have hdeg' : 2 * π.natDegree + ψ.natDegree ≤ 3 := by
    rw [natDegree_mul (pow_ne_zero 2 hπ0) hψ0, natDegree_pow] at hdeg
    exact hdeg
  have hpos : 0 < π.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hπ)
  have h1 : π.degree = 1 := by
    rw [degree_eq_natDegree hπ0]
    norm_cast
    omega
  obtain ⟨c, hc⟩ := exists_root_of_degree_eq_one h1
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hc
  have hXu : ¬ IsUnit (Polynomial.X - Polynomial.C c) := fun hu => by
    have := degree_eq_zero_of_isUnit hu
    rw [degree_X_sub_C] at this
    exact one_ne_zero this
  have hru : IsUnit r := (hπ.isUnit_or_isUnit hr).resolve_left hXu
  refine ⟨c, fun P => ⟨fun h => (Dvd.intro r hr.symm).trans h, fun h => ?_⟩⟩
  obtain ⟨u, hu⟩ := hru
  refine dvd_trans (show π ∣ Polynomial.X - Polynomial.C c from ⟨((u⁻¹ : (k[X])ˣ) : k[X]), ?_⟩) h
  rw [hr, ← hu, mul_assoc, Units.mul_inv, mul_one]

/-- In a prime ideal, `a * a = b * c` with `b` in the ideal forces `a` into it. -/
private theorem mem_of_mul_self_eq_mul {R : Type*} [CommRing R] {M : Ideal R} [M.IsPrime]
    {a b c : R} (h : a * a = b * c) (hb : b ∈ M) : a ∈ M :=
  (Ideal.IsPrime.mem_or_mem inferInstance (h ▸ Ideal.mul_mem_right _ _ hb)).elim id id

/-- A polynomial with coefficients in `𝔪_A`, evaluated along `g`, lies in `(W)` when
`g(𝔪_A) ⊆ (W)`. -/
private theorem eval₂_mem_span_of_map_eq_zero_aux {A R : Type*} [CommRing A] [IsLocalRing A]
    [CommRing R] (g : A →+* R) (W Y : R) (hdiv : ∀ r ∈ maximalIdeal A, g r ∈ Ideal.span {W})
    {P : A[X]} (hP : P.map (residue A) = 0) : P.eval₂ g Y ∈ Ideal.span {W} := by
  rw [eval₂_eq_sum_range]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hdiv _ ?_)
  rw [← residue_eq_zero_iff, ← coeff_map, hP, coeff_zero]

/-! ### Points of the first chart on the line `x₁ = y₃ = 0` -/

section Chart

variable {A : Type u} [CommRing A] [IsLocalRing A] {x : Fin 3 → A}
  (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away (x 0) S]

/-- **Every element of the chart is a polynomial in `y₂` modulo `y₃`.** -/
theorem exists_sub_aeval_mem_span_chartFraction (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (z : affineBlowupAlgebra (maximalIdeal A) (x 0) S) :
    ∃ P : A[X], z - aeval (chartFraction S hx 1) P ∈ Ideal.span {chartFraction S hx 2} := by
  have hz : z ∈ Algebra.adjoin A (Set.range (chartFraction S hx)) := by
    rw [adjoin_range_chartFraction_eq_top S hx hspan]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    have hidx : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide
    rcases hidx i with rfl | rfl | rfl
    · exact ⟨1, by simp [chartFraction_zero]⟩
    · exact ⟨Polynomial.X, by simp⟩
    · exact ⟨0, by simp⟩
  | algebraMap r => exact ⟨Polynomial.C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨P, hP⟩ := hu
    obtain ⟨Q, hQ⟩ := hv
    exact ⟨P + Q, by rw [map_add, add_sub_add_comm]; exact Ideal.add_mem _ hP hQ⟩
  | mul u v _ _ hu hv =>
    obtain ⟨P, hP⟩ := hu
    obtain ⟨Q, hQ⟩ := hv
    refine ⟨P * Q, ?_⟩
    have heq : u * v - aeval (chartFraction S hx 1) (P * Q) =
        (u - aeval (chartFraction S hx 1) P) * v +
          aeval (chartFraction S hx 1) P * (v - aeval (chartFraction S hx 1) Q) := by
      rw [map_mul]; ring
    rw [heq]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hP) (Ideal.mul_mem_left _ _ hQ)

/-- Elements of `𝔪` map into `x₁A'`. -/
private theorem algebraMap_mem_span_of_mem_maximalIdeal (hx : ∀ i, x i ∈ maximalIdeal A) {r : A}
    (hr : r ∈ maximalIdeal A) :
    algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) r ∈
      Ideal.span {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)} := by
  rw [← affineBlowupAlgebra.map_ideal_eq_span_singleton (maximalIdeal A) (x 0) (hx 0)]
  exact Ideal.mem_map_of_mem _ hr

/-- A polynomial with coefficients in `𝔪`, evaluated at `y₂`, lies in `x₁A'`. -/
theorem aeval_mem_span_of_map_eq_zero (hx : ∀ i, x i ∈ maximalIdeal A) {P : A[X]}
    (hP : P.map (residue A) = 0) :
    aeval (chartFraction S hx 1) P ∈
      Ideal.span {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)} := by
  rw [aeval_def]
  exact eval₂_mem_span_of_map_eq_zero_aux (algebraMap A _) _ _
    (fun _ hr => algebraMap_mem_span_of_mem_maximalIdeal S hx hr) hP

/-- **A point of the first chart on the line `y₃ = 0`.** A maximal ideal `𝔪'` of `A[𝔪/x₁]`
containing `𝔪A'` and `y₃` is `(x₁, y₃, Pl(y₂))` for a lift `Pl` of an irreducible `π ∈ κ[y₂]`, and
`P(y₂) ∈ 𝔪'` exactly when `π` divides `P` modulo `𝔪`. -/
theorem exists_irreducible_of_chartFraction_mem (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (M : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) [hM : M.IsMaximal]
    (hle : Ideal.map (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S))
      (maximalIdeal A) ≤ M) (hy : chartFraction S hx 2 ∈ M) :
    ∃ π : (ResidueField A)[X], Irreducible π ∧
      (∀ P : A[X], aeval (chartFraction S hx 1) P ∈ M ↔ π ∣ P.map (residue A)) ∧
      ∃ Pl : A[X], Pl.map (residue A) = π ∧
        M = Ideal.span {algebraMap A _ (x 0), chartFraction S hx 2,
          aeval (chartFraction S hx 1) Pl} := by
  classical
  let A' := affineBlowupAlgebra (maximalIdeal A) (x 0) S
  let θ : A[X] →+* A' := (aeval (chartFraction S hx 1)).toRingHom
  let ρ : A[X] →+* (ResidueField A)[X] := mapRingHom (residue A)
  have hρ : Function.Surjective ρ := map_surjective _ residue_surjective
  have hx0 : algebraMap A A' (x 0) ∈ M := hle (Ideal.mem_map_of_mem _ (hx 0))
  set K := M.comap θ with hK
  have hker : RingHom.ker ρ ≤ K := fun P hP =>
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx0))
      (aeval_mem_span_of_map_eq_zero S hx (RingHom.mem_ker.mp hP))
  -- `A[X] → A'/𝔪'` is surjective, so `K` is maximal
  have hsurj : Function.Surjective ((Ideal.Quotient.mk M).comp θ) := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨P, hP⟩ := exists_sub_aeval_mem_span_chartFraction S hx hspan z
    refine ⟨P, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    have : θ P - z = -(z - aeval (chartFraction S hx 1) P) := by simp [θ]
    rw [this]
    exact neg_mem ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy)) hP)
  have hKmax : K.IsMaximal := by
    let : Field (A' ⧸ M) := Ideal.Quotient.field M
    have h := RingHom.ker_isMaximal_of_surjective _ hsurj
    rwa [← RingHom.comap_ker, Ideal.mk_ker] at h
  have hcomap : (K.map ρ).comap ρ = K := by
    rw [Ideal.comap_map_of_surjective _ hρ, sup_eq_left.mpr (by
      rw [← RingHom.ker_eq_comap_bot]; exact hker)]
  have hKbar : (K.map ρ).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective ρ hρ hKmax).resolve_left fun htop => ?_
    rw [htop, Ideal.comap_top] at hcomap
    exact hKmax.ne_top hcomap.symm
  set π := Submodule.IsPrincipal.generator (K.map ρ) with hπdef
  have hπspan : K.map ρ = Ideal.span {π} := (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hπ0 : π ≠ 0 := by
    intro h0
    have hbot : K.map ρ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hKbar
      (Polynomial.not_isField _)
    exact hbot (by rw [hπspan, h0, Ideal.span_singleton_eq_bot.mpr rfl])
  have hπprime : Prime π := (Ideal.span_singleton_prime hπ0).mp (hπspan ▸ hKbar.isPrime)
  have hmemK : ∀ P : A[X], aeval (chartFraction S hx 1) P ∈ M ↔ π ∣ P.map (residue A) := by
    intro P
    rw [← Ideal.mem_span_singleton, ← hπspan]
    exact ⟨fun h => Ideal.mem_map_of_mem ρ (show P ∈ K from h),
      fun h => show P ∈ K by rw [← hcomap]; exact h⟩
  obtain ⟨Pl, hPl⟩ := hρ π
  refine ⟨π, hπprime.irreducible, hmemK, Pl, hPl, le_antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨P, hP⟩ := exists_sub_aeval_mem_span_chartFraction S hx hspan z
    have hPM : aeval (chartFraction S hx 1) P ∈ M := by
      have h := M.sub_mem hz ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy)) hP)
      rwa [sub_sub_cancel] at h
    obtain ⟨Qbar, hQbar⟩ := (hmemK P).mp hPM
    obtain ⟨Q, rfl⟩ := hρ Qbar
    have hdiff : (P - Pl * Q).map (residue A) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul]
      change P.map (residue A) - ρ Pl * ρ Q = 0
      rw [hPl, ← hQbar, sub_self]
    have h1 := aeval_mem_span_of_map_eq_zero S hx hdiff
    have hz' : z = (z - aeval (chartFraction S hx 1) P) +
        aeval (chartFraction S hx 1) (P - Pl * Q) +
        aeval (chartFraction S hx 1) Pl * aeval (chartFraction S hx 1) Q := by
      rw [map_sub, map_mul]; ring
    rw [hz']
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.span_mono (by intro t ht; rw [Set.mem_singleton_iff.mp ht]; simp) hP
    · exact Ideal.span_mono (by intro t ht; rw [Set.mem_singleton_iff.mp ht]; simp) h1
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨hx0, hy, (hmemK Pl).mpr (by change π ∣ ρ Pl; rw [hPl])⟩

/-- A maximal ideal `(x₁, y₂ - t₁, y₃ - t₂)` of the chart has residue field a quotient of `A`. -/
private theorem surjective_quotient_comp_algebraMap (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (M : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) (t₁ t₂ : A)
    (hM : M = Ideal.span {algebraMap A _ (x 0), chartFraction S hx 1 - algebraMap A _ t₁,
      chartFraction S hx 2 - algebraMap A _ t₂}) :
    Function.Surjective ((Ideal.Quotient.mk M).comp
      (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S))) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_span_chartFraction_sub S hx hspan t₁ t₂ z
  refine ⟨r, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, ← neg_sub, hM]
  exact neg_mem (Ideal.span_mono (Set.subset_insert _ _) hr)

end Chart

/-- A polynomial of degree at most one divisible by `(X - c)²` is zero: in a Taylor expansion
`H = c₀ + d₀(X - c) + (X - c)²T` with `(X - c)² ∣ H`, `c₀ = d₀ = 0`. -/
theorem eq_zero_of_sq_dvd_taylor {k : Type*} [Field k] {H T : k[X]} {c c₀ d₀ : k}
    (hT : H = Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c) +
      (Polynomial.X - Polynomial.C c) ^ 2 * T)
    (hdvd : (Polynomial.X - Polynomial.C c) ^ 2 ∣ H) : c₀ = 0 ∧ d₀ = 0 := by
  have h1 : (Polynomial.X - Polynomial.C c) ^ 2 ∣
      Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c) := by
    have : Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c) =
        H - (Polynomial.X - Polynomial.C c) ^ 2 * T := by rw [hT]; ring
    rw [this]
    exact dvd_sub hdvd (dvd_mul_right _ _)
  have h0 : Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c) = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h1 ?_
    rw [degree_pow, degree_X_sub_C]
    refine (degree_add_le _ _).trans_lt (max_lt ((degree_C_le).trans_lt (by norm_num)) ?_)
    refine (degree_mul_le _ _).trans_lt ?_
    rw [degree_X_sub_C]
    refine lt_of_le_of_lt (add_le_add (degree_C_le (a := d₀)) le_rfl) ?_
    norm_num
  have hc₀ : c₀ = 0 := by simpa using congrArg (Polynomial.eval c) h0
  refine ⟨hc₀, ?_⟩
  simpa [hc₀, coeff_C, mul_sub, coeff_C_mul] using congrArg (fun P => Polynomial.coeff P 1) h0

variable {B : Type*} [CommRing B] [IsLocalRing B]

/-- **Completing the square at a rational point of the line, in the local ring.** Let
`g : A → B` with `g(𝔪_A) ⊆ (W)`, `𝔪_B = (W, Y₂ - gc, Y₃)`, `Y₃² = WG` and
`G ≡ H(Y₂)` modulo `(W, Y₃)`, where `H = c₀ + d₀(X - c) + (X - c)²T` with `c₀, d₀ ∈ 𝔪_A`. If `B`
is in case II, then for some `μ` the generators `W, Y₂ - gc, Y₃ + μW` satisfy the case II
invariant, with `F ≡ T(Y₂)(Y₂ - gc)²` modulo `(W, Y₃ + μW)𝔪`. -/
theorem hasDoubleLineRelation_of_taylor {A : Type*} [CommRing A] [IsLocalRing A]
    (hII : ¬ IsCaseOne B) (g : A →+* B) (W Y₂ Y₃ G : B)
    (hdiv : ∀ r ∈ maximalIdeal A, g r ∈ Ideal.span {W}) (c c₀ d₀ : A) (H T : A[X])
    (hc₀ : c₀ ∈ maximalIdeal A) (hd₀ : d₀ ∈ maximalIdeal A)
    (hT : H = Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c) +
      (Polynomial.X - Polynomial.C c) ^ 2 * T)
    (hspan : maximalIdeal B = Ideal.span {W, Y₂ - g c, Y₃}) (hrel : Y₃ * Y₃ = W * G)
    (hG : G - H.eval₂ g Y₂ ∈ Ideal.span {W, Y₃}) :
    ∃ μ : B, HasDoubleLineRelation B ![W, Y₂ - g c, Y₃ + μ * W] ∧
      (IsUnit (T.eval₂ g Y₂) → HasDoubleLineRelationUnit B ![W, Y₂ - g c, Y₃ + μ * W]) := by
  set T₁ := Y₂ - g c with hT₁
  set w : Fin 3 → B := ![W, T₁, Y₃] with hw
  have hwspan : Ideal.span (Set.range w) = maximalIdeal B := by
    rw [span_range_fin_three, hspan]; rfl
  have hmem : ∀ i, w i ∈ maximalIdeal B := fun i => hwspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hTm : T₁ ∈ maximalIdeal B := hmem 1
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hG
  obtain ⟨e₀, he₀⟩ := Ideal.mem_span_singleton'.mp (hdiv c₀ hc₀)
  obtain ⟨e₁, he₁⟩ := Ideal.mem_span_singleton'.mp (hdiv d₀ hd₀)
  have hGexp : G = W * (e₀ + e₁ * T₁ + a) + T.eval₂ g Y₂ * T₁ * T₁ + b * Y₃ := by
    have hH : H.eval₂ g Y₂ = g c₀ + g d₀ * T₁ + T₁ ^ 2 * T.eval₂ g Y₂ := by
      rw [hT, eval₂_add, eval₂_add, eval₂_mul, eval₂_mul, eval₂_pow, eval₂_sub, eval₂_X,
        eval₂_C, eval₂_C, eval₂_C, hT₁]
    linear_combination -hab + hH - he₀ - T₁ * he₁
  have hrel' : w 2 * w 2 = w 0 * ((e₀ + e₁ * T₁ + a) * w 0 + (T.eval₂ g Y₂ * T₁) * w 1 +
      b * w 2) := by
    simp only [hw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [hrel, hGexp]; ring
  obtain ⟨-, μ, hμ₀, hμ₂⟩ := exists_add_mul_sq_mem_of_not_isCaseOne hII w hwspan
    ![e₀ + e₁ * T₁ + a, T.eval₂ g Y₂ * T₁, b]
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]; exact hrel')
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hμ₀ hμ₂
  set F := (e₀ + e₁ * T₁ + a + μ * μ) * W + T.eval₂ g Y₂ * T₁ * T₁ + (b + 2 * μ) * Y₃ with hF
  have hsq : (Y₃ + μ * W) * (Y₃ + μ * W) = W * F := by
    rw [hF]; linear_combination hrel + W * hGexp
  have hspan' : Ideal.span (Set.range ![W, T₁, Y₃ + μ * W]) = maximalIdeal B := by
    rw [span_range_fin_three, hspan]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
      · exact Ideal.add_mem _ (Ideal.subset_span (by simp))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
      · have : z = (z + μ * W) - μ * W := by ring
        rw [this]
        exact Ideal.sub_mem _ (Ideal.subset_span (by simp))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  have hFrest : F - T.eval₂ g Y₂ * (T₁ * T₁) ∈
      Ideal.span {W, Y₃ + μ * W} * maximalIdeal B := by
    have heq : F - T.eval₂ g Y₂ * (T₁ * T₁) =
        W * ((e₀ + e₁ * T₁ + a + μ * μ) - μ * (b + 2 * μ)) + (Y₃ + μ * W) * (b + 2 * μ) := by
      rw [hF]; ring
    rw [heq, Ideal.span_insert, Ideal.sup_mul]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · exact Ideal.mul_mem_mul (Ideal.subset_span rfl)
        (Ideal.sub_mem _ hμ₀ (Ideal.mul_mem_left _ _ hμ₂))
    · exact Ideal.mul_mem_mul (Ideal.subset_span rfl) hμ₂
  refine ⟨μ, ⟨hspan', F, ?_, by simpa using hsq⟩, fun hu => ⟨hspan', F, _, hu, ?_, by simpa using
      hsq⟩⟩
  · have h1 : F - T.eval₂ g Y₂ * (T₁ * T₁) ∈ maximalIdeal B ^ 2 := by
      have hle : Ideal.span {W, Y₃ + μ * W} ≤ maximalIdeal B := by
        rw [Ideal.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hmem 0
        · exact hspan' ▸ Ideal.subset_span ⟨2, rfl⟩
      have := Ideal.mul_mono_left hle hFrest
      rwa [← pow_two] at this
    have h2 : T.eval₂ g Y₂ * (T₁ * T₁) ∈ maximalIdeal B ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hTm hTm)
    have := Ideal.add_mem _ h1 h2
    rwa [sub_add_cancel] at this
  · simpa using hFrest

omit [IsLocalRing B] in
/-- A polynomial whose coefficients lie in `𝔪_A`, evaluated along `g`, lies in `(W)` when
`g(𝔪_A) ⊆ (W)`. -/
theorem eval₂_mem_span_of_map_eq_zero {A : Type*} [CommRing A] [IsLocalRing A] (g : A →+* B)
    (W Y : B) (hdiv : ∀ r ∈ maximalIdeal A, g r ∈ Ideal.span {W}) {P : A[X]}
    (hP : P.map (residue A) = 0) : P.eval₂ g Y ∈ Ideal.span {W} :=
  eval₂_mem_span_of_map_eq_zero_aux g W Y hdiv hP

/-- **The singular case II point of the exceptional line is `κ`-rational, in the local ring.**
Let `B` be a normal singular two-dimensional Noetherian local ring in case II, `g : A → B` with
`g(𝔪_A) ⊆ (W)`, and `𝔪_B = (W, Π(Y₂), Y₃)` where `Π` lifts an irreducible `π ∈ κ[X]` and
`P(Y₂) ∈ 𝔪_B ⟺ π ∣ P̄`. If `Y₃² = WG` with `G ≡ H(Y₂)` modulo `(W, Y₃)` and `deg H̄ ≤ 3`, then
`π = X - c̄` up to a unit and `(X - c̄)² ∣ H̄`.

`H̄ ≠ 0` because otherwise `Y₃/W` is integral over `B` and `B` is regular (the source: "`h` must
be nonzero in the residue field of `ξ`"); `π ∣ H̄` because `B` is singular; `π² ∣ H̄` because `B`
is in case II (the source's footnote: otherwise the quadratic form at `p` is
`y₃² - x₁(… + (unit)g)`, never a square); and then `π` is linear as `deg H̄ ≤ 3`. -/
theorem exists_rationalPoint_of_line {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (hdim : ringKrullDim B = 2)
    (hsing : ¬ IsRegularLocalRing B) (hII : ¬ IsCaseOne B) (g : A →+* B) (W Y₂ Y₃ G : B)
    (H Pl : A[X]) (π : (ResidueField A)[X]) (hπ : Irreducible π)
    (hPl : Pl.map (residue A) = π) (hdiv : ∀ r ∈ maximalIdeal A, g r ∈ Ideal.span {W})
    (hspan : maximalIdeal B = Ideal.span {W, Pl.eval₂ g Y₂, Y₃})
    (hmemπ : ∀ P : A[X], P.eval₂ g Y₂ ∈ maximalIdeal B ↔ π ∣ P.map (residue A))
    (hrel : Y₃ * Y₃ = W * G) (hG : G - H.eval₂ g Y₂ ∈ Ideal.span {W, Y₃})
    (hdeg : (H.map (residue A)).natDegree ≤ 3) :
    ∃ c : A, (∀ P : A[X], π ∣ P.map (residue A) ↔
        (Polynomial.X - Polynomial.C (residue A c)) ∣ P.map (residue A)) ∧
      H.map (residue A) ≠ 0 ∧
      (Polynomial.X - Polynomial.C (residue A c)) ^ 2 ∣ H.map (residue A) := by
  set w : Fin 3 → B := ![W, Pl.eval₂ g Y₂, Y₃] with hw
  have hwspan : Ideal.span (Set.range w) = maximalIdeal B := by
    rw [span_range_fin_three, hspan]; rfl
  have hmem : ∀ i, w i ∈ maximalIdeal B := fun i => hwspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hGm : G ∈ maximalIdeal B := mem_maximalIdeal_of_sq_eq_mul hdim hsing w hwspan hrel
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hG
  have hHm : H.eval₂ g Y₂ ∈ maximalIdeal B := by
    have : H.eval₂ g Y₂ = G - (a * W + b * Y₃) := by rw [hab]; ring
    rw [this]
    exact Ideal.sub_mem _ hGm (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hmem 0))
      (Ideal.mul_mem_left _ _ (hmem 2)))
  have hH0 : H.map (residue A) ≠ 0 := by
    intro h0
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (eval₂_mem_span_of_map_eq_zero g W Y₂ hdiv h0)
    have hY : Y₃ ∈ Ideal.span {W} := mem_span_singleton_of_sq_eq_mul (α := e + a) (β := b)
      (by rw [hrel, ← sub_add_cancel G (H.eval₂ g Y₂), ← hab, ← he]; ring)
    refine hsing (isRegularLocalRing_of_maximalIdeal_eq_span_pair hdim (u := W)
      (v := Pl.eval₂ g Y₂) (le_antisymm ?_ ?_))
    · rw [hspan, Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
      · exact Ideal.span_mono (by simp) hY
    · rw [Ideal.span_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨hmem 0, hmem 1⟩
  obtain ⟨ψ, hψ⟩ := (hmemπ H).mp hHm
  obtain ⟨Ψ, rfl⟩ := map_surjective (residue A) residue_surjective ψ
  have hdiff : (H - Pl * Ψ).map (residue A) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hPl, ← hψ, sub_self]
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (eval₂_mem_span_of_map_eq_zero g W Y₂ hdiv hdiff)
  have hrel' : w 2 * w 2 = w 0 * ((e + a) * w 0 + Ψ.eval₂ g Y₂ * w 1 + b * w 2) := by
    simp only [hw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [hrel]
    have h1 : G = H.eval₂ g Y₂ + (a * W + b * Y₃) := by rw [hab]; ring
    have h2 : H.eval₂ g Y₂ = (H - Pl * Ψ).eval₂ g Y₂ + Pl.eval₂ g Y₂ * Ψ.eval₂ g Y₂ := by
      rw [eval₂_sub, eval₂_mul]; ring
    rw [h1, h2, ← he]; ring
  obtain ⟨hΨ, -⟩ := exists_add_mul_sq_mem_of_not_isCaseOne hII w hwspan
    ![e + a, Ψ.eval₂ g Y₂, b]
    (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]; exact hrel')
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hΨ
  have hπψ := (hmemπ Ψ).mp hΨ
  have hsq : π ^ 2 ∣ H.map (residue A) := by
    rw [hψ, pow_two]
    exact mul_dvd_mul_left π hπψ
  obtain ⟨c', hc'⟩ := exists_dvd_iff_X_sub_C_dvd hπ hH0 hdeg hsq
  obtain ⟨c, rfl⟩ := residue_surjective c'
  refine ⟨c, fun P => hc' (P.map (residue A)), hH0, ?_⟩
  have hXπ : (Polynomial.X - Polynomial.C (residue A c)) ∣ π := (hc' π).mp dvd_rfl
  exact (pow_dvd_pow_of_dvd hXπ 2).trans hsq

/-! ### The case II analysis on the first chart -/

section ChartTwo

variable {A : Type u} [CommRing A] [IsLocalRing A] {x : Fin 3 → A}
  (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away (x 0) S]

/-- **Stacks 0BGE, case II on the first chart.** Let `x₁, x₂, x₃` generate `𝔪`, and on
`A' = A[𝔪/x₁]` let `y₃² = x₁G` with `G ≡ H(y₂)` modulo `(x₁, y₃)`, `deg H̄ ≤ 3`. Let `𝔪'` be a
maximal ideal containing `𝔪A'` at which `B = A'_{𝔪'}` is a normal singular two-dimensional
Noetherian local ring in case II. Then the point is `κ`-rational, `𝔪B = x₁B`, and there are
`c ∈ A`, a Taylor expansion `H = c₀ + d₀(X - c) + (X - c)²T` and `μ ∈ B` such that
`x₁, y₂ - c, y₃ + μx₁` satisfy the exact case II invariant
`AlgebraicGeometry.HasDoubleLineRelation`, and the nondegenerate one
`AlgebraicGeometry.HasDoubleLineRelationUnit` when `T(y₂)` is a unit.

This is the source's analysis of case II ("`p` must correspond to a zero of `h` … at most one
singular point `p ∈ C` falling into case II which is moreover `κ`-rational … we may assume this is
the point `y₂ = y₃ = 0`"), with the exact invariant in place of the source's "subclass". -/
theorem exists_hasDoubleLineRelation_of_chart (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (G : affineBlowupAlgebra (maximalIdeal A) (x 0) S)
    (hrel : chartFraction S hx 2 * chartFraction S hx 2 = algebraMap A _ (x 0) * G)
    (H : A[X]) (hdeg : (H.map (residue A)).natDegree ≤ 3)
    (hGH : G - aeval (chartFraction S hx 1) H ∈
      Ideal.span {algebraMap A _ (x 0), chartFraction S hx 2})
    (M : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) [hM : M.IsMaximal]
    (hle : Ideal.map (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S))
      (maximalIdeal A) ≤ M)
    [IsNoetherianRing (Localization.AtPrime M)] [IsDomain (Localization.AtPrime M)]
    [IsIntegrallyClosed (Localization.AtPrime M)]
    (hdim : ringKrullDim (Localization.AtPrime M) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime M))
    (hII : ¬ IsCaseOne (Localization.AtPrime M)) :
    Function.Surjective ((Ideal.Quotient.mk M).comp
        (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S))) ∧
      ∃ (c : A) (T : A[X]), H.map (residue A) ≠ 0 ∧
        (Polynomial.X - Polynomial.C (residue A c)) ^ 2 ∣ H.map (residue A) ∧
        (∃ c₀ d₀ : A, H = Polynomial.C c₀ +
          Polynomial.C d₀ * (Polynomial.X - Polynomial.C c) +
          (Polynomial.X - Polynomial.C c) ^ 2 * T) ∧
        ∃ μ : Localization.AtPrime M,
          HasDoubleLineRelation (Localization.AtPrime M)
            ![algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)),
              algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (chartFraction S hx 1 - algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0)
                  S) c),
              algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (chartFraction S hx 2) +
                μ * algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime
                    M) (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0))] ∧
          (IsUnit (T.eval₂ ((algebraMap _ (Localization.AtPrime M)).comp
              (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S)))
              (algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (chartFraction S hx 1))) →
            HasDoubleLineRelationUnit (Localization.AtPrime M)
              ![algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)),
                algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                    (chartFraction S hx 1 - algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x
                    0) S) c),
                algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                    (chartFraction S hx 2) +
                  μ * algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S)
                      (Localization.AtPrime M) (algebraMap A (affineBlowupAlgebra (maximalIdeal A)
                      (x 0) S) (x 0))]) := by
  classical
  set φ := algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
    with hφ
  set g := φ.comp (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) with hg
  have hx0 : algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0) ∈ M :=
    hle (Ideal.mem_map_of_mem _ (hx 0))
  have hy2 : chartFraction S hx 2 ∈ M := mem_of_mul_self_eq_mul hrel hx0
  obtain ⟨π, hπ, hmemπ, Pl, hPl, hMeq⟩ :=
    exists_irreducible_of_chartFraction_mem S hx hspan M hle hy2
  have heval : ∀ P : A[X], φ (aeval (chartFraction S hx 1) P) =
      P.eval₂ g (φ (chartFraction S hx 1)) := fun P => by
    rw [aeval_def, hom_eval₂]
  have hmemB : ∀ z, φ z ∈ maximalIdeal (Localization.AtPrime M) ↔ z ∈ M := fun z =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff _ M z
  have hdiv : ∀ r ∈ maximalIdeal A, g r ∈ Ideal.span {g (x 0)} := by
    intro r hr
    have h := Ideal.mem_map_of_mem φ (algebraMap_mem_span_of_mem_maximalIdeal S hx hr)
    rwa [Ideal.map_span, Set.image_singleton] at h
  have hmaxB : ∀ {J : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)}, M = J →
      maximalIdeal (Localization.AtPrime M) = J.map φ := fun hJ => by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, congrArg (Ideal.map φ) hJ]
  have hspanB : maximalIdeal (Localization.AtPrime M) =
      Ideal.span {g (x 0), Pl.eval₂ g (φ (chartFraction S hx 1)), φ (chartFraction S hx 2)} := by
    rw [hmaxB hMeq, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton, heval, Set.pair_comm]
    rfl
  have hrelB : φ (chartFraction S hx 2) * φ (chartFraction S hx 2) = g (x 0) * φ G := by
    rw [← map_mul, hrel, map_mul]; rfl
  have hGB : φ G - H.eval₂ g (φ (chartFraction S hx 1)) ∈
      Ideal.span {g (x 0), φ (chartFraction S hx 2)} := by
    have h := Ideal.mem_map_of_mem φ hGH
    rwa [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_sub, heval] at h
  obtain ⟨c, hcπ, hH0, hcsq⟩ := exists_rationalPoint_of_line hdim hsing hII g (g (x 0))
    (φ (chartFraction S hx 1)) (φ (chartFraction S hx 2)) (φ G) H Pl π hπ hPl hdiv hspanB
    (fun P => by rw [← heval, hmemB, hmemπ]) hrelB hGB hdeg
  -- the point is `(x₁, y₂ - c, y₃)`
  have hyc : chartFraction S hx 1 - algebraMap A _ c ∈ M := by
    have h := (hmemπ (Polynomial.X - Polynomial.C c)).mpr ((hcπ _).mpr (by simp))
    simpa using h
  have hMeq' := eq_span_chartFraction_sub_of_le S hx hspan M c 0 <| Ideal.span_le.mpr <| by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨hx0, hyc, by simpa using hy2⟩
  refine ⟨surjective_quotient_comp_algebraMap S hx hspan M c 0 hMeq', ?_⟩
  obtain ⟨c₀, d₀, T, hT⟩ := exists_eq_taylor_two H c
  have hTk : H.map (residue A) = Polynomial.C (residue A c₀) +
      Polynomial.C (residue A d₀) * (Polynomial.X - Polynomial.C (residue A c)) +
      (Polynomial.X - Polynomial.C (residue A c)) ^ 2 * T.map (residue A) := by
    rw [hT]; simp
  obtain ⟨hc₀, hd₀⟩ := eq_zero_of_sq_dvd_taylor hTk hcsq
  have hspanB' : maximalIdeal (Localization.AtPrime M) =
      Ideal.span {g (x 0), φ (chartFraction S hx 1) - g c, φ (chartFraction S hx 2)} := by
    rw [hmaxB hMeq', Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton]
    simp only [map_sub, map_zero, sub_zero]
    rfl
  obtain ⟨μ, h1, h2⟩ := hasDoubleLineRelation_of_taylor hII g (g (x 0))
    (φ (chartFraction S hx 1)) (φ (chartFraction S hx 2)) (φ G) hdiv c c₀ d₀ H T
    ((residue_eq_zero_iff _).mp hc₀) ((residue_eq_zero_iff _).mp hd₀) hT hspanB' hrelB hGB
  refine ⟨c, T, hH0, hcsq, ⟨c₀, d₀, hT⟩, μ, ?_, fun hu => ?_⟩
  · rwa [map_sub]
  · rw [map_sub]; exact h2 hu

/-! ### The chart relation of case II -/

/-- The point `(1, y₂, 0)` of the line `y₃ = 0` of the chart, as polynomials in `y₂`. -/
noncomputable def lineCoords (R : Type*) [CommRing R] : Fin 3 → R[X] :=
  ![1, Polynomial.X, 0]

/-- The coordinates `(1, y₂, 0)` are polynomials of degree at most one. -/
theorem natDegree_lineCoords_le {R : Type*} [CommRing R] (i : Fin 3) :
    (lineCoords R i).natDegree ≤ 1 := by
  fin_cases i <;> simp [lineCoords, natDegree_X_le]

/-- If `uᵢ ≡ vᵢ` modulo `I` for every `i`, then `uₚu_qu_r ≡ vₚv_qv_r` modulo `I`. -/
theorem sub_mem_span_of_forall_sub_mem {R : Type*} [CommRing R] (I : Ideal R) (u v : Fin 3 → R)
    (h : ∀ i, u i - v i ∈ I) (p q r : Fin 3) :
    u p * u q * u r - v p * v q * v r ∈ I := by
  have heq : u p * u q * u r - v p * v q * v r =
      (u p - v p) * u q * u r + v p * (u q - v q) * u r + v p * v q * (u r - v r) := by ring
  rw [heq]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (h p)))
    (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (h q)))) (Ideal.mul_mem_left _ _ (h r))

/-- The chart fractions agree with `(1, y₂, 0)` modulo `y₃`. -/
theorem chartFraction_sub_aeval_lineCoords_mem (hx : ∀ i, x i ∈ maximalIdeal A) (i : Fin 3) :
    chartFraction S hx i - aeval (chartFraction S hx 1) (lineCoords A i) ∈
      Ideal.span {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0),
        chartFraction S hx 2} := by
  fin_cases i
  · simp [lineCoords, chartFraction_zero]
  · simp [lineCoords]
  · simpa [lineCoords] using Ideal.subset_span (by simp)

/-- **The chart relation in case II.** If `x₃² = Σ bₚᵩᵣ xₚxᵩxᵣ`, then on `A[𝔪/x₁]`,
`y₃² = x₁ G` with `G = Σ bₚᵩᵣ yₚyᵩyᵣ ≡ h(y₂)` modulo `(x₁, y₃)`, `h = Σ bₚᵩᵣ ŷₚŷᵩŷᵣ` of degree at
most three (`ŷ = (1, y₂, 0)`): the source's `y₃² = x₁(Σ aᵢⱼₖ yᵢyⱼyₖ)` and its polynomial `h`. -/
theorem chart_sq_eq_mul_of_sq_eq_cubic (hx : ∀ i, x i ∈ maximalIdeal A)
    (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hrel : x 2 * x 2 = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) :
    chartFraction S hx 2 * chartFraction S hx 2 = algebraMap A _ (x 0) *
        ∑ p, ∑ q, ∑ r, algebraMap A _ (b p q r) *
          (chartFraction S hx p * chartFraction S hx q * chartFraction S hx r) ∧
      (∑ p, ∑ q, ∑ r, algebraMap A _ (b p q r) *
          (chartFraction S hx p * chartFraction S hx q * chartFraction S hx r)) -
        aeval (chartFraction S hx 1) (∑ p, ∑ q, ∑ r, Polynomial.C (b p q r) *
          (lineCoords A p * lineCoords A q * lineCoords A r)) ∈
        Ideal.span {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0),
          chartFraction S hx 2} ∧
      ((∑ p, ∑ q, ∑ r, Polynomial.C (b p q r) *
          (lineCoords A p * lineCoords A q * lineCoords A r)).map (residue A)).natDegree ≤ 3 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := affineBlowupAlgebra_chart_relation S hx (fun p q => if p = 2 ∧ q = 2 then 1 else 0)
      b (by simpa [Fin.sum_univ_three] using hrel)
    simpa [Fin.sum_univ_three] using h
  · simp only [map_sum, map_mul, aeval_C]
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun q _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun r _ => ?_
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (sub_mem_span_of_forall_sub_mem _ _ _
      (chartFraction_sub_aeval_lineCoords_mem S hx) p q r)
  · rw [Polynomial.map_sum]
    refine natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
    rw [Polynomial.map_sum]
    refine natDegree_sum_le_of_forall_le _ _ fun q _ => ?_
    rw [Polynomial.map_sum]
    refine natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_map_le).trans ?_
    refine (natDegree_mul_le).trans ?_
    have h1 := natDegree_lineCoords_le (R := A) p
    have h2 := natDegree_lineCoords_le (R := A) q
    have h3 := natDegree_lineCoords_le (R := A) r
    have := (natDegree_mul_le (p := lineCoords A p) (q := lineCoords A q))
    omega

/-- **The chart relation of the case II invariant.** If `x₃² = x₁ Σ fₚᵩ xₚxᵩ`, then on
`A[𝔪/x₁]`, `y₃² = x₁ G` with `G = Σ fₚᵩ yₚyᵩ ≡ f₁₁ + (f₁₂ + f₂₁)y₂ + f₂₂y₂²` modulo `(x₁, y₃)`. -/
theorem chart_sq_eq_mul_of_sq_eq_mul (hx : ∀ i, x i ∈ maximalIdeal A)
    (f : Fin 3 → Fin 3 → A) (hrel : x 2 * x 2 = x 0 * ∑ p, ∑ q, f p q * (x p * x q)) :
    chartFraction S hx 2 * chartFraction S hx 2 = algebraMap A _ (x 0) *
        ∑ p, ∑ q, algebraMap A _ (f p q) * (chartFraction S hx p * chartFraction S hx q) ∧
      (∑ p, ∑ q, algebraMap A _ (f p q) * (chartFraction S hx p * chartFraction S hx q)) -
        aeval (chartFraction S hx 1) (Polynomial.C (f 1 1) * Polynomial.X ^ 2 +
          Polynomial.C (f 0 1 + f 1 0) * Polynomial.X + Polynomial.C (f 0 0)) ∈
        Ideal.span {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0),
          chartFraction S hx 2} := by
  classical
  have hcub := chart_sq_eq_mul_of_sq_eq_cubic S hx (fun p q r => if p = 0 then f q r else 0)
    (by rw [hrel]; simp [Fin.sum_univ_three]; ring)
  refine ⟨?_, ?_⟩
  · rw [hcub.1]
    congr 1
    simp [Fin.sum_univ_three, chartFraction_zero]
  · have hmem := hcub.2.1
    have h1 : (∑ p, ∑ q, ∑ r, algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S)
        ((fun p q r => if p = 0 then f q r else 0) p q r) *
          (chartFraction S hx p * chartFraction S hx q * chartFraction S hx r)) =
        ∑ p, ∑ q, algebraMap A _ (f p q) * (chartFraction S hx p * chartFraction S hx q) := by
      simp [Fin.sum_univ_three, chartFraction_zero]
    have h2 : (∑ p, ∑ q, ∑ r, Polynomial.C ((fun p q r => if p = 0 then f q r else 0) p q r) *
        (lineCoords A p * lineCoords A q * lineCoords A r)) =
        Polynomial.C (f 1 1) * Polynomial.X ^ 2 + Polynomial.C (f 0 1 + f 1 0) * Polynomial.X +
          Polynomial.C (f 0 0) := by
      simp [Fin.sum_univ_three, lineCoords]
      ring
    rwa [h1, h2] at hmem

/-- In a second-order Taylor expansion of a quadratic polynomial the remainder is the leading
coefficient. -/
theorem taylor_two_eq_C_of_quadratic {R : Type*} [CommRing R] [Nontrivial R]
    {a e d c c₀ d₀ : R} {T : R[X]}
    (h : Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C d =
      Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c) +
        (Polynomial.X - Polynomial.C c) ^ 2 * T) :
    T = Polynomial.C a := by
  have hmonic : ((Polynomial.X - Polynomial.C c) ^ 2 : R[X]).Monic := (monic_X_sub_C c).pow 2
  have hQ : (Polynomial.X - Polynomial.C c) ^ 2 * T =
      Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C d -
        (Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c)) := by
    rw [h]; ring
  have hT0 : T.natDegree = 0 := by
    by_contra hne
    have hTne : T ≠ 0 := fun h0 => hne (by rw [h0, natDegree_zero])
    have h1 := hmonic.natDegree_mul' hTne
    rw [hQ, (monic_X_sub_C c).natDegree_pow, natDegree_X_sub_C] at h1
    have h2 : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X +
        Polynomial.C d - (Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c))
          : R[X]).natDegree ≤ 2 := by
      have : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X +
          Polynomial.C d - (Polynomial.C c₀ + Polynomial.C d₀ * (Polynomial.X - Polynomial.C c))
            : R[X]) = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (e - d₀) * Polynomial.X +
              Polynomial.C (d - c₀ + d₀ * c) := by
        simp only [map_sub, map_add, map_mul]; ring
      rw [this]
      exact natDegree_quadratic_le
    omega
  rw [eq_C_of_natDegree_eq_zero hT0] at h ⊢
  congr 1
  have := congrArg (fun P => Polynomial.coeff P 2) h
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] at this
  have hsq : ((Polynomial.X - Polynomial.C c) ^ 2 * Polynomial.C (T.coeff 0) : R[X]) =
      Polynomial.C (T.coeff 0) * Polynomial.X ^ 2 - Polynomial.C (2 * c * T.coeff 0) *
        Polynomial.X + Polynomial.C (c ^ 2 * T.coeff 0) := by
    simp only [map_mul, map_pow, map_ofNat]; ring
  rw [hsq] at this
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] at this
  norm_num at this
  exact this.symm

/-- **The chart of a square in the cube of the maximal ideal has no point over `𝔪`.** If
`b ∈ 𝔪` and `b² ∈ 𝔪³`, then `b` is a unit of `A[𝔪/b]`: the chart `x₃` of the source in case II,
"Computing the affine blowup algebras … the reader easily sees that `p` cannot be contained in
the corresponding opens". -/
theorem false_of_mul_self_mem_pow_three {b : A} (hb : b ∈ maximalIdeal A)
    (hsq : b * b ∈ maximalIdeal A ^ 3) (T : Type u) [CommRing T] [Algebra A T]
    [IsLocalization.Away b T] (M : Ideal (affineBlowupAlgebra (maximalIdeal A) b T))
    [hM : M.IsMaximal]
    (hle : Ideal.map (algebraMap A (affineBlowupAlgebra (maximalIdeal A) b T))
      (maximalIdeal A) ≤ M) : False := by
  have h := Ideal.mem_map_of_mem (algebraMap A (affineBlowupAlgebra (maximalIdeal A) b T)) hsq
  rw [Ideal.map_pow, affineBlowupAlgebra.map_ideal_eq_span_singleton (maximalIdeal A) b hb,
    Ideal.span_singleton_pow] at h
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h
  have hreg := (Stacks.Blowup.isRegular_algebraMap_affineBlowupAlgebra (maximalIdeal A) b T).left
  have h1 : algebraMap A (affineBlowupAlgebra (maximalIdeal A) b T) b * t = 1 := by
    refine hreg (hreg ?_)
    change _ * (_ * (_ * t)) = _ * (_ * 1)
    rw [mul_one, ← map_mul, ← ht]
    ring
  refine hM.ne_top ((Ideal.eq_top_iff_one M).mpr ?_)
  rw [← h1]
  exact Ideal.mul_mem_right _ _ (hle (Ideal.mem_map_of_mem _ hb))

/-- **Stacks 0BGE, case II: the singular case II point of the first chart, in the normal form
`x₃² = Σ bₚᵩᵣ xₚxᵩxᵣ`.** It is `κ`-rational and, for suitable `c, μ`, the generators
`x₁, y₂ - c, y₃ + μx₁` satisfy the exact case II invariant
`AlgebraicGeometry.HasDoubleLineRelation` (the source's "Resolution in case II", with
`h = Σ āᵢⱼₖ ŷᵢŷⱼŷₖ` of degree at most three). -/
theorem hasDoubleLineRelation_of_sq_eq_cubic_chart (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (M : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) [hM : M.IsMaximal]
    (hle : Ideal.map (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) (maximalIdeal A)
        ≤ M)
    [IsNoetherianRing (Localization.AtPrime M)] [IsDomain (Localization.AtPrime M)]
        [IsIntegrallyClosed (Localization.AtPrime M)]
    (hdim : ringKrullDim (Localization.AtPrime M) = 2) (hsing : ¬ IsRegularLocalRing
        (Localization.AtPrime M))
    (hII : ¬ IsCaseOne (Localization.AtPrime M))
    (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hrel : x 2 * x 2 = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) :
    Function.Surjective ((Ideal.Quotient.mk M).comp (algebraMap A (affineBlowupAlgebra
        (maximalIdeal A) (x 0) S))) ∧
      ∃ (c : A) (μ : (Localization.AtPrime M)), HasDoubleLineRelation (Localization.AtPrime M)
            ![algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)),
              algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (chartFraction S hx 1 - algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0)
                  S) c),
              algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (chartFraction S hx 2) +
                μ * algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime
                    M) (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0))] := by
  obtain ⟨h1, h2, h3⟩ := chart_sq_eq_mul_of_sq_eq_cubic S hx b hrel
  obtain ⟨hsurj, c, T, -, -, -, μ, hμ, -⟩ := exists_hasDoubleLineRelation_of_chart S hx hspan _ h1
      _ h3 h2
    M hle hdim hsing hII
  exact ⟨hsurj, c, μ, hμ⟩

/-- **Stacks 0BGE, case II: the singular case II point of the first chart, for the exact
invariant `x₃² = x₁ Σ fₚᵩ xₚxᵩ`.** It is `κ`-rational and, for suitable `c, μ`, the generators
`x₁, y₂ - c, y₃ + μx₁` satisfy the nondegenerate invariant
`AlgebraicGeometry.HasDoubleLineRelationUnit`, with the same first generator `x₁`: the restricted
polynomial `h = f₁₁ + (f₁₂ + f₂₁)y₂ + f₂₂y₂²` is nonzero with a double root, so `f̄₂₂ ≠ 0`. -/
theorem hasDoubleLineRelation_of_sq_eq_mul_chart (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (M : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) [hM : M.IsMaximal]
    (hle : Ideal.map (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) (maximalIdeal A)
        ≤ M)
    [IsNoetherianRing (Localization.AtPrime M)] [IsDomain (Localization.AtPrime M)]
        [IsIntegrallyClosed (Localization.AtPrime M)]
    (hdim : ringKrullDim (Localization.AtPrime M) = 2) (hsing : ¬ IsRegularLocalRing
        (Localization.AtPrime M))
    (hII : ¬ IsCaseOne (Localization.AtPrime M))
    (f : Fin 3 → Fin 3 → A) (hrel : x 2 * x 2 = x 0 * ∑ p, ∑ q, f p q * (x p * x q)) :
    Function.Surjective ((Ideal.Quotient.mk M).comp (algebraMap A (affineBlowupAlgebra
        (maximalIdeal A) (x 0) S))) ∧
      ∃ (c : A) (μ : (Localization.AtPrime M)), HasDoubleLineRelationUnit (Localization.AtPrime M)
            ![algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)),
              algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (chartFraction S hx 1 - algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0)
                  S) c),
              algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
                  (chartFraction S hx 2) +
                μ * algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime
                    M) (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0))] := by
  obtain ⟨h1, h2⟩ := chart_sq_eq_mul_of_sq_eq_mul S hx f hrel
  have hdeg : ((Polynomial.C (f 1 1) * Polynomial.X ^ 2 + Polynomial.C (f 0 1 + f 1 0) *
      Polynomial.X + Polynomial.C (f 0 0)).map (residue A)).natDegree ≤ 3 := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    exact natDegree_quadratic_le.trans (by norm_num)
  obtain ⟨hsurj, c, T, hH0, hdvd, ⟨c₀, d₀, hT⟩, μ, -, hμu⟩ :=
    exists_hasDoubleLineRelation_of_chart S hx hspan _ h1 _ hdeg h2 M hle hdim hsing hII
  refine ⟨hsurj, c, μ, hμu ?_⟩
  rw [taylor_two_eq_C_of_quadratic hT, eval₂_C]
  refine IsUnit.map _ (notMem_maximalIdeal.mp fun hf => hH0 ?_)
  refine Polynomial.eq_zero_of_dvd_of_degree_lt hdvd ?_
  rw [degree_pow, degree_X_sub_C]
  have hf' : residue A (f 1 1) = 0 := (residue_eq_zero_iff _).mpr hf
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, hf', map_zero, zero_mul, zero_add]
  refine (degree_add_le _ _).trans_lt (max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num))
    ((degree_C_le).trans_lt (by norm_num)))

/-- **Stacks 0BGE, case II: the point `P*` of the second chart.** Write the case II invariant of
`w₁, w₂, w₃` with the generators reordered as `x₁ = w₂, x₂ = w₁, x₃ = w₃`, so that it reads
`x₃² = x₂ Σ fₚᵩ xₚxᵩ` (`f₁₁` is the coefficient of `w₂²`). On `A[𝔪/x₁]`, a maximal ideal
`𝔪' ⊇ 𝔪A'` containing `y₂ = w₁/w₂` is the point `P* = (x₁, y₂, y₃)`, which is `κ`-rational; if the
local ring there is in case II, then `f₁₁ ∈ 𝔪` (otherwise the quadratic form at `P*` is
`t₃² - f̄₁₁t₁t₂`, which is not a square), and the generators `y₂, x₁, y₃` satisfy the case II
invariant again, `y₃² = y₂ · (x₁G')`, with the element `x₁ = w₂` in the middle position. -/
theorem hasDoubleLineRelation_of_sq_eq_mul_secondChart (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (f : Fin 3 → Fin 3 → A) (hrel : x 2 * x 2 = x 1 * ∑ p, ∑ q, f p q * (x p * x q))
    (M : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) [hM : M.IsMaximal]
    (hle : Ideal.map (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) (maximalIdeal A)
        ≤ M)
    (hII : ¬ IsCaseOne (Localization.AtPrime M)) (hz : chartFraction S hx 1 ∈ M) :
    f 0 0 ∈ maximalIdeal A ∧
      Function.Surjective ((Ideal.Quotient.mk M).comp (algebraMap A (affineBlowupAlgebra
          (maximalIdeal A) (x 0) S))) ∧
      HasDoubleLineRelation (Localization.AtPrime M)
        ![algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
            (chartFraction S hx 1),
          algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
              (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)),
          algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M)
              (chartFraction S hx 2)] := by
  classical
  set φ := algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (Localization.AtPrime M) with
      hφ
  have hcub := (chart_sq_eq_mul_of_sq_eq_cubic S hx (fun p q r => if p = 1 then f q r else 0)
    (by rw [hrel]; simp [Fin.sum_univ_three]; ring)).1
  set G := ∑ p, ∑ q, algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (f p q) *
      (chartFraction S hx p * chartFraction S hx q)
    with hG
  have hrel' : chartFraction S hx 2 * chartFraction S hx 2 =
      algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0) * (chartFraction S hx 1 *
          G) := by
    rw [hcub, hG]
    congr 1
    simp [Fin.sum_univ_three, chartFraction_zero]
    ring
  have hx0 : algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0) ∈ M := hle
      (Ideal.mem_map_of_mem _ (hx 0))
  have hy2 : chartFraction S hx 2 ∈ M := mem_of_mul_self_eq_mul hrel' hx0
  have hMeq := eq_span_chartFraction_sub_of_le S hx hspan M 0 0 <| Ideal.span_le.mpr <| by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨hx0, by simpa using hz, by simpa using hy2⟩
  have hsurj := surjective_quotient_comp_algebraMap S hx hspan M 0 0 hMeq
  simp only [map_zero, sub_zero] at hMeq
  have hGf : G - algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (f 0 0) ∈ M := by
    have heq : G - algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (f 0 0) =
        chartFraction S hx 1 *
        (algebraMap A _ (f 0 1) + algebraMap A _ (f 1 0) + algebraMap A _ (f 1 1) *
          chartFraction S hx 1 + algebraMap A _ (f 1 2) * chartFraction S hx 2 +
          algebraMap A _ (f 2 1) * chartFraction S hx 2) + chartFraction S hx 2 *
        (algebraMap A _ (f 0 2) + algebraMap A _ (f 2 0) + algebraMap A _ (f 2 2) *
          chartFraction S hx 2) := by
      rw [hG]; simp [Fin.sum_univ_three, chartFraction_zero]; ring
    rw [heq]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hz) (Ideal.mul_mem_right _ _ hy2)
  have hmB : maximalIdeal (Localization.AtPrime M) = Ideal.span {φ (algebraMap A
      (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)),
      φ (chartFraction S hx 1), φ (chartFraction S hx 2)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, congrArg (Ideal.map φ) hMeq, Ideal.map_span,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  have hmemB : ∀ z, φ z ∈ maximalIdeal (Localization.AtPrime M) ↔ z ∈ M := fun z =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff _ M z
  have hf00 : f 0 0 ∈ maximalIdeal A := by
    by_contra hf
    have hGu : φ G ∉ maximalIdeal (Localization.AtPrime M) := by
      intro hG'
      have h1 : algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (f 0 0) ∈ M := by
        have := M.sub_mem ((hmemB G).mp hG') hGf
        rwa [sub_sub_cancel] at this
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 ((notMem_maximalIdeal.mp hf).map _))
    refine hII ⟨![φ (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)), φ
        (chartFraction S hx 1), φ (chartFraction S hx 2)],
      ![![0, -φ G, 0], ![0, 0, 0], ![0, 0, 1]], ?_, ?_, ⟨2, 2, le_rfl, ?_⟩, ?_, ?_⟩
    · rw [span_range_fin_three, hmB]; rfl
    · intro p q hpq
      fin_cases p <;> fin_cases q <;> simp at hpq ⊢
    · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [notMem_maximalIdeal]; exact isUnit_one
    · have h0 : ∑ p, ∑ q, ![![0, -φ G, 0], ![0, 0, 0], ![(0 : (Localization.AtPrime M)), 0, 1]] p q
        *
          (![φ (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)), φ
              (chartFraction S hx 1), φ (chartFraction S hx 2)] p *
            ![φ (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)), φ
                (chartFraction S hx 1),
              φ (chartFraction S hx 2)] q) = 0 := by
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        have := congrArg φ hrel'
        simp only [map_mul] at this
        linear_combination this
      rw [h0]; exact zero_mem _
    · rintro ⟨k, l, hdiag, hoff⟩
      have h0 := hdiag 0
      have h01 := hoff 0 1 (by decide)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, map_neg, add_zero] at h0 h01
      have hk : k * l 0 * l 1 = 0 := by
        rcases mul_eq_zero.mp ((mul_assoc k (l 0) (l 0)).symm.trans h0.symm) with h | h
        · rw [h, zero_mul, zero_mul]
        · rw [mul_self_eq_zero.mp h, mul_zero, zero_mul]
      rw [hk, mul_zero, neg_eq_zero, residue_eq_zero_iff] at h01
      exact hGu h01
  refine ⟨hf00, hsurj, ?_, φ (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)) *
      φ G, ?_, ?_⟩
  · rw [span_range_fin_three, hmB]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [Set.insert_comm]
  · rw [pow_two]
    refine Ideal.mul_mem_mul ((hmemB _).mpr hx0) ((hmemB _).mpr ?_)
    simpa using M.add_mem hGf (hle (Ideal.mem_map_of_mem _ hf00))
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    have := congrArg φ hrel'
    simp only [map_mul] at this
    rw [this]; ring

end ChartTwo

end AlgebraicGeometry

end
