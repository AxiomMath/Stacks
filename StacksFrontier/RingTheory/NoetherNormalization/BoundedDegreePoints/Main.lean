module

public import StacksFrontier.RingTheory.NoetherNormalization.Basic
public import StacksFrontier.RingTheory.NoetherNormalization.BoundedDegreePoints.Spread
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Infinitely many points of bounded degree

Let `R` be an infinite Noetherian domain, `B` a finite type `R`-algebra and `k` an algebraically
closed field containing `R` such that `k ⊗_R B` has positive Krull dimension. Then there are
`0 ≠ f ∈ R`, `d ∈ ℕ` and infinitely many (pairwise distinct) `R`-algebra maps `ρₙ : B → k` such
that for every maximal ideal `𝔪` of `R` with `f ∉ 𝔪` each `ρₙ` factors as
`B → O → k` through a local domain `O` with `O → k` injective, maximal ideal over `𝔪` and
residue field of degree at most `d` over `R / 𝔪`.

The proof: with `K = Frac(R)`, the `K`-algebra `K ⊗_R B` is nonzero and admits a Noether
normalization `K[X₁, …, Xₙ] → K ⊗_R B` with `n ≥ 1` (otherwise `k ⊗_R B` would be integral
over `k`, of dimension `≤ 0`). Spread it out over `R[1/f]`
(`exists_pow_smul_mem_span_of_finite`), take `ρ_c` lying over the `K`-point `(c, …, c)` of
`K[X]` for `c ∈ R` (`exists_algHom_apply_eq_of_injective_of_isIntegral`), and apply
`exists_isLocalRing_finrank_residueField_le` to the image of `ρ_c`.

## Main results

* `exists_boundedDegree_points`: the statement above.
* `exists_span_points_of_infinite`: the points `ρₙ`, with `ρₙ(B)[1/f]` spanned over `R[1/f]` by
  the images of fixed `u₁, …, u_d ∈ B`, which is what the local domains are built from
  (`exists_isLocalRing_of_pow_smul_mem_span`).
-/

@[expose] public section

universe u

open MvPolynomial TensorProduct

/-- Every element of `Frac(R) ⊗_R B` lies in the image of `B` after multiplication by a
nonzero element of `R`. -/
theorem TensorProduct.exists_smul_mem_range_includeRight (R B : Type*) [CommRing R]
    [IsDomain R] [CommRing B] [Algebra R B] (t : FractionRing R ⊗[R] B) :
    ∃ s : R, s ≠ 0 ∧
      s • t ∈ (Algebra.TensorProduct.includeRight : B →ₐ[R] FractionRing R ⊗[R] B).range := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Subalgebra.zero_mem _⟩
  | tmul a b =>
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (nonZeroDivisors R) a
    refine ⟨t, nonZeroDivisors.ne_zero t.2, r • b, ?_⟩
    change (1 : FractionRing R) ⊗ₜ[R] (r • b) = (t : R) • (a ⊗ₜ[R] b)
    rw [TensorProduct.smul_tmul', _root_.Algebra.smul_def (t : R) a, mul_comm, ht,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨s₁, hs₁, h₁⟩ := hx
    obtain ⟨s₂, hs₂, h₂⟩ := hy
    refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
    rw [smul_add]
    refine Subalgebra.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Subalgebra.smul_mem _ h₁ _
    · rw [mul_smul]
      exact Subalgebra.smul_mem _ h₂ _

/-- If `Frac(R) ⊗_R B` is integral over `Frac(R)` and `k` is a field containing `R`, then
`k ⊗_R B` is integral over `k`, so its Krull dimension is at most `0`. -/
theorem ringKrullDim_tensorProduct_le_zero_of_isIntegral {R B k : Type*} [CommRing R]
    [IsDomain R] [CommRing B] [Algebra R B] [Field k] [Algebra R k]
    (hι : Function.Injective (algebraMap R k))
    [Algebra.IsIntegral (FractionRing R) (FractionRing R ⊗[R] B)] :
    ringKrullDim (k ⊗[R] B) ≤ 0 := by
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).mpr hι
  let := FractionRing.liftAlgebra R k
  let ι : FractionRing R →ₐ[R] k := IsScalarTower.toAlgHom R _ k
  let Φ : FractionRing R ⊗[R] B →ₐ[R] k ⊗[R] B := Algebra.TensorProduct.map ι (AlgHom.id R B)
  have hb : ∀ b : B, IsIntegral k ((1 : k) ⊗ₜ[R] b) := by
    intro b
    have h := IsIntegral.map_of_comp_eq (algebraMap (FractionRing R) k) Φ.toRingHom ?_
      (Algebra.IsIntegral.isIntegral (R := FractionRing R) ((1 : FractionRing R) ⊗ₜ[R] b))
    · simpa [Φ] using h
    · ext a
      simp [Φ, ι, Algebra.TensorProduct.algebraMap_apply]
  have : Algebra.IsIntegral k (k ⊗[R] B) := by
    refine ⟨fun x => ?_⟩
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul a b =>
      have h : a ⊗ₜ[R] b = algebraMap k (k ⊗[R] B) a * (1 ⊗ₜ b) := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [h]
      exact isIntegral_algebraMap.mul (hb b)
    | add x y hx hy => exact hx.add hy
  rcases subsingleton_or_nontrivial (k ⊗[R] B) with h | h
  · rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  · rw [← ringKrullDim_eq_of_injective_isIntegral (algebraMap k (k ⊗[R] B))
      (algebraMap k _).injective fun x => Algebra.IsIntegral.isIntegral x,
      ringKrullDim_eq_zero_of_field]

/-- Let `R` be an infinite domain, `B` a finite type `R`-algebra and `k` an algebraically
closed field with `R ⊆ k` such that `Frac(R) ⊗_R B` is not integral over `Frac(R)`. Then there
are `0 ≠ f ∈ R`, elements `u₁, …, u_d ∈ B` and an injective sequence `ρ` of `R`-algebra maps
`B → k` such that for every `n` the image `ρ n (B)[1/f]` is spanned over `R[1/f]` by the
`ρ n (u_i)`: every `b ∈ B` has `f ^ M • ρ n b ∈ span R {ρ n (u_i)}` for some `M`. -/
theorem exists_span_points_of_not_isIntegral {R B k : Type u} [CommRing R]
    [IsDomain R] [Infinite R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Field k] [IsAlgClosed k] [Algebra R k]
    (hι : Function.Injective (algebraMap R k))
    (hnot : ¬ Algebra.IsIntegral (FractionRing R) (FractionRing R ⊗[R] B)) :
    ∃ (f : R) (_ : f ≠ 0) (d : ℕ) (u : Fin d → B) (ρ : ℕ → (B →ₐ[R] k)), Function.Injective ρ ∧
      ∀ (n : ℕ) (b : B), ∃ M : ℕ, f ^ M • ρ n b ∈ Submodule.span R (Set.range (ρ n ∘ u)) := by
  let K := FractionRing R
  let T := K ⊗[R] B
  let j : B →ₐ[R] T := Algebra.TensorProduct.includeRight
  have hT : Nontrivial T := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Algebra.IsIntegral K T :=
      ⟨fun x => by rw [Subsingleton.elim x 0]; exact isIntegral_zero⟩
    exact hnot this
  obtain ⟨n, ψ, -, hψinj, hψfin⟩ := noether_normalization_global (k := K) (T := T)
  have hψint : ψ.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hψfin
  obtain ⟨n, rfl⟩ : ∃ n' : ℕ, n = n' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun hn => ?_
    subst hn
    have : Algebra.IsIntegral K T := by
      refine ⟨fun x => ?_⟩
      let : Algebra (MvPolynomial (Fin 0) K) T := ψ.toRingHom.toAlgebra
      have hx : IsIntegral (MvPolynomial (Fin 0) K) x := hψint x
      have h := IsIntegral.map_of_comp_eq (MvPolynomial.eval (Fin.elim0 : Fin 0 → K))
        (RingHom.id T) ?_ hx
      · exact h
      · refine RingHom.ext fun p => ?_
        obtain ⟨a, rfl⟩ := MvPolynomial.C_surjective (Fin 0) p
        change algebraMap K T (MvPolynomial.eval _ (C a)) = ψ (C a)
        rw [MvPolynomial.eval_C, ← MvPolynomial.algebraMap_eq, ψ.commutes]
    exact hnot this
  obtain ⟨f, hf, d, y, s, u, hys, hspan⟩ :=
    exists_pow_smul_mem_span_of_finite j (TensorProduct.exists_smul_mem_range_includeRight R B)
      ψ hψfin
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).mpr hι
  let := FractionRing.liftAlgebra R k
  have hpt : ∀ c : R, ∃ ρ' : T →ₐ[R] k, ∀ i, ρ' (j (y i)) = algebraMap R k c := by
    intro c
    obtain ⟨φ, hφ⟩ := exists_algHom_apply_eq_of_injective_of_isIntegral (k := k) ψ hψinj hψint
      (fun i => algebraMap R K c / algebraMap R K (s i))
    refine ⟨φ.restrictScalars R, fun i => ?_⟩
    have hsK : algebraMap R K (s i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (hys i).1
    rw [AlgHom.restrictScalars_apply, (hys i).2, φ.map_smul_of_tower, hφ i, Algebra.smul_def,
      IsScalarTower.algebraMap_apply R K k (s i), ← map_mul, mul_div_cancel₀ _ hsK,
      ← IsScalarTower.algebraMap_apply]
  choose ρ' hρ' using hpt
  let c := Infinite.natEmbedding R
  let ρ : ℕ → (B →ₐ[R] k) := fun m => (ρ' (c m)).comp j
  have hρinj : Function.Injective ρ := by
    intro m₁ m₂ h
    have h' := congrArg (fun φ : B →ₐ[R] k => φ (y 0)) h
    simp only [ρ, AlgHom.comp_apply, hρ'] at h'
    exact c.injective (hι h')
  refine ⟨f, hf, d, u, ρ, hρinj, fun m b => ?_⟩
  obtain ⟨M, hM⟩ := hspan b
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hM
  have hle : Algebra.adjoin R (Set.range (j ∘ y)) ≤ (⊥ : Subalgebra R k).comap (ρ' (c m)) :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨c m, (hρ' _ i).symm⟩)
  choose r hr using fun i => hle (q i).2
  refine ⟨M, (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨r, ?_⟩⟩
  have h1 := congrArg (ρ' (c m)) hq
  simp only [map_sum, map_smul, Subalgebra.smul_def, smul_eq_mul, map_mul] at h1
  simp only [Function.comp_apply, ρ, AlgHom.comp_apply]
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hri : algebraMap R k (r i) = ρ' (c m) (q i) := hr i
  rw [Algebra.smul_def, hri]
  rfl

/-- Let `ρ : B → k` be an `R`-algebra map to a field with `R → k` injective, and `u₁, …, u_d ∈ B`
with `f ^ M • ρ b ∈ span R {ρ (u_i)}` for every `b ∈ B` and some `M`. Then for every maximal
ideal `𝔪 ∌ f` of `R`, `ρ` factors as `B → O → k` through a local domain `O`, with `O → k`
injective, the maximal ideal of `O` lying over `𝔪`, and the residue field of `O` finite of degree
at most `d` over `R / 𝔪`. -/
theorem exists_isLocalRing_of_pow_smul_mem_span {R B k : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [Field k] [Algebra R k] (hι : Function.Injective (algebraMap R k))
    (ρ : B →ₐ[R] k) {f : R} {d : ℕ} (u : Fin d → B)
    (hu : ∀ b : B, ∃ M : ℕ, f ^ M • ρ b ∈ Submodule.span R (Set.range (ρ ∘ u)))
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hf𝔪 : f ∉ 𝔪) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsLocalRing O) (_ : IsDomain O) (_ : Algebra R O)
      (β : B →ₐ[R] O) (γ : O →ₐ[R] k), Function.Injective γ ∧ γ.comp β = ρ ∧
      (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = 𝔪 ∧
      ∃ (_ : Algebra (R ⧸ 𝔪) (IsLocalRing.ResidueField O)),
        IsScalarTower R (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
        Module.Finite (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
        Module.finrank (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ≤ d := by
  let A := B ⧸ RingHom.ker ρ
  let σ : A →ₐ[R] k := Ideal.kerLiftAlg ρ
  have he : ∀ a : A, ∃ M : ℕ,
      f ^ M • a ∈ Submodule.span R (Set.range (Ideal.Quotient.mkₐ R (RingHom.ker ρ) ∘ u)) := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨M, hM⟩ := hu b
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hM
    refine ⟨M, (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨r, ?_⟩⟩
    refine Ideal.kerLiftAlg_injective ρ ?_
    have h : ∀ x : A, σ x = Ideal.kerLiftAlg ρ x := fun _ => rfl
    rw [← h, ← h, map_sum, map_smul]
    simp only [map_smul, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, σ,
      Ideal.kerLiftAlg_mk] at hr ⊢
    exact hr
  obtain ⟨O, i₁, i₂, i₃, i₄, β, γ, hγ, hγβ, hmax, rest⟩ :=
    exists_isLocalRing_finrank_residueField_le σ (Ideal.kerLiftAlg_injective _) hι _ he 𝔪 hf𝔪
  refine ⟨O, i₁, i₂, i₃, i₄, β.comp (Ideal.Quotient.mkₐ R _), γ, hγ, ?_, hmax, rest⟩
  rw [← AlgHom.comp_assoc, hγβ]
  ext b
  exact Ideal.kerLiftAlg_mk ρ b

/-- Let `R` be an infinite domain, `B` a finite type `R`-algebra and `k` an algebraically
closed field with `R ⊆ k` such that `Frac(R) ⊗_R B` is not integral over `Frac(R)`. Then there
are `0 ≠ f ∈ R`, `d ∈ ℕ` and an injective sequence `ρ` of `R`-algebra maps `B → k` such that
for every `n` and every maximal ideal `𝔪 ∌ f` of `R`, `ρ n` factors as `B → O → k` through a
local domain `O`, with `O → k` injective, the maximal ideal of `O` lying over `𝔪`, and the
residue field of `O` finite of degree at most `d` over `R / 𝔪`. -/
theorem exists_boundedDegree_points_of_not_isIntegral {R B k : Type u} [CommRing R]
    [IsDomain R] [Infinite R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Field k] [IsAlgClosed k] [Algebra R k]
    (hι : Function.Injective (algebraMap R k))
    (hnot : ¬ Algebra.IsIntegral (FractionRing R) (FractionRing R ⊗[R] B)) :
    ∃ (f : R) (_ : f ≠ 0) (d : ℕ) (ρ : ℕ → (B →ₐ[R] k)), Function.Injective ρ ∧
      ∀ (n : ℕ) (𝔪 : Ideal R) [𝔪.IsMaximal], f ∉ 𝔪 →
        ∃ (O : Type u) (_ : CommRing O) (_ : IsLocalRing O) (_ : IsDomain O) (_ : Algebra R O)
          (β : B →ₐ[R] O) (γ : O →ₐ[R] k), Function.Injective γ ∧ γ.comp β = ρ n ∧
          (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = 𝔪 ∧
          ∃ (_ : Algebra (R ⧸ 𝔪) (IsLocalRing.ResidueField O)),
            IsScalarTower R (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
            Module.Finite (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
            Module.finrank (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ≤ d := by
  obtain ⟨f, hf, d, u, ρ, hρ, hu⟩ := exists_span_points_of_not_isIntegral hι hnot
  exact ⟨f, hf, d, ρ, hρ, fun n 𝔪 _ hf𝔪 =>
    exists_isLocalRing_of_pow_smul_mem_span hι (ρ n) u (hu n) 𝔪 hf𝔪⟩

/-- If `Frac(R) ⊗_R B` is integral over `Frac(R)`, `B` is of finite type over `R` and `k` is a
field containing `R`, then there are only finitely many `R`-algebra maps `B → k`: they
correspond to the `Frac(R)`-algebra maps from the finite-dimensional `Frac(R) ⊗_R B` to `k`. -/
theorem finite_algHom_of_isIntegral {R B k : Type*} [CommRing R] [IsDomain R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B] [Field k] [Algebra R k]
    (hι : Function.Injective (algebraMap R k))
    [Algebra.IsIntegral (FractionRing R) (FractionRing R ⊗[R] B)] :
    Finite (B →ₐ[R] k) := by
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).mpr hι
  let := FractionRing.liftAlgebra R k
  have : Module.Finite (FractionRing R) (FractionRing R ⊗[R] B) := Algebra.IsIntegral.finite
  refine Finite.of_surjective
    (fun φ : FractionRing R ⊗[R] B →ₐ[FractionRing R] k =>
      (φ.restrictScalars R).comp Algebra.TensorProduct.includeRight) fun g => ?_
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId _ k) g fun _ _ => Commute.all _ _, ?_⟩
  ext b
  simp

/-- Let `R` be an infinite Noetherian domain, `B` a finite type `R`-algebra and `k` an
algebraically closed field with `R ⊆ k` such that `dim (k ⊗_R B) > 0`. Then there are
`0 ≠ f ∈ R`, `d ∈ ℕ` and an injective sequence `ρ` of `R`-algebra maps `B → k` such that for
every `n` and every maximal ideal `𝔪 ∌ f` of `R`, `ρ n` factors as `B → O → k` through a local
domain `O`, with `O → k` injective, the maximal ideal of `O` lying over `𝔪`, and the residue
field of `O` finite of degree at most `d` over `R / 𝔪`. -/
theorem exists_boundedDegree_points {R B k : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Infinite R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Field k] [IsAlgClosed k] [Algebra R k]
    (hι : Function.Injective (algebraMap R k))
    (hdim : 0 < ringKrullDim (TensorProduct R k B)) :
    ∃ (f : R) (_ : f ≠ 0) (d : ℕ) (ρ : ℕ → (B →ₐ[R] k)), Function.Injective ρ ∧
      ∀ (n : ℕ) (𝔪 : Ideal R) [𝔪.IsMaximal], f ∉ 𝔪 →
        ∃ (O : Type u) (_ : CommRing O) (_ : IsLocalRing O) (_ : IsDomain O) (_ : Algebra R O)
          (β : B →ₐ[R] O) (γ : O →ₐ[R] k), Function.Injective γ ∧ γ.comp β = ρ n ∧
          (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = 𝔪 ∧
          ∃ (_ : Algebra (R ⧸ 𝔪) (IsLocalRing.ResidueField O)),
            IsScalarTower R (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
            Module.Finite (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
            Module.finrank (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ≤ d :=
  exists_boundedDegree_points_of_not_isIntegral hι fun _ => by
    exact (ringKrullDim_tensorProduct_le_zero_of_isIntegral (B := B) hι).not_gt hdim

/-- Let `R` be an infinite Noetherian domain, `B` a finite type `R`-algebra and `k` an
algebraically closed field with `R ⊆ k` such that there are infinitely many `R`-algebra maps
`B → k`. Then there are `0 ≠ f ∈ R`, `d ∈ ℕ` and an injective sequence `ρ` of `R`-algebra maps
`B → k` such that for every `n` and every maximal ideal `𝔪 ∌ f` of `R`, `ρ n` factors as
`B → O → k` through a local domain `O`, with `O → k` injective, the maximal ideal of `O` lying
over `𝔪`, and the residue field of `O` finite of degree at most `d` over `R / 𝔪`. -/
theorem exists_boundedDegree_points_of_infinite {R B k : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Infinite R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Field k] [IsAlgClosed k] [Algebra R k]
    (hι : Function.Injective (algebraMap R k))
    (hinf : Infinite (B →ₐ[R] k)) :
    ∃ (f : R) (_ : f ≠ 0) (d : ℕ) (ρ : ℕ → (B →ₐ[R] k)), Function.Injective ρ ∧
      ∀ (n : ℕ) (𝔪 : Ideal R) [𝔪.IsMaximal], f ∉ 𝔪 →
        ∃ (O : Type u) (_ : CommRing O) (_ : IsLocalRing O) (_ : IsDomain O) (_ : Algebra R O)
          (β : B →ₐ[R] O) (γ : O →ₐ[R] k), Function.Injective γ ∧ γ.comp β = ρ n ∧
          (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = 𝔪 ∧
          ∃ (_ : Algebra (R ⧸ 𝔪) (IsLocalRing.ResidueField O)),
            IsScalarTower R (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
            Module.Finite (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ∧
            Module.finrank (R ⧸ 𝔪) (IsLocalRing.ResidueField O) ≤ d :=
  exists_boundedDegree_points_of_not_isIntegral hι fun _ => by
    exact @not_finite _ hinf (finite_algHom_of_isIntegral hι)

/-- Let `R` be an infinite domain, `B` a finite type `R`-algebra and `k` an algebraically closed
field with `R ⊆ k` such that there are infinitely many `R`-algebra maps `B → k`. Then there are
`0 ≠ f ∈ R`, elements `u₁, …, u_d ∈ B` and an injective sequence `ρ` of `R`-algebra maps `B → k`
such that for every `n` and `b ∈ B` some `f ^ M • ρ n b` lies in `span R {ρ n (u_i)}`. -/
theorem exists_span_points_of_infinite {R B k : Type u} [CommRing R] [IsDomain R]
    [Infinite R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Field k] [IsAlgClosed k] [Algebra R k]
    (hι : Function.Injective (algebraMap R k))
    (hinf : Infinite (B →ₐ[R] k)) :
    ∃ (f : R) (_ : f ≠ 0) (d : ℕ) (u : Fin d → B) (ρ : ℕ → (B →ₐ[R] k)), Function.Injective ρ ∧
      ∀ (n : ℕ) (b : B), ∃ M : ℕ, f ^ M • ρ n b ∈ Submodule.span R (Set.range (ρ n ∘ u)) :=
  exists_span_points_of_not_isIntegral hι fun _ => by
    exact @not_finite _ hinf (finite_algHom_of_isIntegral hι)
