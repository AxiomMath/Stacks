module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PadicIntegerRingExtensionModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingValuation

/-!
# Integers of a finite extension of `E`: commensurable models and coordinates modulo `ℓᵏ`

Let `E ⊆ E''` be finite extensions of `ℚ_ℓ` with integers `O_E ⊆ O''`.

* Two integral models over `O''` of conjugates of the same representation over `E''` are
  commensurable: there are integral intertwiners `A`, `A'` with `A' A = A A' = ℓᵃ`
  (`Stacks.EtaleCohomology.exists_intertwiner_pow_of_conj`), since every element of `E''` times a
  power of `ℓ` is integral (`Stacks.EtaleCohomology.exists_natCast_pow_mul_mem_padicIntegerRing`).
* `O''` is a free `O_E`-module of finite rank (`O_E` is a principal ideal domain), and an
  `O_E`-basis of `O''` gives, at every level `k`, elements `β_i` of `O''/ℓᵏ` and coordinate maps
  `π_i : O''/ℓᵏ → O_E/ℓᵏ` with `π_i(ρ(c) x) = c π_i(x)`, `π_j(β_i) = δ_{ij}` and
  `x = Σ_i ρ(π_i x) β_i` (`Stacks.EtaleCohomology.exists_quotient_coordinates`).

These are the algebraic inputs of the extension of the level isogeny of Laumon's comparison from
`O_E` to `O''` (step R3 of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.exists_natCast_pow_mul_mem_padicIntegerRing`.
* `Stacks.EtaleCohomology.exists_intertwiner_pow_of_conj`.
* `Stacks.EtaleCohomology.exists_quotient_coordinates`.
* `Stacks.EtaleCohomology.free_padicIntegerRing_extension`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Conj

variable {O K : Type*} [CommRing O] [Field K] [Algebra O K] {G : Type*} {m : ℕ} (ℓ : ℕ)

/-- **Commensurable models**: if `σ₁ = T₁⁻¹ ρ T₁` and `σ₂ = T₂⁻¹ ρ T₂` over `K` with `σ₁, σ₂`
integral over `O ⊆ K`, and every element of `K` times a power of `ℓ` is integral, then there are
integral `A`, `A'` with `A σ₁ = σ₂ A`, `A' σ₂ = σ₁ A'` and `A' A = A A' = ℓᵃ`. -/
theorem exists_intertwiner_pow_of_conj (hinj : Function.Injective (algebraMap O K))
    (hden : ∀ x : K, ∃ (c : ℕ) (y : O), algebraMap O K y = (ℓ : K) ^ c * x)
    (σ₁ σ₂ : G → Matrix (Fin m) (Fin m) O) (ρ : G → Matrix (Fin m) (Fin m) K)
    (T₁ T₂ : GL (Fin m) K)
    (h₁ : ∀ g, (σ₁ g).map (algebraMap O K) = (T₁⁻¹ : GL (Fin m) K).val * ρ g * T₁.val)
    (h₂ : ∀ g, (σ₂ g).map (algebraMap O K) = (T₂⁻¹ : GL (Fin m) K).val * ρ g * T₂.val) :
    ∃ (a : ℕ) (A A' : Matrix (Fin m) (Fin m) O), (∀ g, A * σ₁ g = σ₂ g * A) ∧
      (∀ g, A' * σ₂ g = σ₁ g * A') ∧ A' * A = ((ℓ : O) ^ a) • 1 ∧ A * A' = ((ℓ : O) ^ a) • 1 := by
  -- a common exponent clearing the denominators of `M = T₂⁻¹ T₁` and `M⁻¹ = T₁⁻¹ T₂`
  let M : Matrix (Fin m) (Fin m) K := (T₂⁻¹ : GL (Fin m) K).val * T₁.val
  let M' : Matrix (Fin m) (Fin m) K := (T₁⁻¹ : GL (Fin m) K).val * T₂.val
  have hden' : ∀ x : K, ∃ c : ℕ, ∀ c' ≥ c, ∃ y : O, algebraMap O K y = (ℓ : K) ^ c' * x := by
    intro x
    obtain ⟨c, y, hy⟩ := hden x
    refine ⟨c, fun c' hc' => ⟨(ℓ : O) ^ (c' - c) * y, ?_⟩⟩
    rw [map_mul, hy, map_pow, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hc']
  choose c hc using hden'
  let a : ℕ := ∑ p : Fin m × Fin m, (c (M p.1 p.2) + c (M' p.1 p.2))
  have hle : ∀ p : Fin m × Fin m, c (M p.1 p.2) ≤ a ∧ c (M' p.1 p.2) ≤ a := fun p => by
    have := Finset.single_le_sum (f := fun p : Fin m × Fin m => c (M p.1 p.2) + c (M' p.1 p.2))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
    exact ⟨le_trans (Nat.le_add_right _ _) this, le_trans (Nat.le_add_left _ _) this⟩
  choose y hy using fun p : Fin m × Fin m => hc (M p.1 p.2) a (hle p).1
  choose y' hy' using fun p : Fin m × Fin m => hc (M' p.1 p.2) a (hle p).2
  let A : Matrix (Fin m) (Fin m) O := Matrix.of fun i j => y (i, j)
  let A' : Matrix (Fin m) (Fin m) O := Matrix.of fun i j => y' (i, j)
  have hA : A.map (algebraMap O K) = ((ℓ : K) ^ a) • M := by
    ext i j
    exact hy (i, j)
  have hA' : A'.map (algebraMap O K) = ((ℓ : K) ^ a) • M' := by
    ext i j
    exact hy' (i, j)
  have hinv : ∀ U V : GL (Fin m) K,
      (U⁻¹ : GL (Fin m) K).val * V.val * ((V⁻¹ : GL (Fin m) K).val * U.val) = 1 := fun U V => by
    have : U⁻¹ * V * (V⁻¹ * U) = 1 := by group
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val this
  have hMM' : M * M' = 1 := hinv T₂ T₁
  have hM'M : M' * M = 1 := hinv T₁ T₂
  have hmapinj : ∀ X Y : Matrix (Fin m) (Fin m) O,
      X.map (algebraMap O K) = Y.map (algebraMap O K) → X = Y :=
    fun _ _ h => Matrix.map_injective hinj h
  -- `M σ₁ = σ₂ M` over `K`
  have hint : ∀ g, M * (σ₁ g).map (algebraMap O K) = (σ₂ g).map (algebraMap O K) * M := fun g => by
    rw [h₁, h₂]
    change (T₂⁻¹ : GL (Fin m) K).val * T₁.val * ((T₁⁻¹ : GL (Fin m) K).val * ρ g * T₁.val) =
      (T₂⁻¹ : GL (Fin m) K).val * ρ g * T₂.val * ((T₂⁻¹ : GL (Fin m) K).val * T₁.val)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T₁.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.mul_assoc T₂.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
  have hint' : ∀ g, M' * (σ₂ g).map (algebraMap O K) = (σ₁ g).map (algebraMap O K) * M' :=
    fun g => by
      have := congrArg (fun X => M' * X * M') (hint g)
      simp only [← Matrix.mul_assoc, hM'M, Matrix.one_mul] at this
      simp only [Matrix.mul_assoc, hMM', Matrix.mul_one] at this
      exact this.symm
  refine ⟨a + a, A, A', fun g => hmapinj _ _ ?_, fun g => hmapinj _ _ ?_, hmapinj _ _ ?_,
    hmapinj _ _ ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, hA, Matrix.smul_mul, Matrix.mul_smul, hint]
  · rw [Matrix.map_mul, Matrix.map_mul, hA', Matrix.smul_mul, Matrix.mul_smul, hint']
  · rw [Matrix.map_mul, hA, hA', Matrix.smul_mul, Matrix.mul_smul, hM'M, smul_smul, ← pow_add,
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow,
      map_natCast]
  · rw [Matrix.map_mul, hA, hA', Matrix.smul_mul, Matrix.mul_smul, hMM', smul_smul, ← pow_add,
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow,
      map_natCast]

end Conj

section Reduction

variable {R S : Type*} [CommRing R] [CommRing S] (ι : R →+* S) (I : Ideal S) (J : Ideal R)
  (hJI : J ≤ I.comap ι) {G : Type*} [Group G] {m : ℕ}

/-- **Intertwiners modulo an ideal**: integral intertwiners `A : σ_O → ι ∘ σ_E` and
`A' : ι ∘ σ_E → σ_O` with `A' A = A A' = n` reduce, modulo `I ⊇ ι(J)`, to intertwiners between
`σ_O mod I` and `ρ ∘ (σ_E mod J)`, `ρ : R/J → S/I` induced by `ι`, with the same products. -/
theorem intertwiners_quotient (σE : G →* GL (Fin m) R) (σO : G →* GL (Fin m) S)
    (A A' : Matrix (Fin m) (Fin m) S) (hA : ∀ g, A * (σO g).val = (σE g).val.map ι * A)
    (hA' : ∀ g, A' * (σE g).val.map ι = (σO g).val * A') (n : ℕ)
    (hAA' : A' * A = (n : S) • 1) (hA'A : A * A' = (n : S) • 1) :
    (∀ g, A.map (Ideal.Quotient.mk I) *
        (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp σO) g).val =
      (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp σE) g).val.map
        (Ideal.quotientMap I ι hJI) * A.map (Ideal.Quotient.mk I)) ∧
    (∀ g, A'.map (Ideal.Quotient.mk I) *
        (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp σE) g).val.map
          (Ideal.quotientMap I ι hJI) =
      (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp σO) g).val *
        A'.map (Ideal.Quotient.mk I)) ∧
    A'.map (Ideal.Quotient.mk I) * A.map (Ideal.Quotient.mk I) = (n : S ⧸ I) • 1 ∧
    A.map (Ideal.Quotient.mk I) * A'.map (Ideal.Quotient.mk I) = (n : S ⧸ I) • 1 := by
  have hmk : ∀ M : Matrix (Fin m) (Fin m) R,
      (M.map (Ideal.Quotient.mk J)).map (Ideal.quotientMap I ι hJI) =
        (M.map ι).map (Ideal.Quotient.mk I) := fun _ => rfl
  have hn : ((n : S) • (1 : Matrix (Fin m) (Fin m) S)).map (Ideal.Quotient.mk I) =
      (n : S ⧸ I) • 1 := by
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _),
      map_natCast]
  refine ⟨fun g => ?_, fun g => ?_, ?_, ?_⟩
  · change A.map (Ideal.Quotient.mk I) * (σO g).val.map (Ideal.Quotient.mk I) =
      ((σE g).val.map (Ideal.Quotient.mk J)).map (Ideal.quotientMap I ι hJI) *
        A.map (Ideal.Quotient.mk I)
    rw [hmk, ← Matrix.map_mul, ← Matrix.map_mul, hA g]
  · change A'.map (Ideal.Quotient.mk I) *
        ((σE g).val.map (Ideal.Quotient.mk J)).map (Ideal.quotientMap I ι hJI) =
      (σO g).val.map (Ideal.Quotient.mk I) * A'.map (Ideal.Quotient.mk I)
    rw [hmk, ← Matrix.map_mul, ← Matrix.map_mul, hA' g]
  · rw [← Matrix.map_mul, hAA', hn]
  · rw [← Matrix.map_mul, hA'A, hn]

end Reduction

section Integers

attribute [local instance] padicIntAlgebraOfRat

variable (ℓ : ℕ) [Fact ℓ.Prime] {E' : Type} [Field E'] [Algebra ℚ_[ℓ] E']
  [FiniteDimensional ℚ_[ℓ] E']

/-- **Every element of `E'` times a power of `ℓ` is integral.** -/
theorem exists_natCast_pow_mul_mem_padicIntegerRing (x : E') :
    ∃ (c : ℕ) (y : integralClosure ℤ_[ℓ] E'),
      algebraMap (integralClosure ℤ_[ℓ] E') E' y = (ℓ : E') ^ c * x := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure ℤ_[ℓ] E') x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  obtain ⟨c, r, hr⟩ := exists_dvd_natCast_pow_padicIntegerRing ℓ hq0
  refine ⟨c, p * r, ?_⟩
  have hq' : algebraMap (integralClosure ℤ_[ℓ] E') E' q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure ℤ_[ℓ] E') E')).2 hq0
  have hℓ : (ℓ : E') ^ c = algebraMap (integralClosure ℤ_[ℓ] E') E' q *
      algebraMap (integralClosure ℤ_[ℓ] E') E' r := by
    rw [← map_mul, ← hr, map_pow, map_natCast]
  rw [hℓ, map_mul]
  field_simp

end Integers

section Coordinates

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e : ℕ} (ℓ k : ℕ)

/-- The span of `ℓᵏ` in `R` is contained in the preimage of its span in `S`. -/
theorem span_natCast_pow_le_comap :
    Ideal.span {(ℓ : R) ^ k} ≤ (Ideal.span {(ℓ : S) ^ k}).comap (algebraMap R S) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
    map_natCast]
  exact Ideal.subset_span rfl

/-- **Coordinates modulo `ℓᵏ` along a basis**: for an `R`-basis `b` of `S`, the images `β_i` of
`b_i` in `S/ℓᵏ` and the coordinates `π_i : S/ℓᵏ → R/ℓᵏ` satisfy `π_i(ρ(c) x) = c π_i(x)`,
`π_j(β_i) = δ_{ij}` and `x = Σ_i ρ(π_i x) β_i`, for `ρ : R/ℓᵏ → S/ℓᵏ` the induced map. -/
theorem exists_quotient_coordinates (b : Module.Basis (Fin e) R S) :
    ∃ (β : Fin e → S ⧸ Ideal.span {(ℓ : S) ^ k})
      (π : Fin e → (S ⧸ Ideal.span {(ℓ : S) ^ k}) →+ (R ⧸ Ideal.span {(ℓ : R) ^ k})),
      (∀ i (c : R ⧸ Ideal.span {(ℓ : R) ^ k}) (x : S ⧸ Ideal.span {(ℓ : S) ^ k}),
        π i (Ideal.quotientMap _ (algebraMap R S) (span_natCast_pow_le_comap ℓ k) c * x) =
          c * π i x) ∧
      (∀ i j, π j (β i) = if i = j then 1 else 0) ∧
      ∀ x : S ⧸ Ideal.span {(ℓ : S) ^ k}, ∑ i, Ideal.quotientMap _ (algebraMap R S)
        (span_natCast_pow_le_comap ℓ k) (π i x) * β i = x := by
  let I : Ideal S := Ideal.span {(ℓ : S) ^ k}
  let J : Ideal R := Ideal.span {(ℓ : R) ^ k}
  have hIJ : ∀ i, I.restrictScalars R ≤ LinearMap.ker (J.mkQ ∘ₗ b.coord i) := fun i x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have hy : y * (ℓ : S) ^ k = ((ℓ : R) ^ k) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hy, map_smul, smul_eq_mul]
    exact J.mul_mem_right _ (Ideal.subset_span rfl)
  let π : Fin e → (S ⧸ I) →+ (R ⧸ J) := fun i =>
    ((I.restrictScalars R).liftQ (J.mkQ ∘ₗ b.coord i) (hIJ i) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R I).symm.toLinearMap).toAddMonoidHom
  have hπ : ∀ i (x : S), π i (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (b.repr x i) :=
    fun i x => rfl
  refine ⟨fun i => Ideal.Quotient.mk I (b i), π, fun i c x => ?_, fun i j => ?_, fun x => ?_⟩
  · obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, ← map_mul, hπ, hπ, ← map_mul, ← Algebra.smul_def, map_smul]
    rfl
  · rw [hπ, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    calc ∑ i, Ideal.quotientMap _ (algebraMap R S) (span_natCast_pow_le_comap ℓ k)
          (π i (Ideal.Quotient.mk I x)) * Ideal.Quotient.mk I (b i) =
        ∑ i, Ideal.Quotient.mk I (algebraMap R S (b.repr x i) * b i) :=
          Finset.sum_congr rfl fun i _ => by rw [hπ, Ideal.quotientMap_mk, map_mul]
      _ = Ideal.Quotient.mk I (∑ i, algebraMap R S (b.repr x i) * b i) := (map_sum _ _ _).symm
      _ = Ideal.Quotient.mk I x := by
          congr 1
          conv_rhs => rw [← b.sum_repr x]
          exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm

end Coordinates

section Free

attribute [local instance] padicIntAlgebraOfRat

variable (ℓ : ℕ) [Fact ℓ.Prime] (E L : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  [Field L] [Algebra E L] [Algebra ℚ_[ℓ] L] [IsScalarTower ℚ_[ℓ] E L] [FiniteDimensional ℚ_[ℓ] L]

/-- **The integers of `L` are a free module of finite rank over the integers of `E`** (through
`Stacks.EtaleCohomology.padicIntegerRingMap`): `O_L` is finite and torsion free over the
principal ideal domain `O_E`. -/
theorem free_padicIntegerRing_extension :
    letI := (padicIntegerRingMap ℓ E L).toAlgebra
    Module.Free (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L) ∧
      Module.Finite (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L) := by
  let := (padicIntegerRingMap ℓ E L).toAlgebra
  have := isPrincipalIdealRing_padicIntegerRing ℓ (E := E)
  have : IsScalarTower ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L) :=
    IsScalarTower.of_algebraMap_eq fun z => Subtype.ext (by
      change algebraMap ℤ_[ℓ] L z = algebraMap E L (algebraMap ℤ_[ℓ] E z)
      exact (isScalarTower_padicInt_padicIntAlgebraOfRat ℓ E L).algebraMap_apply ℤ_[ℓ] E L z)
  have hfin : Module.Finite (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L) :=
    Module.Finite.of_restrictScalars_finite ℤ_[ℓ] _ _
  have hinj : Function.Injective
      (algebraMap (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L)) := fun _ _ h =>
    Subtype.ext ((algebraMap E L).injective (congrArg Subtype.val h))
  have : FaithfulSMul (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L) :=
    FaithfulSMul.to_isTorsionFree _ _
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

/-- **Coordinates modulo `ℓᵏ` along an `O_E`-basis of `O_L`**: there are `e`, `β_i ∈ O_L/ℓᵏ` and
coordinate maps `π_i : O_L/ℓᵏ → O_E/ℓᵏ` with `π_i(ρ(c) x) = c π_i(x)`, `π_j(β_i) = δ_{ij}` and
`x = Σ_i ρ(π_i x) β_i`, for `ρ : O_E/ℓᵏ → O_L/ℓᵏ` induced by `O_E → O_L`. -/
theorem exists_padicIntegerRing_quotient_coordinates (k : ℕ)
    (h : Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k} ≤
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] L) ^ k}).comap (padicIntegerRingMap ℓ E L)) :
    ∃ (e : ℕ) (β : Fin e → integralClosure ℤ_[ℓ] L ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] L) ^ k})
      (π : Fin e → (integralClosure ℤ_[ℓ] L ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] L) ^ k}) →+
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k})),
      (∀ i c x, π i (Ideal.quotientMap _ (padicIntegerRingMap ℓ E L) h c * x) = c * π i x) ∧
      (∀ i j, π j (β i) = if i = j then 1 else 0) ∧
      ∀ x, ∑ i, Ideal.quotientMap _ (padicIntegerRingMap ℓ E L) h (π i x) * β i = x := by
  let := (padicIntegerRingMap ℓ E L).toAlgebra
  obtain ⟨hfree, hfin⟩ := free_padicIntegerRing_extension ℓ E L
  exact ⟨_, exists_quotient_coordinates ℓ k
    (Module.finBasis (integralClosure ℤ_[ℓ] E) (integralClosure ℤ_[ℓ] L))⟩

omit [FiniteDimensional ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] L] in
/-- The span of `ℓᵏ` in `O_E` is contained in the preimage of its span in `O_L`. -/
theorem span_natCast_pow_le_comap_padicIntegerRingMap (k : ℕ) :
    Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k} ≤
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] L) ^ k}).comap (padicIntegerRingMap ℓ E L) :=
  let := (padicIntegerRingMap ℓ E L).toAlgebra
  span_natCast_pow_le_comap ℓ k

end Free

end Stacks.EtaleCohomology

end
