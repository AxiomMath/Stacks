module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixInertia

/-!
# Weil II 1.8.4 for representations with coefficients in a finite extension of `ℚ_ℓ`

The group form `Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_forall_isOpen` of Weil II,
Théorème 1.8.4, is stated for a representation with values in `GL_r(ℤ_ℓ)` read in `ℂ` along an
embedding of `ℚ_ℓ`.  The weights of Laumon's argument are read along one embedding `ι' : E → ℂ` of
a finite extension `E` of `ℚ_ℓ` at a time, for a representation `ρ : G → GL_r(E)` whose restriction
of scalars `Res_b ρ : G → GL_{r d}(ℚ_ℓ)` is continuous.  This file proves the theorem in that
setting: the `ℓ`-adic group theory (the tame generator, the tame relation, and the invariants of
open subgroups of inertia) runs on integral models of the restrictions of scalars of `ρ`, `ρ ⊗ ρ`
and `ρ^∨ ⊗ ρ^∨`, and is transported back to `E` through the coordinates of the basis `b`.

## Main results

* `Stacks.EtaleCohomology.exists_tame_generator_forall_isOpen`: the group-theoretic input for three
  continuous `ℤ_ℓ`-representations at once.
* `Stacks.EtaleCohomology.restrictScalarsMatrix_mulVec_restrictScalarsCoords`: `Res_b M` acts on the
  `b`-coordinates of `x` as `M` acts on `x`.
* `Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_forall_isOpen_restrictScalars`: Weil II
  1.8.4 along `ι' : E → ℂ`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7, 1.8.4.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open scoped Pointwise TensorProduct
open Matrix

namespace Stacks.EtaleCohomology

/-! ### Coordinates of restriction of scalars -/

section Coordinates

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- The `b`-coordinates `Fin (n * d) → F` of a vector `x : Fin n → E`. -/
public def restrictScalarsCoords {n : ℕ} (x : Fin n → E) : Fin (n * d) → F :=
  fun p => b.repr (x (finProdFinEquiv.symm p).1) (finProdFinEquiv.symm p).2

theorem restrictScalarsCoords_apply {n : ℕ} (x : Fin n → E) (i : Fin n) (l : Fin d) :
    restrictScalarsCoords b x (finProdFinEquiv (i, l)) = b.repr (x i) l := by
  simp [restrictScalarsCoords]

public theorem restrictScalarsCoords_injective {n : ℕ} :
    Function.Injective (restrictScalarsCoords (n := n) b) := by
  intro x y h
  funext i
  refine b.repr.injective (Finsupp.ext fun l => ?_)
  have := congrFun h (finProdFinEquiv (i, l))
  rwa [restrictScalarsCoords_apply, restrictScalarsCoords_apply] at this

/-- **`Res_b M` acts on coordinates as `M` acts on vectors.** -/
public theorem restrictScalarsMatrix_mulVec_restrictScalarsCoords {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (x : Fin n → E) :
    restrictScalarsMatrix b M *ᵥ restrictScalarsCoords b x =
      restrictScalarsCoords b (M *ᵥ x) := by
  funext p
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  rw [restrictScalarsCoords_apply, Matrix.mulVec, dotProduct, ← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type]
  simp only [restrictScalarsMatrix_apply, restrictScalarsCoords_apply]
  rw [Matrix.mulVec, dotProduct, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (Algebra.leftMulMatrix_mulVec_repr b (M i j) (x j)) l
  rw [Matrix.mulVec, dotProduct] at this
  rw [this]

/-- **Fixed vectors over `E` from fixed coordinates.**  If every vector of `F ^ (n d)` fixed by
`Res_b M` is fixed by `Res_b M'`, then every vector of `E ^ n` fixed by `M` is fixed by `M'`. -/
public theorem mulVec_eq_self_of_restrictScalarsMatrix {n : ℕ} {M M' : Matrix (Fin n) (Fin n) E}
    (h : ∀ y : Fin (n * d) → F, restrictScalarsMatrix b M *ᵥ y = y →
      restrictScalarsMatrix b M' *ᵥ y = y) (x : Fin n → E) (hx : M *ᵥ x = x) : M' *ᵥ x = x := by
  refine restrictScalarsCoords_injective b ?_
  rw [← restrictScalarsMatrix_mulVec_restrictScalarsCoords]
  exact h _ (by rw [restrictScalarsMatrix_mulVec_restrictScalarsCoords, hx])

/-- Restriction of scalars of square matrices is injective. -/
public theorem restrictScalarsMatrix_injective {n : ℕ} :
    Function.Injective (restrictScalarsMatrix (m := n) (n := n) b) := by
  intro M M' h
  ext i j
  refine (Algebra.leftMulMatrix_injective b) ?_
  ext l l'
  have := congrFun (congrFun h (finProdFinEquiv (i, l))) (finProdFinEquiv (j, l'))
  rwa [restrictScalarsMatrix_apply, restrictScalarsMatrix_apply] at this

end Coordinates

/-! ### Fixed vectors under conjugation -/

/-- If every vector fixed by `P⁻¹ A P` is fixed by `P⁻¹ B P`, then every vector fixed by `A` is
fixed by `B`. -/
theorem mulVec_eq_self_of_conj {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (P : GL n K) {A B : Matrix n n K}
    (h : ∀ y, (((P⁻¹ : GL n K) : Matrix n n K) * A * (P : Matrix n n K)) *ᵥ y = y →
      (((P⁻¹ : GL n K) : Matrix n n K) * B * (P : Matrix n n K)) *ᵥ y = y) (x : n → K)
    (hx : A *ᵥ x = x) : B *ᵥ x = x := by
  have hPP : ∀ z, (P : Matrix n n K) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have key := h (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ x) (by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP, hx])
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP] at key
  have := congrArg (fun z => (P : Matrix n n K) *ᵥ z) key
  simpa only [hPP] using this

/-! ### The group-theoretic input for three representations -/

section Tame

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [IsSepClosure K L] [Algebra A L] [IsScalarTower A K L]
  (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- **Grothendieck's tame generator for three representations at once.**  For continuous
`ρ₁ : G → GL_a(ℤ_ℓ)`, `ρ₂ : G → GL_b(ℤ_ℓ)`, `ρ₃ : G → GL_c(ℤ_ℓ)`, `φ : Gal(L/K) → G` and an
arithmetic Frobenius `Fr`, there is `T ∈ I` with `ρ₁(φ Fr) ρ₁(φ T) = ρ₁(φ T) ^ q ρ₁(φ Fr)` such
that for every `m > 0` there are an open subgroup `O` of `G` and `f > 0` with `φ(Fr) ^ f ∈ O`, and
every `σ ∈ I` with `φ σ ∈ O` fixes, under `ρ₂` and under `ρ₃`, every integral vector fixed by the
`m`-th power of the image of `T`. -/
public theorem exists_tame_generator_forall_isOpen {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A)) (φ : Gal(L/K) →* G) (hφ : Continuous φ)
    {a b c : ℕ} (ρ₁ : G →* GL (Fin a) ℤ_[ℓ]) (ρ₂ : G →* GL (Fin b) ℤ_[ℓ])
    (ρ₃ : G →* GL (Fin c) ℤ_[ℓ]) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
    (hρ₃ : Continuous ρ₃) (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P)
    (hFr : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∃ T ∈ P.inertia Gal(L/K),
      ρ₁ (φ Fr) * ρ₁ (φ T) = ρ₁ (φ T) ^ Nat.card (IsLocalRing.ResidueField A) * ρ₁ (φ Fr) ∧
      ∀ m : ℕ, 0 < m → ∃ O : Subgroup G, IsOpen (O : Set G) ∧ (∃ f : ℕ, 0 < f ∧ φ Fr ^ f ∈ O) ∧
        ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
          (∀ v : Fin b → ℤ_[ℓ],
            ((ρ₂ (φ T) ^ m : GL (Fin b) ℤ_[ℓ]) : Matrix (Fin b) (Fin b) ℤ_[ℓ]) *ᵥ v = v →
            ((ρ₂ (φ σ) : GL (Fin b) ℤ_[ℓ]) : Matrix (Fin b) (Fin b) ℤ_[ℓ]) *ᵥ v = v) ∧
          (∀ v : Fin c → ℤ_[ℓ],
            ((ρ₃ (φ T) ^ m : GL (Fin c) ℤ_[ℓ]) : Matrix (Fin c) (Fin c) ℤ_[ℓ]) *ᵥ v = v →
            ((ρ₃ (φ σ) : GL (Fin c) ℤ_[ℓ]) : Matrix (Fin c) (Fin c) ℤ_[ℓ]) *ᵥ v = v) := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  set q := Nat.card (IsLocalRing.ResidueField A) with hq_def
  obtain ⟨t, htc, htker, htFr, -⟩ := Stacks.FundamentalGroup.exists_ladicTameCharacter A K L P ℓ hℓ
  let J : Subgroup Gal(L/K) := P.inertia Gal(L/K) ⊓ (congruenceSubgroup ℓ a 1).comap (ρ₁.comp φ) ⊓
    (congruenceSubgroup ℓ b 1).comap (ρ₂.comp φ) ⊓ (congruenceSubgroup ℓ c 1).comap (ρ₃.comp φ)
  have hJI : J ≤ P.inertia Gal(L/K) := fun σ h => h.1.1.1
  have hJ : IsClosed (J : Set Gal(L/K)) := by
    refine (((isClosed_inertia A K L P).inter ?_).inter ?_).inter ?_
    · exact Subgroup.isClosed_of_isOpen _ ((isOpen_congruenceSubgroup 1).preimage (hρ₁.comp hφ))
    · exact Subgroup.isClosed_of_isOpen _ ((isOpen_congruenceSubgroup 1).preimage (hρ₂.comp hφ))
    · exact Subgroup.isClosed_of_isOpen _ ((isOpen_congruenceSubgroup 1).preimage (hρ₃.comp hφ))
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJ.isCompact
  let t' : J →* Multiplicative ℤ_[ℓ] := t.comp (Subgroup.inclusion hJI)
  have ht' : Continuous t' := htc.comp (continuous_subtype_val.subtype_mk fun x => hJI x.2)
  have hker₂ : ∀ τ : J, t' τ = 1 → (ρ₂.comp φ) τ = 1 := fun τ h =>
    map_eq_one_of_forall_exists_coprime_pow_mem (ρ := ρ₂.comp φ) (σ := (τ : Gal(L/K)))
      (hρ₂.comp hφ) τ.2.1.2 (htker _ h)
  have hker₃ : ∀ τ : J, t' τ = 1 → (ρ₃.comp φ) τ = 1 := fun τ h =>
    map_eq_one_of_forall_exists_coprime_pow_mem (ρ := ρ₃.comp φ) (σ := (τ : Gal(L/K)))
      (hρ₃.comp hφ) τ.2.2 (htker _ h)
  obtain ⟨T, hgen⟩ := Stacks.FundamentalGroup.exists_forall_exists_eq_mul_of_compactSpace t' ht'
  have hτ : ∀ U : OpenSubgroup Gal(L/K), ∃ m : ℕ, ℓ.Coprime m ∧
      (Fr * (T : Gal(L/K)) * Fr⁻¹ * ((T : Gal(L/K)) ^ q)⁻¹) ^ m ∈ U := by
    intro U
    obtain ⟨τ, hτ, hτ1, -⟩ := htFr Fr hFrD hFr ⟨T, hJI T.2⟩
    obtain ⟨m, hm, hmU⟩ := htker τ hτ1 U
    exact ⟨m, hm, by rw [← hτ]; exact hmU⟩
  refine ⟨T, hJI T.2, map_mul_eq_pow_mul_of_tame (ρ := ρ₁.comp φ) (hρ₁.comp hφ)
    (T := (T : Gal(L/K))) (Fr := Fr) T.2.1.1.2 hτ, fun m hm => ?_⟩
  have hpow_dvd : ∀ {n : ℕ} {H : Subgroup (GL (Fin n) ℤ_[ℓ])} {g : GL (Fin n) ℤ_[ℓ]} {f₀ d : ℕ},
      g ^ f₀ ∈ H → f₀ ∣ d → g ^ d ∈ H := by
    rintro n H g f₀ d h ⟨e, rfl⟩
    rw [pow_mul]
    exact Subgroup.pow_mem _ h e
  obtain ⟨N₂, hN₂⟩ := exists_forall_mulVec_eq_of_pow_mulVec_eq (ρ := ρ₂.comp φ) (hρ₂.comp hφ) t'
    ht' hker₂ T hgen hm
  obtain ⟨N₃, hN₃⟩ := exists_forall_mulVec_eq_of_pow_mulVec_eq (ρ := ρ₃.comp φ) (hρ₃.comp hφ) t'
    ht' hker₃ T hgen hm
  let O : Subgroup G :=
    (congruenceSubgroup ℓ b N₂).comap ρ₂ ⊓ (congruenceSubgroup ℓ c N₃).comap ρ₃ ⊓
      ((congruenceSubgroup ℓ a 1).comap ρ₁ ⊓ (congruenceSubgroup ℓ b 1).comap ρ₂ ⊓
        (congruenceSubgroup ℓ c 1).comap ρ₃)
  have hO : IsOpen (O : Set G) :=
    (((isOpen_congruenceSubgroup N₂).preimage hρ₂).inter
      ((isOpen_congruenceSubgroup N₃).preimage hρ₃)).inter
      ((((isOpen_congruenceSubgroup 1).preimage hρ₁).inter
        ((isOpen_congruenceSubgroup 1).preimage hρ₂)).inter
        ((isOpen_congruenceSubgroup 1).preimage hρ₃))
  obtain ⟨f₁, hf₁, h₁⟩ := exists_pow_mem_congruenceSubgroup (ρ₂ (φ Fr)) N₂
  obtain ⟨f₂, hf₂, h₂⟩ := exists_pow_mem_congruenceSubgroup (ρ₃ (φ Fr)) N₃
  obtain ⟨f₃, hf₃, h₃⟩ := exists_pow_mem_congruenceSubgroup (ρ₁ (φ Fr)) 1
  obtain ⟨f₄, hf₄, h₄⟩ := exists_pow_mem_congruenceSubgroup (ρ₂ (φ Fr)) 1
  obtain ⟨f₅, hf₅, h₅⟩ := exists_pow_mem_congruenceSubgroup (ρ₃ (φ Fr)) 1
  refine ⟨O, hO, ⟨f₁ * f₂ * f₃ * f₄ * f₅, by positivity, ?_⟩, fun σ hσI hσO => ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · change ρ₂ (φ Fr ^ (f₁ * f₂ * f₃ * f₄ * f₅)) ∈ congruenceSubgroup ℓ b N₂
      rw [map_pow]; exact hpow_dvd h₁ ⟨f₂ * f₃ * f₄ * f₅, by ring⟩
    · change ρ₃ (φ Fr ^ (f₁ * f₂ * f₃ * f₄ * f₅)) ∈ congruenceSubgroup ℓ c N₃
      rw [map_pow]; exact hpow_dvd h₂ ⟨f₁ * f₃ * f₄ * f₅, by ring⟩
    · change ρ₁ (φ Fr ^ (f₁ * f₂ * f₃ * f₄ * f₅)) ∈ congruenceSubgroup ℓ a 1
      rw [map_pow]; exact hpow_dvd h₃ ⟨f₁ * f₂ * f₄ * f₅, by ring⟩
    · change ρ₂ (φ Fr ^ (f₁ * f₂ * f₃ * f₄ * f₅)) ∈ congruenceSubgroup ℓ b 1
      rw [map_pow]; exact hpow_dvd h₄ ⟨f₁ * f₂ * f₃ * f₅, by ring⟩
    · change ρ₃ (φ Fr ^ (f₁ * f₂ * f₃ * f₄ * f₅)) ∈ congruenceSubgroup ℓ c 1
      rw [map_pow]; exact hpow_dvd h₅ ⟨f₁ * f₂ * f₃ * f₄, by ring⟩
  have hσJ : σ ∈ J := ⟨⟨⟨hσI, hσO.2.1.1⟩, hσO.2.1.2⟩, hσO.2.2⟩
  refine ⟨fun v hv => hN₂ ⟨σ, hσJ⟩ hσO.1.1 v ?_, fun v hv => hN₃ ⟨σ, hσJ⟩ hσO.1.2 v ?_⟩
  · simpa [map_pow] using hv
  · simpa [map_pow] using hv

end Tame

/-! ### The linear algebra of Weil II 1.8.4 in Kronecker form -/

section Kronecker

/-- An inclusion of fixed-vector spaces persists along a field embedding. -/
public theorem mulVec_map_eq_self_of_forall_mulVec_eq_self {K L : Type*} [Field K] [Field L]
    (ι : K →+* L) {n : Type*} [Fintype n] [DecidableEq n] {M M' : Matrix n n K}
    (h : ∀ v : n → K, M *ᵥ v = v → M' *ᵥ v = v) (w : n → L) (hw : M.map ι *ᵥ w = w) :
    M'.map ι *ᵥ w = w := by
  have hK : ∀ v : n → K, (M - 1) *ᵥ v = 0 → (M' - 1) *ᵥ v = 0 := fun v hv => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv ⊢
    exact h v hv
  have := mulVec_map_eq_zero_of_forall_mulVec_eq_zero ι hK w (by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.sub_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    exact hw)
  rwa [Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero] at this

variable {G : Type*} [Group G] {r : ℕ}

/-- **Weil II 1.8.4, linear algebra in Kronecker form.**  Let `ψ : G → GL_r(ℂ)`, `T, F ∈ G` with
`ψ(F) ψ(T) = ψ(T) ^ q ψ(F)`, `q ≥ 2`.  Suppose that for every `m > 0` the eigenvalues of
`(ψ ⊗ ψ)(F⁻¹)` on the vectors fixed by `(ψ ⊗ ψ)(T) ^ m` are bounded by `Q`, and those of
`(ψ^∨ ⊗ ψ^∨)(F⁻¹)` on the vectors fixed by `(ψ^∨ ⊗ ψ^∨)(T) ^ m` by `Q'`, `Q Q' = 1`.  Then every
eigenvalue `α` of `ψ(F⁻¹)` on a vector fixed by `ψ(T)` satisfies `|α|² q ^ i = Q`, `i ∈ ℕ`. -/
public theorem exists_norm_sq_mul_pow_eq_of_kronecker (ψ : G →* GL (Fin r) ℂ) (T F : G) {q : ℕ}
    (hq : 2 ≤ q) (hrel : ψ F * ψ T = ψ T ^ q * ψ F) {Q Q' : ℝ} (hQQ' : Q * Q' = 1)
    (H : ∀ m : ℕ, 0 < m → ∀ Y : Fin (r * r) → ℂ, Y ≠ 0 →
      ((kroneckerRepresentation ψ ψ T ^ m : GL (Fin (r * r)) ℂ) : Matrix _ _ ℂ) *ᵥ Y = Y →
      ∀ c : ℂ,
        ((kroneckerRepresentation ψ ψ F⁻¹ : GL (Fin (r * r)) ℂ) : Matrix _ _ ℂ) *ᵥ Y = c • Y →
        ‖c‖ ≤ Q)
    (H' : ∀ m : ℕ, 0 < m → ∀ Y : Fin (r * r) → ℂ, Y ≠ 0 →
      ((kroneckerRepresentation (contragredient ψ) (contragredient ψ) T ^ m :
        GL (Fin (r * r)) ℂ) : Matrix _ _ ℂ) *ᵥ Y = Y →
      ∀ c : ℂ, ((kroneckerRepresentation (contragredient ψ) (contragredient ψ) F⁻¹ :
        GL (Fin (r * r)) ℂ) : Matrix _ _ ℂ) *ᵥ Y = c • Y → ‖c‖ ≤ Q')
    {v : Fin r → ℂ} (hv0 : v ≠ 0) (hTv : ((ψ T : GL (Fin r) ℂ) : Matrix _ _ ℂ) *ᵥ v = v) {α : ℂ}
    (hα : ((ψ F⁻¹ : GL (Fin r) ℂ) : Matrix _ _ ℂ) *ᵥ v = α • v) :
    ∃ i : ℕ, ‖α‖ ^ 2 * (q : ℝ) ^ i = Q := by
  let E : GL (Fin r) ℂ →* Module.End ℂ (Fin r → ℂ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin r → ℂ)).toAlgHom
      |>.toRingHom.toMonoidHom.comp (Units.coeHom _)
  have hE : ∀ g, E g = Matrix.toLin' (g : Matrix (Fin r) (Fin r) ℂ) := fun g => rfl
  have hST : E (ψ T)⁻¹ * E (ψ T) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hTS : E (ψ T) * E (ψ T)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hGF : E (ψ F) * E (ψ F⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hFG : E (ψ F⁻¹) * E (ψ F) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hrel' : ψ T * ψ F⁻¹ = ψ F⁻¹ * ψ T ^ q := by
    rw [map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, hrel, mul_assoc, mul_inv_cancel, mul_one]
  have hTF : E (ψ T) * E (ψ F⁻¹) = E (ψ F⁻¹) * E (ψ T) ^ q := by
    rw [← map_mul, hrel', map_mul, map_pow]
  have hkron : ∀ g : GL (Fin r) ℂ, ((kroneckerMonoidHom ((g : Matrix (Fin r) (Fin r) ℂ),
      (g : Matrix (Fin r) (Fin r) ℂ))) : Matrix (Fin (r * r)) (Fin (r * r)) ℂ) =
      ((Units.map kroneckerMonoidHom (MulEquiv.prodUnits.symm (g, g)) : GL (Fin (r * r)) ℂ) :
        Matrix _ _ ℂ) := fun g => rfl
  have hHlin : ∀ m : ℕ, 0 < m → ∀ (X : (Fin r → ℂ) ⊗[ℂ] (Fin r → ℂ)) (c : ℂ), X ≠ 0 →
      TensorProduct.map (E (ψ T) ^ m) (E (ψ T) ^ m) X = X →
      TensorProduct.map (E (ψ F⁻¹)) (E (ψ F⁻¹)) X = c • X → ‖(RingHom.id ℂ) c‖ ≤ Q := by
    intro m hm X c hX hTX hFX
    rw [← map_pow, hE] at hTX
    rw [hE] at hFX
    refine H m hm (tensorFinEquiv X) ((LinearEquiv.map_ne_zero_iff _).2 hX) ?_ c ?_
    · have := congrArg tensorFinEquiv hTX
      rw [tensorFinEquiv_map, ← map_pow ψ] at this
      rw [← map_pow]
      exact this
    · have := congrArg tensorFinEquiv hFX
      rwa [tensorFinEquiv_map, LinearEquiv.map_smul] at this
  have hH'lin : ∀ m : ℕ, 0 < m → ∀ (X : Module.Dual ℂ (Fin r → ℂ) ⊗[ℂ] Module.Dual ℂ (Fin r → ℂ))
      (c : ℂ), X ≠ 0 →
      TensorProduct.map (E (ψ T)⁻¹ ^ m).dualMap (E (ψ T)⁻¹ ^ m).dualMap X = X →
      TensorProduct.map (E (ψ F)).dualMap (E (ψ F)).dualMap X = c • X →
        ‖(RingHom.id ℂ) c‖ ≤ Q' := by
    intro m hm X c hX hTX hFX
    have e1 : (ψ T)⁻¹ ^ m = (ψ (T ^ m))⁻¹ := by rw [map_pow, inv_pow]
    have e2 : ψ F = (ψ F⁻¹)⁻¹ := by rw [map_inv, inv_inv]
    rw [← map_pow, e1, hE] at hTX
    rw [e2, hE] at hFX
    refine H' m hm (dualTensorFinEquiv X) ((LinearEquiv.map_ne_zero_iff _).2 hX) ?_ c ?_
    · have := congrArg dualTensorFinEquiv hTX
      rw [dualTensorFinEquiv_map] at this
      rw [← map_pow]
      exact this
    · have := congrArg dualTensorFinEquiv hFX
      rwa [dualTensorFinEquiv_map, LinearEquiv.map_smul] at this
  obtain ⟨i, hi⟩ := exists_norm_sq_mul_pow_eq_of_tame_monodromy (RingHom.id ℂ) hST hTS hGF hFG hq
    hTF hQQ' hHlin hH'lin hv0 (by rw [hE, Matrix.toLin'_apply]; exact hTv)
    (by rw [hE, Matrix.toLin'_apply]; exact hα)
  exact ⟨i, by simpa using hi⟩

end Kronecker

/-! ### From the integral model of `Res_b σ` back to `σ` in `ℂ` -/

section Transfer

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E)

/-- **Fixed vectors of an integral model, read in `ℂ` on the representation itself.**  If every
integral vector fixed by the integral model of `Res_b σ` at `g` is fixed by it at `g'`, then every
vector of `ℂ ^ n` fixed by `σ(g)` read along `ι' : E → ℂ` is fixed by `σ(g')`. -/
public theorem mulVec_map_eq_self_of_integralModel {n : ℕ} (σ : G →* GL (Fin n) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (ι' : E →+* ℂ) {g g' : G}
    (h : ∀ v : Fin (n * d) → ℤ_[ℓ],
      ((integralModel (restrictScalarsRep b σ) hσ g : GL (Fin (n * d)) ℤ_[ℓ]) :
        Matrix (Fin (n * d)) (Fin (n * d)) ℤ_[ℓ]) *ᵥ v = v →
      ((integralModel (restrictScalarsRep b σ) hσ g' : GL (Fin (n * d)) ℤ_[ℓ]) :
        Matrix (Fin (n * d)) (Fin (n * d)) ℤ_[ℓ]) *ᵥ v = v)
    (Y : Fin n → ℂ) (hY : ((σ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map ι' *ᵥ Y = Y) :
    ((σ g' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map ι' *ᵥ Y = Y := by
  set P := (exists_conj_integral (restrictScalarsRep b σ) hσ).choose
  have hconj : ∀ x : G, ((integralModel (restrictScalarsRep b σ) hσ x : GL (Fin (n * d)) ℤ_[ℓ]) :
      Matrix (Fin (n * d)) (Fin (n * d)) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      ((P⁻¹ : GL (Fin (n * d)) ℚ_[ℓ]) : Matrix (Fin (n * d)) (Fin (n * d)) ℚ_[ℓ]) *
        restrictScalarsMatrix b ((σ x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        (P : Matrix (Fin (n * d)) (Fin (n * d)) ℚ_[ℓ]) := fun x => by
    have := congrArg Units.val (map_integralModel (restrictScalarsRep b σ) hσ x)
    rw [Units.val_mul, Units.val_mul, restrictScalarsRep_val] at this
    rw [← this]
    rfl
  have hQ := mulVec_eq_self_of_forall_integral h
  refine mulVec_map_eq_self_of_forall_mulVec_eq_self ι' (fun x hx => ?_) Y hY
  refine mulVec_eq_self_of_restrictScalarsMatrix b (fun y hy => ?_) x hx
  refine mulVec_eq_self_of_conj P (fun z hz => ?_) y hy
  rw [← hconj] at hz ⊢
  exact hQ z hz

end Transfer

/-! ### Weil II 1.8.4 along an embedding of the coefficient field -/

section Coefficients

/-- A matrix representation pushed along a ring homomorphism of its coefficients. -/
public abbrev mapRepresentation {G R S : Type*} [Group G] [CommRing R] [CommRing S] {n : Type*}
    [Fintype n] [DecidableEq n] (f : R →+* S) (ρ : G →* GL n R) : G →* GL n S :=
  (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom).comp ρ

theorem mapRepresentation_val {G R S : Type*} [Group G] [CommRing R] [CommRing S] {n : Type*}
    [Fintype n] [DecidableEq n] (f : R →+* S) (ρ : G →* GL n R) (g : G) :
    ((mapRepresentation f ρ g : GL n S) : Matrix n n S) = ((ρ g : GL n R) : Matrix n n R).map f :=
  rfl

theorem kroneckerRepresentation_mapRepresentation_val {G R S : Type*} [Group G] [CommRing R]
    [CommRing S] (f : R →+* S) {a b : ℕ} (ρ : G →* GL (Fin a) R) (ρ' : G →* GL (Fin b) R) (g : G) :
    ((kroneckerRepresentation (mapRepresentation f ρ) (mapRepresentation f ρ') g :
      GL (Fin (a * b)) S) : Matrix (Fin (a * b)) (Fin (a * b)) S) =
      (((kroneckerRepresentation ρ ρ' g : GL (Fin (a * b)) R) :
        Matrix (Fin (a * b)) (Fin (a * b)) R)).map f := by
  ext i j
  simp [kroneckerRepresentation_val, Matrix.kroneckerMap_apply]

theorem contragredient_mapRepresentation {G R S : Type*} [Group G] [CommRing R] [CommRing S]
    (f : R →+* S) {a : ℕ} (ρ : G →* GL (Fin a) R) :
    contragredient (mapRepresentation f ρ) = mapRepresentation f (contragredient ρ) := by
  ext g i j
  simp only [contragredient_val, mapRepresentation_val, ← map_inv, Matrix.transpose_apply,
    Matrix.map_apply]

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [IsSepClosure K L] [Algebra A L] [IsScalarTower A K L]
  (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- **Weil II, Théorème 1.8.4, with coefficients in a finite extension `E` of `ℚ_ℓ`, along one
embedding `ι' : E → ℂ`.**  Let `ρ : G → GL_r(E)` with `Res_b ρ`, `Res_b (ρ ⊗ ρ)` and
`Res_b (ρ^∨ ⊗ ρ^∨)` continuous, `φ : Gal(L/K) → G` continuous and `Fr ∈ D` an arithmetic Frobenius.
If for every open subgroup `O` of `G` and `f > 0` with `φ(Fr) ^ f ∈ O` the eigenvalues of
`(ρ ⊗ ρ)(φ Fr⁻¹) ^ f`, read along `ι'`, on the vectors fixed by `(ρ ⊗ ρ)(φ σ)` for all `σ ∈ I` with
`φ σ ∈ O` are bounded by `Q ^ f`, and likewise for `ρ^∨ ⊗ ρ^∨` with `Q'`, `Q Q' = 1`, then every
eigenvalue `α` of `ρ(φ Fr⁻¹)` on the `I`-invariants satisfies `|α|² q ^ i = Q` for some `i ∈ ℕ`. -/
public theorem exists_norm_sq_mul_pow_eq_of_forall_isOpen_restrictScalars {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A)) (φ : Gal(L/K) →* G) (hφ : Continuous φ)
    {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {r : ℕ}
    (ρ : G →* GL (Fin r) E) (hρ : Continuous (restrictScalarsRep b ρ))
    (hρ₂ : Continuous (restrictScalarsRep b (kroneckerRepresentation ρ ρ)))
    (hρ₃ : Continuous (restrictScalarsRep b
      (kroneckerRepresentation (contragredient ρ) (contragredient ρ))))
    (ι' : E →+* ℂ) {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q') (hQQ' : Q * Q' = 1) (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P)
    (hFr : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    (H : ∀ O : Subgroup G, IsOpen (O : Set G) → ∀ f : ℕ, 0 < f → φ Fr ^ f ∈ O →
      ∀ Y : Fin (r * r) → ℂ, Y ≠ 0 →
      (letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
        ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
          ((kroneckerRepresentation ρ ρ (φ σ) : GL (Fin (r * r)) E) :
            Matrix (Fin (r * r)) (Fin (r * r)) E).map ι' *ᵥ Y = Y) →
      ∀ c : ℂ, ((kroneckerRepresentation ρ ρ (φ Fr⁻¹) ^ f : GL (Fin (r * r)) E) :
          Matrix (Fin (r * r)) (Fin (r * r)) E).map ι' *ᵥ Y = c • Y → ‖c‖ ≤ Q ^ f)
    (H' : ∀ O : Subgroup G, IsOpen (O : Set G) → ∀ f : ℕ, 0 < f → φ Fr ^ f ∈ O →
      ∀ Y : Fin (r * r) → ℂ, Y ≠ 0 →
      (letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
        ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
          ((kroneckerRepresentation (contragredient ρ) (contragredient ρ) (φ σ) :
            GL (Fin (r * r)) E) : Matrix (Fin (r * r)) (Fin (r * r)) E).map ι' *ᵥ Y = Y) →
      ∀ c : ℂ, ((kroneckerRepresentation (contragredient ρ) (contragredient ρ) (φ Fr⁻¹) ^ f :
          GL (Fin (r * r)) E) : Matrix (Fin (r * r)) (Fin (r * r)) E).map ι' *ᵥ Y = c • Y →
        ‖c‖ ≤ Q' ^ f)
    {v : Fin r → ℂ} (hv0 : v ≠ 0)
    (hvI : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ σ ∈ P.inertia Gal(L/K),
        ((ρ (φ σ) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map ι' *ᵥ v = v)
    {α : ℂ} (hα : ((ρ (φ Fr⁻¹) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map ι' *ᵥ v = α • v) :
    ∃ i : ℕ, ‖α‖ ^ 2 * (Nat.card (IsLocalRing.ResidueField A) : ℝ) ^ i = Q := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  set q := Nat.card (IsLocalRing.ResidueField A) with hq_def
  have hq : 2 ≤ q := Finite.one_lt_card
  obtain ⟨T, hTI, hrel, hfix⟩ := exists_tame_generator_forall_isOpen A K L P hℓ φ hφ
    (integralModel _ hρ) (integralModel _ hρ₂) (integralModel _ hρ₃)
    (continuous_integralModel _ hρ) (continuous_integralModel _ hρ₂)
    (continuous_integralModel _ hρ₃) Fr hFrD hFr
  -- the tame relation for `ρ`
  have hrelR : restrictScalarsRep b ρ (φ Fr) * restrictScalarsRep b ρ (φ T) =
      restrictScalarsRep b ρ (φ T) ^ q * restrictScalarsRep b ρ (φ Fr) := by
    have h := congrArg (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))) hrel
    simp only [map_mul, map_pow, map_integralModel] at h
    set C := (exists_conj_integral (restrictScalarsRep b ρ) hρ).choose
    have e : ∀ x, C⁻¹ * x * C = MulAut.conj C⁻¹ x := fun x => by simp
    simp only [e] at h
    rw [← map_mul (MulAut.conj C⁻¹), ← map_pow (MulAut.conj C⁻¹), ← map_mul (MulAut.conj C⁻¹)] at h
    exact (MulAut.conj C⁻¹).injective h
  have hinj : Function.Injective (Units.map (restrictScalarsMonoidHom b r)) := fun x y h =>
    Units.ext (restrictScalarsMatrix_injective b (congrArg Units.val h))
  have hrelE : ρ (φ Fr) * ρ (φ T) = ρ (φ T) ^ q * ρ (φ Fr) :=
    hinj (by rw [map_mul, map_mul, map_pow]; exact hrelR)
  set ψ := mapRepresentation ι' ρ with hψ
  have hrelψ : ψ (φ Fr) * ψ (φ T) = ψ (φ T) ^ q * ψ (φ Fr) := by
    have := congrArg (Units.map (ι'.mapMatrix : Matrix (Fin r) (Fin r) E →+*
      Matrix (Fin r) (Fin r) ℂ).toMonoidHom) hrelE
    rw [map_mul, map_mul, map_pow] at this
    exact this
  refine exists_norm_sq_mul_pow_eq_of_kronecker ψ (φ T) (φ Fr) hq hrelψ hQQ' ?_ ?_ hv0 ?_ ?_
  · intro m hm Y hY hTY c hFY
    obtain ⟨O, hO, ⟨f, hf, hFrO⟩, hσ⟩ := hfix m hm
    have hinvY : ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
        ((kroneckerRepresentation ρ ρ (φ σ) : GL (Fin (r * r)) E) :
          Matrix (Fin (r * r)) (Fin (r * r)) E).map ι' *ᵥ Y = Y := by
      intro σ hσI hσO
      refine mulVec_map_eq_self_of_integralModel b _ hρ₂ ι' (g := φ T ^ m) (fun v hv => ?_) Y ?_
      · exact (hσ σ hσI hσO).1 v (by rwa [map_pow] at hv)
      · rw [← kroneckerRepresentation_mapRepresentation_val, map_pow]
        exact hTY
    have hc := H O hO f hf hFrO Y hY hinvY (c ^ f) (by
      rw [Units.val_pow_eq_pow_val, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply,
        ← kroneckerRepresentation_mapRepresentation_val, map_inv φ]
      exact pow_mulVec_eq_pow_smul hFY f)
    rw [norm_pow] at hc
    exact (pow_le_pow_iff_left₀ (norm_nonneg c) hQ hf.ne').1 hc
  · intro m hm Y hY hTY c hFY
    obtain ⟨O, hO, ⟨f, hf, hFrO⟩, hσ⟩ := hfix m hm
    rw [contragredient_mapRepresentation] at hTY hFY
    have hinvY : ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
        ((kroneckerRepresentation (contragredient ρ) (contragredient ρ) (φ σ) :
          GL (Fin (r * r)) E) : Matrix (Fin (r * r)) (Fin (r * r)) E).map ι' *ᵥ Y = Y := by
      intro σ hσI hσO
      refine mulVec_map_eq_self_of_integralModel b _ hρ₃ ι' (g := φ T ^ m) (fun v hv => ?_) Y ?_
      · exact (hσ σ hσI hσO).2 v (by rwa [map_pow] at hv)
      · rw [← kroneckerRepresentation_mapRepresentation_val, map_pow]
        exact hTY
    have hc := H' O hO f hf hFrO Y hY hinvY (c ^ f) (by
      rw [Units.val_pow_eq_pow_val, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply,
        ← kroneckerRepresentation_mapRepresentation_val, map_inv φ]
      exact pow_mulVec_eq_pow_smul hFY f)
    rw [norm_pow] at hc
    exact (pow_le_pow_iff_left₀ (norm_nonneg c) hQ' hf.ne').1 hc
  · rw [hψ, mapRepresentation_val]
    exact hvI T hTI
  · rw [← map_inv φ, hψ, mapRepresentation_val]
    exact hα

end Coefficients

end Stacks.EtaleCohomology

end
