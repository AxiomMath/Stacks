module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyInertia
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyQuasiUnipotent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixPlumbing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TameInvariantsOpenSubgroup

/-!
# Inertia invariants of a pure representation are strongly mixed (Weil II 1.8.4, group form)

Let `A` be a discrete valuation ring with finite residue field of cardinality `q`, `K` its
fraction field, `L` a separable closure, `P` a place of `L` over `A` with inertia group `I` and
decomposition group `D` in `Gal(L/K)`, `φ : Gal(L/K) → G` a continuous homomorphism (for a curve
`V` and a missing point, `G = π₁(V, η̄)`, `φ` the canonical map) and `ρ : G → GL_r(ℤ_ℓ)`
continuous, `ℓ ≠ p`.  Fix an arithmetic Frobenius `Fr ∈ D` and an embedding `ι : ℚ_ℓ → ℂ`, and
read every matrix in `ℂ` along `ι`.

Deligne's Théorème 1.8.4 says that the eigenvalues `α` of the geometric Frobenius `ρ(φ Fr⁻¹)` on
the `I`-invariants satisfy `|α|² q ^ i = Q` for some `i ∈ ℕ`, `Q = q ^ w`, when `ρ` is pure of
weight `w`.  Its proof combines Grothendieck's local monodromy theorem with **weak** bounds on the
local invariants of `ρ ⊗ ρ` and of `ρ^∨ ⊗ ρ^∨` after finite extensions of the local field.  This
file proves the theorem from exactly those weak bounds, stated for the open subgroups `O` of `G`
(the finite étale covers of `V`): for every open subgroup `O` and every `f > 0` with
`φ(Fr) ^ f ∈ O`, the eigenvalues of `φ(Fr⁻¹) ^ f` on the `(I ∩ φ⁻¹ O)`-invariants of `ρ ⊗ ρ`
(resp. `ρ^∨ ⊗ ρ^∨`) are bounded by `Q ^ f` (resp. `Q' ^ f`), `Q Q' = 1`.

The two are related by `Stacks.EtaleCohomology.exists_forall_mulVec_eq_of_pow_mulVec_eq`: the
invariants of `T ^ m`, `T` a tame generator, are invariants of `I ∩ φ⁻¹ O` for `O` the preimage
of a congruence subgroup.

## Main results

* `Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_forall_isOpen`: under these weak bounds,
  every eigenvalue `α` of `ρ(φ Fr⁻¹)` on the `I`-invariants satisfies `|α|² q ^ i = Q`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7, 1.8.4.
* K. Kedlaya, *Fourier transforms and p-adic Weil II*, Compos. Math. 142 (2006), Prop. 6.3.3.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open scoped Pointwise TensorProduct
open Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- Matrices over `ℤ_ℓ` read in `ℂ` along `ι : ℚ_ℓ → ℂ`. -/
abbrev complexMatrixHom (ι : ℚ_[ℓ] →+* ℂ) (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℤ_[ℓ] →+* Matrix n n ℂ :=
  (ι.comp (algebraMap ℤ_[ℓ] ℚ_[ℓ])).mapMatrix

/-- `GL_r(ℤ_ℓ) → End_ℂ(ℂ ^ r)` along `ι`. -/
abbrev complexEndHom (ι : ℚ_[ℓ] →+* ℂ) (r : ℕ) : GL (Fin r) ℤ_[ℓ] →* Module.End ℂ (Fin r → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin r → ℂ)).toAlgHom
    |>.toRingHom.toMonoidHom.comp ((complexMatrixHom ι (Fin r)).toMonoidHom.comp (Units.coeHom _))

/-- `complexEndHom ι r g` is the linear map `ℂ ^ r → ℂ ^ r` given by the matrix of `g` read in
`ℂ` along `ι`. -/
theorem complexEndHom_apply (ι : ℚ_[ℓ] →+* ℂ) (g : GL (Fin r) ℤ_[ℓ]) :
    complexEndHom ι r g = Matrix.toLin' (complexMatrixHom ι (Fin r) g) :=
  rfl

/-- The Kronecker product commutes with reading matrices in `ℂ`. -/
theorem complexMatrixHom_kroneckerMonoidHom (ι : ℚ_[ℓ] →+* ℂ) {s : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (N : Matrix (Fin s) (Fin s) ℤ_[ℓ]) :
    complexMatrixHom ι (Fin (r * s)) (kroneckerMonoidHom (M, N)) =
      kroneckerMonoidHom (complexMatrixHom ι (Fin r) M, complexMatrixHom ι (Fin s) N) := by
  ext i j
  simp [kroneckerMonoidHom_apply, Matrix.kroneckerMap_apply]

/-- A vector fixed by `M` is fixed by every power of `M`; an eigenvector of `M` with eigenvalue
`c` is an eigenvector of `M ^ f` with eigenvalue `c ^ f`. -/
theorem pow_mulVec_eq_pow_smul {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    {Y : n → ℂ} {c : ℂ} (h : M *ᵥ Y = c • Y) (f : ℕ) : (M ^ f) *ᵥ Y = c ^ f • Y := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ, mul_comm]

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [IsSepClosure K L] [Algebra A L] [IsScalarTower A K L]
  (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- **Weil II, Théorème 1.8.4, from weak bounds on open subgroups.**  Let `ρ : G → GL_r(ℤ_ℓ)` and
`φ : Gal(L/K) → G` be continuous, `Fr ∈ D` an arithmetic Frobenius and `ι : ℚ_ℓ → ℂ`, all matrices
read in `ℂ` along `ι`.  Suppose that for every open subgroup `O` of `G` and `f > 0` with
`φ(Fr) ^ f ∈ O`, every eigenvalue `c` of `(ρ ⊗ ρ)(φ Fr⁻¹) ^ f` on the vectors fixed by
`(ρ ⊗ ρ)(φ σ)` for all `σ ∈ I` with `φ σ ∈ O` satisfies `|c| ≤ Q ^ f`, and likewise for the
contragredient `ρ^∨ ⊗ ρ^∨` with `Q'`, where `Q, Q' ≥ 0` and `Q Q' = 1`.  Then every eigenvalue
`α` of `ρ(φ Fr⁻¹)` on the `I`-invariants satisfies `|α|² q ^ i = Q` for some `i ∈ ℕ`. -/
public theorem exists_norm_sq_mul_pow_eq_of_forall_isOpen
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A))
    (φ : Gal(L/K) →* G) (hφ : Continuous φ) {r : ℕ} (ρ : G →* GL (Fin r) ℤ_[ℓ])
    (hρ : Continuous ρ) (ι : ℚ_[ℓ] →+* ℂ) {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q')
    (hQQ' : Q * Q' = 1) (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P)
    (hFr : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    (H : ∀ O : Subgroup G, IsOpen (O : Set G) → ∀ f : ℕ, 0 < f → φ Fr ^ f ∈ O →
      ∀ Y : Fin (r * r) → ℂ, Y ≠ 0 →
      (letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
        ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
          complexMatrixHom ι _ (kroneckerRepresentation ρ ρ (φ σ)) *ᵥ Y = Y) →
      ∀ c : ℂ, complexMatrixHom ι _ (kroneckerRepresentation ρ ρ (φ Fr⁻¹) ^ f) *ᵥ Y = c • Y →
        ‖c‖ ≤ Q ^ f)
    (H' : ∀ O : Subgroup G, IsOpen (O : Set G) → ∀ f : ℕ, 0 < f → φ Fr ^ f ∈ O →
      ∀ Y : Fin (r * r) → ℂ, Y ≠ 0 →
      (letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
        ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
          complexMatrixHom ι _ (kroneckerRepresentation (contragredient ρ) (contragredient ρ)
            (φ σ)) *ᵥ Y = Y) →
      ∀ c : ℂ, complexMatrixHom ι _ (kroneckerRepresentation (contragredient ρ) (contragredient ρ)
          (φ Fr⁻¹) ^ f) *ᵥ Y = c • Y →
        ‖c‖ ≤ Q' ^ f)
    {v : Fin r → ℂ} (hv0 : v ≠ 0)
    (hvI : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ σ ∈ P.inertia Gal(L/K), complexMatrixHom ι _ (ρ (φ σ)) *ᵥ v = v)
    {α : ℂ} (hα : complexMatrixHom ι _ (ρ (φ Fr⁻¹)) *ᵥ v = α • v) :
    ∃ i : ℕ, ‖α‖ ^ 2 * (Nat.card (IsLocalRing.ResidueField A) : ℝ) ^ i = Q := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  set q := Nat.card (IsLocalRing.ResidueField A) with hq_def
  have hq : 2 ≤ q := Finite.one_lt_card
  obtain ⟨t, htc, htker, htFr, -⟩ := Stacks.FundamentalGroup.exists_ladicTameCharacter A K L P ℓ hℓ
  set ρ₂ := kroneckerRepresentation ρ ρ with hρ₂
  set ρ₃ := kroneckerRepresentation (contragredient ρ) (contragredient ρ) with hρ₃
  have hρ₂c : Continuous ρ₂ := continuous_kroneckerRepresentation ρ ρ hρ hρ
  have hρ₃c : Continuous ρ₃ := continuous_kroneckerRepresentation _ _
    (continuous_contragredient hρ) (continuous_contragredient hρ)
  -- the open subgroup `J` of inertia on which all three representations are `≡ 1 (mod ℓ)`
  let J : Subgroup Gal(L/K) := P.inertia Gal(L/K) ⊓ (congruenceSubgroup ℓ r 1).comap (ρ.comp φ) ⊓
    (congruenceSubgroup ℓ (r * r) 1).comap (ρ₂.comp φ) ⊓
    (congruenceSubgroup ℓ (r * r) 1).comap (ρ₃.comp φ)
  have hJI : J ≤ P.inertia Gal(L/K) := fun σ h => h.1.1.1
  have hJ : IsClosed (J : Set Gal(L/K)) := by
    refine (((isClosed_inertia A K L P).inter ?_).inter ?_).inter ?_
    · exact Subgroup.isClosed_of_isOpen _ ((isOpen_congruenceSubgroup 1).preimage (hρ.comp hφ))
    · exact Subgroup.isClosed_of_isOpen _ ((isOpen_congruenceSubgroup 1).preimage (hρ₂c.comp hφ))
    · exact Subgroup.isClosed_of_isOpen _ ((isOpen_congruenceSubgroup 1).preimage (hρ₃c.comp hφ))
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJ.isCompact
  let t' : J →* Multiplicative ℤ_[ℓ] := t.comp (Subgroup.inclusion hJI)
  have ht' : Continuous t' := htc.comp (continuous_subtype_val.subtype_mk fun x => hJI x.2)
  have hker₂ : ∀ τ : J, t' τ = 1 → (ρ₂.comp φ) τ = 1 := fun τ h =>
    map_eq_one_of_forall_exists_coprime_pow_mem (ρ := ρ₂.comp φ) (σ := (τ : Gal(L/K)))
      (hρ₂c.comp hφ) τ.2.1.2 (htker _ h)
  have hker₃ : ∀ τ : J, t' τ = 1 → (ρ₃.comp φ) τ = 1 := fun τ h =>
    map_eq_one_of_forall_exists_coprime_pow_mem (ρ := ρ₃.comp φ) (σ := (τ : Gal(L/K)))
      (hρ₃c.comp hφ) τ.2.2 (htker _ h)
  obtain ⟨T, hgen⟩ := Stacks.FundamentalGroup.exists_forall_exists_eq_mul_of_compactSpace t' ht'
  -- the tame relation `ρ(Fr) ρ(T) = ρ(T) ^ q ρ(Fr)`
  have hτ : ∀ U : OpenSubgroup Gal(L/K), ∃ m : ℕ, ℓ.Coprime m ∧
      (Fr * (T : Gal(L/K)) * Fr⁻¹ * ((T : Gal(L/K)) ^ q)⁻¹) ^ m ∈ U := by
    intro U
    obtain ⟨τ, hτ, hτ1, -⟩ := htFr Fr hFrD hFr ⟨T, hJI T.2⟩
    obtain ⟨m, hm, hmU⟩ := htker τ hτ1 U
    exact ⟨m, hm, by rw [← hτ]; exact hmU⟩
  have hrel := map_mul_eq_pow_mul_of_tame (ρ := ρ.comp φ) (hρ.comp hφ) (T := (T : Gal(L/K)))
    (Fr := Fr) T.2.1.1.2 hτ
  have hrel' : ρ (φ T) * ρ (φ Fr⁻¹) = ρ (φ Fr⁻¹) * ρ (φ T) ^ q := by
    have h0 : ρ (φ Fr) * ρ (φ T) = ρ (φ T) ^ q * ρ (φ Fr) := hrel
    rw [map_inv, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, h0, mul_assoc, mul_inv_cancel,
      mul_one]
  set E := complexEndHom ι r with hE
  -- the linear algebra of Weil II 1.8.4, over `ℂ`
  have hST : E (ρ (φ T))⁻¹ * E (ρ (φ T)) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hTS : E (ρ (φ T)) * E (ρ (φ T))⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hGF : E (ρ (φ Fr)) * E (ρ (φ Fr⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]
  have hFG : E (ρ (φ Fr⁻¹)) * E (ρ (φ Fr)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, map_one]
  have hTF : E (ρ (φ T)) * E (ρ (φ Fr⁻¹)) = E (ρ (φ Fr⁻¹)) * E (ρ (φ T)) ^ q := by
    rw [← map_mul, hrel', map_mul, map_pow]
  have hTv : E (ρ (φ T)) v = v := by
    rw [hE, complexEndHom_apply, Matrix.toLin'_apply]
    exact hvI T (hJI T.2)
  have hFv : E (ρ (φ Fr⁻¹)) v = α • v := by
    rw [hE, complexEndHom_apply, Matrix.toLin'_apply]
    exact hα
  -- a power of `Fr` lies in a given finite intersection of congruence preimages
  have hpow_dvd : ∀ {n : ℕ} {H : Subgroup (GL (Fin n) ℤ_[ℓ])} {g : GL (Fin n) ℤ_[ℓ]} {f₀ d : ℕ},
      g ^ f₀ ∈ H → f₀ ∣ d → g ^ d ∈ H := by
    rintro n H g f₀ d h ⟨c, rfl⟩
    rw [pow_mul]
    exact Subgroup.pow_mem _ h c
  have hkron₂ : ∀ g : G, complexMatrixHom ι (Fin (r * r))
      ((ρ₂ g : GL (Fin (r * r)) ℤ_[ℓ]) : Matrix (Fin (r * r)) (Fin (r * r)) ℤ_[ℓ]) =
      kroneckerMonoidHom
        (complexMatrixHom ι (Fin r) ((ρ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]),
          complexMatrixHom ι (Fin r) ((ρ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ])) :=
    fun g => by rw [← complexMatrixHom_kroneckerMonoidHom]; rfl
  have hkron₃ : ∀ g : G, complexMatrixHom ι (Fin (r * r))
      ((ρ₃ g : GL (Fin (r * r)) ℤ_[ℓ]) : Matrix (Fin (r * r)) (Fin (r * r)) ℤ_[ℓ]) =
      kroneckerMonoidHom
        (complexMatrixHom ι (Fin r)
          ((contragredient ρ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]),
          complexMatrixHom ι (Fin r)
            ((contragredient ρ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ])) :=
    fun g => by rw [← complexMatrixHom_kroneckerMonoidHom]; rfl
  have hcontra : ∀ g : G, (complexMatrixHom ι (Fin r)
      (((ρ g)⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]))ᵀ =
      complexMatrixHom ι (Fin r)
        ((contragredient ρ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := fun g => by
    rw [contragredient_val, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  -- the bound on `‖c‖` from a bound on open subgroups, for `ρ₂` and `ρ₃` alike
  have key : ∀ (ρ' : G →* GL (Fin (r * r)) ℤ_[ℓ]), Continuous ρ' →
      (∀ τ : J, t' τ = 1 → (ρ'.comp φ) τ = 1) → ∀ {Qb : ℝ}, 0 ≤ Qb →
      (∀ O : Subgroup G, IsOpen (O : Set G) → ∀ f : ℕ, 0 < f → φ Fr ^ f ∈ O →
        ∀ Y : Fin (r * r) → ℂ, Y ≠ 0 → (∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
          complexMatrixHom ι _ (ρ' (φ σ)) *ᵥ Y = Y) →
        ∀ c : ℂ, complexMatrixHom ι _ (ρ' (φ Fr⁻¹) ^ f) *ᵥ Y = c • Y → ‖c‖ ≤ Qb ^ f) →
      ∀ m : ℕ, 0 < m → ∀ (Y : Fin (r * r) → ℂ), Y ≠ 0 → ∀ c : ℂ,
      complexMatrixHom ι _ (ρ' (φ T ^ m)) *ᵥ Y = Y →
      complexMatrixHom ι _ (ρ' (φ Fr⁻¹)) *ᵥ Y = c • Y → ‖c‖ ≤ Qb := by
    intro ρ' hρ'c hker' Qb hQb Hb m hm Y hY0 c hTY hFY
    obtain ⟨N, hN⟩ := exists_forall_mulVec_eq_of_pow_mulVec_eq (ρ := ρ'.comp φ) (hρ'c.comp hφ)
      t' ht' hker' T hgen hm
    let O : Subgroup G := (congruenceSubgroup ℓ (r * r) N).comap ρ' ⊓
      (congruenceSubgroup ℓ r 1).comap ρ ⊓ (congruenceSubgroup ℓ (r * r) 1).comap ρ₂ ⊓
      (congruenceSubgroup ℓ (r * r) 1).comap ρ₃
    have hO : IsOpen (O : Set G) :=
      ((((isOpen_congruenceSubgroup N).preimage hρ'c).inter
        ((isOpen_congruenceSubgroup 1).preimage hρ)).inter
        ((isOpen_congruenceSubgroup 1).preimage hρ₂c)).inter
        ((isOpen_congruenceSubgroup 1).preimage hρ₃c)
    obtain ⟨f₁, hf₁, h₁⟩ := exists_pow_mem_congruenceSubgroup (ρ' (φ Fr)) N
    obtain ⟨f₂, hf₂, h₂⟩ := exists_pow_mem_congruenceSubgroup (ρ (φ Fr)) 1
    obtain ⟨f₃, hf₃, h₃⟩ := exists_pow_mem_congruenceSubgroup (ρ₂ (φ Fr)) 1
    obtain ⟨f₄, hf₄, h₄⟩ := exists_pow_mem_congruenceSubgroup (ρ₃ (φ Fr)) 1
    have hf : 0 < f₁ * f₂ * f₃ * f₄ := by positivity
    have hFrO : φ Fr ^ (f₁ * f₂ * f₃ * f₄) ∈ O := by
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · change ρ' (φ Fr ^ (f₁ * f₂ * f₃ * f₄)) ∈ congruenceSubgroup ℓ (r * r) N
        rw [map_pow]; exact hpow_dvd h₁ ⟨f₂ * f₃ * f₄, by ring⟩
      · change ρ (φ Fr ^ (f₁ * f₂ * f₃ * f₄)) ∈ congruenceSubgroup ℓ r 1
        rw [map_pow]; exact hpow_dvd h₂ ⟨f₁ * f₃ * f₄, by ring⟩
      · change ρ₂ (φ Fr ^ (f₁ * f₂ * f₃ * f₄)) ∈ congruenceSubgroup ℓ (r * r) 1
        rw [map_pow]; exact hpow_dvd h₃ ⟨f₁ * f₂ * f₄, by ring⟩
      · change ρ₃ (φ Fr ^ (f₁ * f₂ * f₃ * f₄)) ∈ congruenceSubgroup ℓ (r * r) 1
        rw [map_pow]; exact hpow_dvd h₄ ⟨f₁ * f₂ * f₃, by ring⟩
    have hinv : ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
        complexMatrixHom ι _ (ρ' (φ σ)) *ᵥ Y = Y := by
      intro σ hσI hσO
      have hσJ : σ ∈ J := ⟨⟨⟨hσI, hσO.1.1.2⟩, hσO.1.2⟩, hσO.2⟩
      refine mulVec_map_eq_self_of_forall_integral ι (hN ⟨σ, hσJ⟩ hσO.1.1.1) Y ?_
      rwa [MonoidHom.comp_apply, ← map_pow]
    have hcf := Hb O hO _ hf hFrO Y hY0 hinv (c ^ (f₁ * f₂ * f₃ * f₄)) (by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_mulVec_eq_pow_smul hFY _)
    rw [norm_pow] at hcf
    exact (pow_le_pow_iff_left₀ (norm_nonneg c) hQb hf.ne').1 hcf
  have hHlin : ∀ m : ℕ, 0 < m → ∀ (X : (Fin r → ℂ) ⊗[ℂ] (Fin r → ℂ)) (c : ℂ), X ≠ 0 →
      TensorProduct.map (E (ρ (φ T)) ^ m) (E (ρ (φ T)) ^ m) X = X →
      TensorProduct.map (E (ρ (φ Fr⁻¹))) (E (ρ (φ Fr⁻¹))) X = c • X → ‖(RingHom.id ℂ) c‖ ≤ Q := by
    intro m hm X c hX hTX hFX
    set Y := tensorFinEquiv X with hYdef
    have hY0 : Y ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hX
    rw [← map_pow E, ← map_pow ρ, hE, complexEndHom_apply] at hTX
    rw [hE, complexEndHom_apply] at hFX
    have hTY : complexMatrixHom ι _ (ρ₂ (φ T ^ m)) *ᵥ Y = Y := by
      have := congrArg tensorFinEquiv hTX
      rwa [tensorFinEquiv_map, ← hkron₂] at this
    have hFY : complexMatrixHom ι _ (ρ₂ (φ Fr⁻¹)) *ᵥ Y = c • Y := by
      have := congrArg tensorFinEquiv hFX
      rwa [tensorFinEquiv_map, LinearEquiv.map_smul, ← hkron₂] at this
    exact key ρ₂ hρ₂c hker₂ hQ H m hm Y hY0 c hTY hFY
  have hH'lin : ∀ m : ℕ, 0 < m → ∀ (X : Module.Dual ℂ (Fin r → ℂ) ⊗[ℂ] Module.Dual ℂ (Fin r → ℂ))
      (c : ℂ), X ≠ 0 →
      TensorProduct.map (E (ρ (φ T))⁻¹ ^ m).dualMap (E (ρ (φ T))⁻¹ ^ m).dualMap X = X →
      TensorProduct.map (E (ρ (φ Fr))).dualMap (E (ρ (φ Fr))).dualMap X = c • X →
        ‖(RingHom.id ℂ) c‖ ≤ Q' := by
    intro m hm X c hX hTX hFX
    set Y := dualTensorFinEquiv X with hYdef
    have hY0 : Y ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hX
    have e1 : (ρ (φ T))⁻¹ ^ m = (ρ (φ T ^ m))⁻¹ := by rw [map_pow, inv_pow]
    have e2 : ρ (φ Fr) = (ρ (φ Fr⁻¹))⁻¹ := by rw [map_inv, map_inv, inv_inv]
    rw [← map_pow E, e1, hE, complexEndHom_apply] at hTX
    rw [e2, hE, complexEndHom_apply] at hFX
    have hTY : complexMatrixHom ι _ (ρ₃ (φ T ^ m)) *ᵥ Y = Y := by
      have := congrArg dualTensorFinEquiv hTX
      rwa [dualTensorFinEquiv_map, hcontra, ← hkron₃] at this
    have hFY : complexMatrixHom ι _ (ρ₃ (φ Fr⁻¹)) *ᵥ Y = c • Y := by
      have := congrArg dualTensorFinEquiv hFX
      rwa [dualTensorFinEquiv_map, LinearEquiv.map_smul, hcontra, ← hkron₃] at this
    exact key ρ₃ hρ₃c hker₃ hQ' H' m hm Y hY0 c hTY hFY
  obtain ⟨i, hi⟩ := exists_norm_sq_mul_pow_eq_of_tame_monodromy (RingHom.id ℂ) hST hTS hGF hFG hq
    hTF hQQ' hHlin hH'lin hv0 hTv hFv
  refine ⟨i, ?_⟩
  simpa using hi

end Stacks.EtaleCohomology

end
