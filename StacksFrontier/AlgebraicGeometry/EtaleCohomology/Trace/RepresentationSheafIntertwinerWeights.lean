module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel

/-!
# Weights of `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` along intertwiners of representations

Let `ρ₁`, `ρ₂` be continuous `ℤ_ℓ`-representations of `π₁(X, x̄)` and `A : ρ₁ → ρ₂`,
`A' : ρ₂ → ρ₁` intertwiners with `A' A = ℓ ^ M`.  Then `ℱ_A : ℱ_{ρ₁} → ℱ_{ρ₂}` induces an
injection on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` commuting with the geometric Frobenius `π_X^*`, because
`ℱ_{A'} ∘ ℱ_A` is multiplication by `ℓ ^ M`, which is invertible rationally.  Hence every
characteristic root of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_{ρ₁} ⊗ ℚ_ℓ)` is one on
`Hⁱ_c(X_k̄, ℱ_{ρ₂} ⊗ ℚ_ℓ)`.  This covers a direct summand (`A' A = 1`) and two lattices in the
same `ℚ_ℓ`-representation (`A` and `A'` scaled inverse matrices), which is how weights of the
`ℚ_ℓ`-sheaf `ℱ_ρ ⊗ ℚ_ℓ` are independent of the chosen integral model.

## Main results

* `Stacks.EtaleCohomology.representationLAdicSheafMap_natCast_smul_one`: `ℱ_{N • 1} = N • 𝟙`.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_representationLAdicSheaf_of_intertwiner`.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_representationSheaf_of_intertwiner`: the
  same for continuous `ℚ_ℓ`-representations and their sheaves `ℱ_ρ`, given `ℚ_ℓ`-intertwiners
  `A`, `A'` with `A' A = 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}

/-- A `ℚ_ℓ`-matrix becomes integral after multiplication by a power of `ℓ`. -/
public theorem exists_pow_mul_norm_le_one {α β : Type*} [Finite α] [Finite β]
    (C : Matrix α β ℚ_[ℓ]) : ∃ m : ℕ, ∀ i j, ‖(ℓ : ℚ_[ℓ]) ^ m * C i j‖ ≤ 1 := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hone : ∀ x : ℚ_[ℓ], ∃ m : ℕ, ‖(ℓ : ℚ_[ℓ]) ^ m * x‖ ≤ 1 := fun x => by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖x‖ hℓ
    refine ⟨m, ?_⟩
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast,
      inv_mul_le_iff₀ (pow_pos (by linarith) m), mul_one]
    exact hm.le
  choose m hm using hone
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  refine ⟨Finset.univ.sup fun ij : α × β => m (C ij.1 ij.2), fun i j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
    (Finset.le_sup (f := fun ij : α × β => m (C ij.1 ij.2)) (Finset.mem_univ (i, j)))
  rw [hc, pow_add, mul_comm ((ℓ : ℚ_[ℓ]) ^ m (C i j)), mul_assoc, norm_mul]
  have hc1 : ‖(ℓ : ℚ_[ℓ]) ^ c‖ ≤ 1 := by
    rw [Padic.norm_p_pow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hℓ.le)
  exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans (hm _)

/-- Cancelling a unit matrix against its inverse on a rectangular matrix. -/
private theorem units_mul_inv_mul_cancel {R : Type*} [CommRing R] {a b : ℕ}
    (P : (Matrix (Fin a) (Fin a) R)ˣ) (Y : Matrix (Fin a) (Fin b) R) :
    P.val * (P⁻¹.val * Y) = Y := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

/-- Two `ℤ_ℓ`-matrices are equal if their images in `ℚ_ℓ` are. -/
private theorem eq_of_map_coe_eq {ℓ : ℕ} [Fact ℓ.Prime] {a b : Type*} {C D : Matrix a b ℤ_[ℓ]}
    (h : C.map (PadicInt.Coe.ringHom (p := ℓ)) = D.map (PadicInt.Coe.ringHom (p := ℓ))) :
    C = D :=
  Matrix.map_injective (fun _ _ h => PadicInt.ext h) h

/-- A scalar matrix commutes with every matrix. -/
private theorem smul_one_mul_comm {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (c : R) (M : Matrix a b R) :
    (c • (1 : Matrix a a R)) * M = M * (c • (1 : Matrix b b R)) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- Conjugating an intertwiner: if `A R₁ = R₂ A`, then `P₂⁻¹ A P₁` intertwines `P₁⁻¹ R₁ P₁` and
`P₂⁻¹ R₂ P₂`. -/
public theorem conj_mul_conj_eq_of_mul_eq {R : Type*} [CommRing R] {a b : ℕ}
    (P₁ : (Matrix (Fin a) (Fin a) R)ˣ) (P₂ : (Matrix (Fin b) (Fin b) R)ˣ)
    {A : Matrix (Fin b) (Fin a) R} {R₁ : Matrix (Fin a) (Fin a) R} {R₂ : Matrix (Fin b) (Fin b) R}
    (h : A * R₁ = R₂ * A) :
    (P₂⁻¹.val * A * P₁.val) * (P₁⁻¹.val * R₁ * P₁.val) =
      (P₂⁻¹.val * R₂ * P₂.val) * (P₂⁻¹.val * A * P₁.val) := by
  simp only [Matrix.mul_assoc, units_mul_inv_mul_cancel]
  rw [← Matrix.mul_assoc A, h, Matrix.mul_assoc]

/-- Conjugating a left inverse: if `A' A = 1`, then `(P₁⁻¹ A' P₂) (P₂⁻¹ A P₁) = 1`. -/
public theorem conj_mul_conj_eq_one {R : Type*} [CommRing R] {a b : ℕ}
    (P₁ : (Matrix (Fin a) (Fin a) R)ˣ) (P₂ : (Matrix (Fin b) (Fin b) R)ˣ)
    {A : Matrix (Fin b) (Fin a) R} {A' : Matrix (Fin a) (Fin b) R} (h : A' * A = 1) :
    (P₁⁻¹.val * A' * P₂.val) * (P₂⁻¹.val * A * P₁.val) = 1 := by
  simp only [Matrix.mul_assoc, units_mul_inv_mul_cancel]
  rw [← Matrix.mul_assoc A', h, Matrix.one_mul, Units.inv_mul]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

section Map

variable {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')

/-- The morphism induced by an intertwiner only depends on the matrix. -/
public theorem representationLAdicSheafMap_eq_of_eq {A A' : Matrix (Fin r') (Fin r) ℤ_[ℓ]}
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (hA' : ∀ g, A' * (ρ g).val = (ρ' g).val * A')
    (h : A = A') :
    representationLAdicSheafMap B X x e hρ hρ' A hA =
      representationLAdicSheafMap B X x e hρ hρ' A' hA' := by
  subst h
  rfl

/-- The zero matrix induces the zero morphism. -/
public theorem representationLAdicSheafMap_zero (h : ∀ g, (0 : Matrix (Fin r') (Fin r) ℤ_[ℓ]) *
    (ρ g).val = (ρ' g).val * 0) :
    representationLAdicSheafMap B X x e hρ hρ' 0 h = 0 := by
  have h0 := representationLAdicSheafMap_add B X x e hρ hρ' 0 0 h h
  rw [representationLAdicSheafMap_eq_of_eq B X x e hρ hρ' _ h (add_zero 0)] at h0
  simpa using h0

/-- **`ℱ_{N • 1} = N • 𝟙`**: the scalar matrix `N` induces multiplication by `N` on `ℱ_ρ`. -/
public theorem representationLAdicSheafMap_natCast_smul_one (N : ℕ)
    (h : ∀ g, ((N : ℤ_[ℓ]) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) * (ρ g).val =
      (ρ g).val * ((N : ℤ_[ℓ]) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]))) :
    representationLAdicSheafMap B X x e hρ hρ ((N : ℤ_[ℓ]) • 1) h =
      N • 𝟙 (representationLAdicSheaf B X x e ρ hρ) := by
  have hs : ∀ c : ℤ_[ℓ], ∀ g, (c • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) * (ρ g).val =
      (ρ g).val * (c • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) := fun c g => smul_one_mul_comm c _
  induction N with
  | zero =>
    rw [representationLAdicSheafMap_eq_of_eq B X x e hρ hρ _ (fun g => by simp)
      (by simp : ((0 : ℕ) : ℤ_[ℓ]) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = 0), zero_nsmul]
    exact representationLAdicSheafMap_zero B X x e hρ hρ _
  | succ N ih =>
    rw [representationLAdicSheafMap_eq_of_eq B X x e hρ hρ _
      (fun g => by rw [Matrix.add_mul, Matrix.mul_add, hs N g, Matrix.one_mul, Matrix.mul_one])
      (show ((N + 1 : ℕ) : ℤ_[ℓ]) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) =
        (N : ℤ_[ℓ]) • 1 + 1 by push_cast; rw [add_smul, one_smul]),
      representationLAdicSheafMap_add B X x e hρ hρ _ _ (hs N) (fun g => by
        rw [Matrix.one_mul, Matrix.mul_one]),
      ih (hs N), representationLAdicSheafMap_one, succ_nsmul]

end Map

section Cohomology

variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fintype k] in
/-- **An intertwiner with a left inverse up to `ℓ ^ M` induces an injection on
`Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` commuting with `π_X^*`.**  For continuous `ℤ_ℓ`-representations `ρ₁`,
`ρ₂` and intertwiners `A : ρ₁ → ρ₂`, `A' : ρ₂ → ρ₁` with `A' A = ℓ ^ M`, the map induced by
`ℱ_A` is injective, because `ℱ_{A'} ∘ ℱ_A` is multiplication by `ℓ ^ M`, and commutes with the
geometric Frobenius
(`LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius`). -/
public theorem injective_rationalCohomologyMap_representationLAdicSheafMap
    {r₁ r₂ : ℕ} {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℤ_[ℓ]} (hρ₁ : Continuous ρ₁)
    {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℤ_[ℓ]} (hρ₂ : Continuous ρ₂)
    (A : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (A' : Matrix (Fin r₁) (Fin r₂) ℤ_[ℓ]) (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₁ g).val * A')
    (M : ℕ) (hM : A' * A = ((ℓ ^ M : ℕ) : ℤ_[ℓ]) • 1) (i : ℤ) :
    Function.Injective ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
          (representationLAdicSheafMap B X x e hρ₁ hρ₂ A hA) i)).hom := by
  let E := ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])
  have : E.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).left_adjoint_additive
  set φ := representationLAdicSheafMap B X x e hρ₁ hρ₂ A hA
  set ψ := representationLAdicSheafMap B X x e hρ₂ hρ₁ A' hA'
  have hφψ : φ ≫ ψ = (ℓ ^ M) • 𝟙 (representationLAdicSheaf B X x e ρ₁ hρ₁) := by
    rw [← representationLAdicSheafMap_mul, representationLAdicSheafMap_eq_of_eq B X x e hρ₁ hρ₁ _
      (fun g => smul_one_mul_comm _ _) hM,
      representationLAdicSheafMap_natCast_smul_one]
  have hc : E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i) ≫
      E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i) =
      (ℓ ^ M) • 𝟙 _ := by
    rw [← E.map_comp, ← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, hφψ,
      LAdicSheaf.geometricCompactlySupportedCohomologyMap_nsmul_id, E.map_nsmul, E.map_id]
  intro v w hvw
  have h := congrArg (E.map (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i)).hom
    hvw
  have hv := ConcreteCategory.congr_hom hc v
  have hw := ConcreteCategory.congr_hom hc w
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hv hw
  change _ = (ℓ ^ M) • v at hv
  change _ = (ℓ ^ M) • w at hw
  have h' : ((ℓ ^ M : ℕ) : ℚ_[ℓ]) • v = ((ℓ ^ M : ℕ) : ℚ_[ℓ]) • w := by
    rwa [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← hv, ← hw]
  exact smul_right_injective _ (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) h'

/-- **Weights along an intertwiner with a left inverse up to `ℓ ^ M`.**  For continuous
`ℤ_ℓ`-representations `ρ₁`, `ρ₂` and intertwiners `A : ρ₁ → ρ₂`, `A' : ρ₂ → ρ₁` with
`A' A = ℓ ^ M`, if the characteristic roots of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_{ρ₂} ⊗ ℚ_ℓ)` have
absolute values `q ^ (w / 2)` with `w ≤ b`, so do those on `Hⁱ_c(X_k̄, ℱ_{ρ₁} ⊗ ℚ_ℓ)`. -/
public theorem isCharpolyNormMixedOfWeightLE_representationLAdicSheaf_of_intertwiner
    {r₁ r₂ : ℕ} {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℤ_[ℓ]} (hρ₁ : Continuous ρ₁)
    {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℤ_[ℓ]} (hρ₂ : Continuous ρ₂)
    (A : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (A' : Matrix (Fin r₁) (Fin r₂) ℤ_[ℓ]) (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₁ g).val * A')
    (M : ℕ) (hM : A' * A = ((ℓ ^ M : ℕ) : ℤ_[ℓ]) • 1) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (representationLAdicSheaf B X x e ρ₁ hρ₁) i)]
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (representationLAdicSheaf B X x e ρ₂ hρ₂) i)]
    {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (h₂ : IsCharpolyNormMixedOfWeightLE q ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
        (representationLAdicSheaf B X x e ρ₂ hρ₂) i).hom) :
    IsCharpolyNormMixedOfWeightLE q ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
        (representationLAdicSheaf B X x e ρ₁ hρ₁) i).hom := by
  refine IsCharpolyNormMixedOfWeightLE.of_injective h₂ (fun a => ?_)
    (injective_rationalCohomologyMap_representationLAdicSheafMap B X x e f j kbar hρ₁ hρ₂ A hA A'
      hA' M hM i)
  have h := congrArg (fun t => ((ModuleCat.extendScalars.{0, 0, u + 1}
    (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map t).hom a)
    (LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius f j kbar p n hcard
      (representationLAdicSheafMap B X x e hρ₁ hρ₂ A hA) i)
  simp only [Functor.map_comp, ModuleCat.hom_comp] at h
  exact h.symm

omit [Fintype k] in
/-- **Finite dimensionality along an intertwiner with a left inverse up to `ℓ ^ M`.** -/
public theorem finiteDimensional_representationLAdicSheaf_of_intertwiner
    {r₁ r₂ : ℕ} {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℤ_[ℓ]} (hρ₁ : Continuous ρ₁)
    {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℤ_[ℓ]} (hρ₂ : Continuous ρ₂)
    (A : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (A' : Matrix (Fin r₁) (Fin r₂) ℤ_[ℓ]) (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₁ g).val * A')
    (M : ℕ) (hM : A' * A = ((ℓ ^ M : ℕ) : ℤ_[ℓ]) • 1) (i : ℤ)
    (h₂ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (representationLAdicSheaf B X x e ρ₂ hρ₂) i)) :
    FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (representationLAdicSheaf B X x e ρ₁ hρ₁) i) :=
  @FiniteDimensional.of_injective _ _ _ _ _ _ _ _ _
    (injective_rationalCohomologyMap_representationLAdicSheafMap B X x e f j kbar hρ₁ hρ₂ A hA A'
      hA' M hM i) h₂

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The lift to `ℤ_ℓ` of an intertwiner of two integral conjugates, after clearing
denominators: if the `ℤ_ℓ`-representations `ρᵢ` are `Pᵢ⁻¹ σᵢ Pᵢ` over `ℚ_ℓ` and `A` intertwines
`σ₁` and `σ₂`, then `ℓ ^ m P₂⁻¹ A P₁` is integral for large `m` and intertwines `ρ₁` and `ρ₂`. -/
public theorem exists_intertwiner_of_map_eq {G : Type*} [Group G] {r₁ r₂ : ℕ}
    {σ₁ : G →* GL (Fin r₁) ℚ_[ℓ]} {σ₂ : G →* GL (Fin r₂) ℚ_[ℓ]}
    {ρ₁ : G →* GL (Fin r₁) ℤ_[ℓ]} {ρ₂ : G →* GL (Fin r₂) ℤ_[ℓ]}
    (P₁ : GL (Fin r₁) ℚ_[ℓ]) (P₂ : GL (Fin r₂) ℚ_[ℓ])
    (h₁ : ∀ g, (ρ₁ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) = (P₁⁻¹ * σ₁ g * P₁).val)
    (h₂ : ∀ g, (ρ₂ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) = (P₂⁻¹ * σ₂ g * P₂).val)
    (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) (hA : ∀ g, A * (σ₁ g).val = (σ₂ g).val * A) :
    ∃ (m : ℕ) (Ã : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ]),
      Ã.map (PadicInt.Coe.ringHom (p := ℓ)) = (ℓ : ℚ_[ℓ]) ^ m • (P₂⁻¹.val * A * P₁.val) ∧
      ∀ g, Ã * (ρ₁ g).val = (ρ₂ g).val * Ã := by
  set C : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ] := P₂⁻¹.val * A * P₁.val
  obtain ⟨m, hm⟩ := exists_pow_mul_norm_le_one (ℓ := ℓ) C
  let Ã : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ] := Matrix.of fun i j => ⟨_, hm i j⟩
  have hÃ : Ã.map (PadicInt.Coe.ringHom (p := ℓ)) = (ℓ : ℚ_[ℓ]) ^ m • C := by
    ext i j
    rfl
  refine ⟨m, Ã, hÃ, fun g => ?_⟩
  apply eq_of_map_coe_eq
  simp only [Matrix.map_mul]
  rw [hÃ, h₁, h₂, Matrix.smul_mul, Matrix.mul_smul, Units.val_mul, Units.val_mul,
    Units.val_mul, Units.val_mul]
  exact congrArg _ (conj_mul_conj_eq_of_mul_eq P₁ P₂ (hA g))

/-- **Weights along an intertwiner of integral conjugates.**  For continuous
`ℤ_ℓ`-representations `ρᵢ` which are `Pᵢ⁻¹ σᵢ Pᵢ` over `ℚ_ℓ`, and `ℚ_ℓ`-intertwiners
`A : σ₁ → σ₂`, `A' : σ₂ → σ₁` with `A' A = 1`, the characteristic roots of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_{ρ₁} ⊗ ℚ_ℓ)` are among those on `Hⁱ_c(X_k̄, ℱ_{ρ₂} ⊗ ℚ_ℓ)`, and the former is
finite dimensional if the latter is. -/
public theorem isCharpolyNormMixedOfWeightLE_representationLAdicSheaf_of_map_eq
    {r₁ r₂ : ℕ} {σ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℚ_[ℓ]}
    {σ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℚ_[ℓ]}
    {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℤ_[ℓ]} (hρ₁ : Continuous ρ₁)
    {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℤ_[ℓ]} (hρ₂ : Continuous ρ₂)
    (P₁ : GL (Fin r₁) ℚ_[ℓ]) (P₂ : GL (Fin r₂) ℚ_[ℓ])
    (h₁ : ∀ g, (ρ₁ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) = (P₁⁻¹ * σ₁ g * P₁).val)
    (h₂ : ∀ g, (ρ₂ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) = (P₂⁻¹ * σ₂ g * P₂).val)
    (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) (hA : ∀ g, A * (σ₁ g).val = (σ₂ g).val * A)
    (A' : Matrix (Fin r₁) (Fin r₂) ℚ_[ℓ]) (hA' : ∀ g, A' * (σ₂ g).val = (σ₁ g).val * A')
    (hAA : A' * A = 1) (i : ℤ)
    (hfd : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (representationLAdicSheaf B X x e ρ₂ hρ₂) i)) :
    ∃ _ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (representationLAdicSheaf B X x e ρ₁ hρ₁) i),
      ∀ {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}, IsCharpolyNormMixedOfWeightLE q ι b
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
          (representationLAdicSheaf B X x e ρ₂ hρ₂) i).hom →
      IsCharpolyNormMixedOfWeightLE q ι b
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
          (representationLAdicSheaf B X x e ρ₁ hρ₁) i).hom := by
  obtain ⟨m, Ã, hÃ, hÃi⟩ := exists_intertwiner_of_map_eq P₁ P₂ h₁ h₂ A hA
  obtain ⟨m', Ã', hÃ', hÃ'i⟩ := exists_intertwiner_of_map_eq P₂ P₁ h₂ h₁ A' hA'
  have hM : Ã' * Ã = ((ℓ ^ (m' + m) : ℕ) : ℤ_[ℓ]) • 1 := by
    apply eq_of_map_coe_eq
    simp only [Matrix.map_mul]
    rw [hÃ, hÃ', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
    have h1 : ((((ℓ ^ (m' + m) : ℕ) : ℤ_[ℓ]) • (1 : Matrix (Fin r₁) (Fin r₁) ℤ_[ℓ]))).map
        (PadicInt.Coe.ringHom (p := ℓ)) = (ℓ : ℚ_[ℓ]) ^ (m' + m) • 1 := by
      ext a c
      by_cases hac : a = c <;> simp [hac]
    rw [h1, conj_mul_conj_eq_one _ _ hAA]
  have := finiteDimensional_representationLAdicSheaf_of_intertwiner B X x e f j kbar hρ₁ hρ₂ Ã hÃi
    Ã' hÃ'i (m' + m) hM i hfd
  exact ⟨this, fun h => isCharpolyNormMixedOfWeightLE_representationLAdicSheaf_of_intertwiner B X x
    e f j kbar p n hcard hρ₁ hρ₂ Ã hÃi Ã' hÃ'i (m' + m) hM i h⟩

/-- **Weights along an intertwiner of `ℚ_ℓ`-representations with a left inverse.**  For
continuous `ρ₁ : π₁(X, x̄) → GL_{r₁}(ℚ_ℓ)`, `ρ₂ : π₁(X, x̄) → GL_{r₂}(ℚ_ℓ)` and intertwiners
`A : ρ₁ → ρ₂`, `A' : ρ₂ → ρ₁` with `A' A = 1` (a direct summand; a conjugation; a reindexing), if
the characteristic roots of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_{ρ₂} ⊗ ℚ_ℓ)` have absolute values
`q ^ (w / 2)` with `w ≤ b`, so do those on `Hⁱ_c(X_k̄, ℱ_{ρ₁} ⊗ ℚ_ℓ)`. -/
public theorem isCharpolyNormMixedOfWeightLE_representationSheaf_of_intertwiner
    {r₁ r₂ : ℕ} {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℚ_[ℓ]} (hρ₁ : Continuous ρ₁)
    {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℚ_[ℓ]} (hρ₂ : Continuous ρ₂)
    (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (A' : Matrix (Fin r₁) (Fin r₂) ℚ_[ℓ]) (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₁ g).val * A')
    (hAA : A' * A = 1) (i : ℤ)
    [_h₁ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (LAdicSheaf.representationSheaf B X x ρ₁ hρ₁) i)]
    [h₂' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (LAdicSheaf.representationSheaf B X x ρ₂ hρ₂) i)]
    {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (h₂ : IsCharpolyNormMixedOfWeightLE q ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
        (LAdicSheaf.representationSheaf B X x ρ₂ hρ₂) i).hom) :
    IsCharpolyNormMixedOfWeightLE q ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
        (LAdicSheaf.representationSheaf B X x ρ₁ hρ₁) i).hom := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  exact (isCharpolyNormMixedOfWeightLE_representationLAdicSheaf_of_map_eq B X x _ f j kbar p n hcard
    (continuous_integralModel ρ₁ hρ₁) (continuous_integralModel ρ₂ hρ₂) _ _
    (fun g => congrArg Units.val (map_integralModel ρ₁ hρ₁ g))
    (fun g => congrArg Units.val (map_integralModel ρ₂ hρ₂ g)) A hA A' hA' hAA i h₂').2 h₂

end Cohomology

end Stacks.EtaleCohomology

end
