module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafIntertwinerWeights

/-!
# Rational intertwiners act on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)`

For continuous `ρ₁ : π₁(X, x̄) → GL_{r₁}(ℚ_ℓ)`, `ρ₂ : π₁(X, x̄) → GL_{r₂}(ℚ_ℓ)` and a
`ℚ_ℓ`-intertwiner `A : ρ₁ → ρ₂` (`A ρ₁ = ρ₂ A`), the matrix `ℓᴺ P₂⁻¹ A P₁` is, for `N` large, an
integral intertwiner of the integral models `Pᵢ⁻¹ ρᵢ Pᵢ` of which the sheaves `ℱ_{ρᵢ}` are built;
its morphism of sheaves, divided by `ℓᴺ` on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`, is the map
`Stacks.EtaleCohomology.rationalIntertwinerCohomologyMap A`, which does not depend on `N`, by
`Stacks.EtaleCohomology.integralIntertwinerCohomologyMap_eq_smul_rationalIntertwinerCohomologyMap`.
It is functorial and additive in `A`, commutes with `π_X^*`, and for the commutant sheaves of
`Stacks.EtaleCohomology.representationSheafCommutantCoefficientSheaf` it recovers the action of
`E` (`Stacks.EtaleCohomology.rationalRingHom_representationSheafCommutantCoefficientSheaf`): the
action of `e ∈ E` on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` is the map of the intertwiner `α(e)`.  So the
cohomology of `ℱ_ρ ⊗ ℚ_ℓ` is a functor of the `ℚ_ℓ`-representation `ρ`, compatibly with the
coefficients: this is how direct sums and extensions of the coefficient field are read on the
fibres of Laumon's family in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.integralIntertwinerCohomologyMap`.
* `Stacks.EtaleCohomology.rationalIntertwinerCohomologyMap`.

## Main results

* `Stacks.EtaleCohomology.rationalIntertwinerCohomologyMap_one`,
  `Stacks.EtaleCohomology.rationalIntertwinerCohomologyMap_mul`,
  `Stacks.EtaleCohomology.rationalIntertwinerCohomologyMap_add`,
  `Stacks.EtaleCohomology.rationalIntertwinerCohomologyMap_frobenius`.
* `Stacks.EtaleCohomology.rationalRingHom_representationSheafCommutantCoefficientSheaf`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)
  {r₁ r₂ r₃ : ℕ}

/-- Multiplication by a power of `ℓ` is injective on a `ℚ_ℓ`-vector space. -/
theorem eq_of_pow_smul_eq_pow_smul {M : Type*} [AddCommGroup M] [Module ℚ_[ℓ] M] (N : ℕ)
    {v w : M} (h : ((ℓ : ℚ_[ℓ]) ^ N) • v = ((ℓ : ℚ_[ℓ]) ^ N) • w) : v = w := by
  have hne : ((ℓ : ℚ_[ℓ]) ^ N) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  have h' := congrArg (fun t => ((ℓ : ℚ_[ℓ]) ^ N)⁻¹ • t) h
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using h'

/-- Products of matrices intertwining `T₁ → T₂` and `T₂ → T₃` intertwine `T₁ → T₃`. -/
private theorem intertwines_mul {R G : Type*} [Semiring R]
    {T₁ : G → Matrix (Fin r₁) (Fin r₁) R} {T₂ : G → Matrix (Fin r₂) (Fin r₂) R}
    {T₃ : G → Matrix (Fin r₃) (Fin r₃) R} {L : Matrix (Fin r₂) (Fin r₁) R}
    {L' : Matrix (Fin r₃) (Fin r₂) R} (hL : ∀ g, L * T₁ g = T₂ g * L)
    (hL' : ∀ g, L' * T₂ g = T₃ g * L') (g : G) : L' * L * T₁ g = T₃ g * (L' * L) := by
  rw [Matrix.mul_assoc, hL, ← Matrix.mul_assoc, hL', Matrix.mul_assoc]

/-- Sums of matrices intertwining `T₁ → T₂` intertwine `T₁ → T₂`. -/
private theorem intertwines_add {R G : Type*} [Semiring R] {T₁ : G → Matrix (Fin r₁) (Fin r₁) R}
    {T₂ : G → Matrix (Fin r₂) (Fin r₂) R} {L L' : Matrix (Fin r₂) (Fin r₁) R}
    (hL : ∀ g, L * T₁ g = T₂ g * L) (hL' : ∀ g, L' * T₁ g = T₂ g * L') (g : G) :
    (L + L') * T₁ g = T₂ g * (L + L') := by
  rw [Matrix.add_mul, Matrix.mul_add, hL, hL']

/-- Scalar multiples of a matrix intertwining `T₁ → T₂` intertwine `T₁ → T₂`. -/
private theorem intertwines_smul {R G : Type*} [CommSemiring R]
    {T₁ : G → Matrix (Fin r₁) (Fin r₁) R} {T₂ : G → Matrix (Fin r₂) (Fin r₂) R}
    {L : Matrix (Fin r₂) (Fin r₁) R} (c : R) (hL : ∀ g, L * T₁ g = T₂ g * L) (g : G) :
    (c • L) * T₁ g = T₂ g * (c • L) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, hL]

/-- The identity matrix intertwines `T → T`. -/
private theorem intertwines_one {R G : Type*} [Semiring R] (T : G → Matrix (Fin r₁) (Fin r₁) R)
    (g : G) : (1 : Matrix (Fin r₁) (Fin r₁) R) * T g = T g * 1 := by
  rw [Matrix.one_mul, Matrix.mul_one]

/-- The zero matrix intertwines `T₁ → T₂`. -/
private theorem intertwines_zero {R G : Type*} [Semiring R] (T₁ : G → Matrix (Fin r₁) (Fin r₁) R)
    (T₂ : G → Matrix (Fin r₂) (Fin r₂) R) (g : G) :
    (0 : Matrix (Fin r₂) (Fin r₁) R) * T₁ g = T₂ g * (0 : Matrix (Fin r₂) (Fin r₁) R) := by
  rw [Matrix.zero_mul, Matrix.mul_zero]

/-! ### Integral intertwiners -/

section Integral

variable {τ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℤ_[ℓ]} (hτ₁ : Continuous τ₁)
  {τ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℤ_[ℓ]} (hτ₂ : Continuous τ₂)
  {τ₃ : EtaleFundamentalGroup X.1 x →* GL (Fin r₃) ℤ_[ℓ]} (hτ₃ : Continuous τ₃)

/-- **The map on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` of an integral intertwiner** `L : τ₁ → τ₂`: the
extension of scalars of the map induced by the morphism of sheaves `ℱ_L : ℱ_{τ₁} → ℱ_{τ₂}`. -/
def integralIntertwinerCohomologyMap (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hL : ∀ g, L * (τ₁ g).val = (τ₂ g).val * L) :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          τ₁ hτ₁) i →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          τ₂ hτ₂) i :=
  ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
      (representationLAdicSheafMap B X x _ hτ₁ hτ₂ L hL) i)).hom

/-- Equal integral intertwiners induce equal maps on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`. -/
theorem integralIntertwinerCohomologyMap_congr {L L' : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ]}
    (hL : ∀ g, L * (τ₁ g).val = (τ₂ g).val * L) (hL' : ∀ g, L' * (τ₁ g).val = (τ₂ g).val * L')
    (h : L = L') :
    integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L hL =
      integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L' hL' := by
  subst h
  rfl

/-- The identity matrix induces the identity of `Hⁱ_c(X_k̄, ℱ_τ ⊗ ℚ_ℓ)`. -/
theorem integralIntertwinerCohomologyMap_one :
    integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₁ 1
      (fun g => by rw [Matrix.one_mul, Matrix.mul_one]) = LinearMap.id := by
  rw [integralIntertwinerCohomologyMap, representationLAdicSheafMap_one,
    LAdicSheaf.geometricCompactlySupportedCohomologyMap_id, CategoryTheory.Functor.map_id]
  rfl

/-- The map of a product `L' * L` of integral intertwiners is the composite of their maps. -/
theorem integralIntertwinerCohomologyMap_mul (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hL : ∀ g, L * (τ₁ g).val = (τ₂ g).val * L) (L' : Matrix (Fin r₃) (Fin r₂) ℤ_[ℓ])
    (hL' : ∀ g, L' * (τ₂ g).val = (τ₃ g).val * L') :
    integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₃ (L' * L)
        (fun g => by rw [Matrix.mul_assoc, hL, ← Matrix.mul_assoc, hL', Matrix.mul_assoc]) =
      (integralIntertwinerCohomologyMap B X x f j kbar i hτ₂ hτ₃ L' hL').comp
        (integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L hL) := by
  rw [integralIntertwinerCohomologyMap, representationLAdicSheafMap_mul,
    LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- The map of a sum `L + L'` of integral intertwiners is the sum of their maps. -/
theorem integralIntertwinerCohomologyMap_add (L L' : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hL : ∀ g, L * (τ₁ g).val = (τ₂ g).val * L) (hL' : ∀ g, L' * (τ₁ g).val = (τ₂ g).val * L') :
    integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ (L + L')
        (fun g => by rw [Matrix.add_mul, Matrix.mul_add, hL, hL']) =
      integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L hL +
        integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L' hL' := by
  have : (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).left_adjoint_additive
  rw [integralIntertwinerCohomologyMap, representationLAdicSheafMap_add,
    LAdicSheaf.geometricCompactlySupportedCohomologyMap_add, CategoryTheory.Functor.map_add]
  rfl

/-- The map of `N • L` is `N` times the map of `L`. -/
theorem integralIntertwinerCohomologyMap_natCast_smul (N : ℕ) (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hL : ∀ g, L * (τ₁ g).val = (τ₂ g).val * L) :
    integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ ((N : ℤ_[ℓ]) • L)
        (fun g => by rw [Matrix.smul_mul, Matrix.mul_smul, hL]) =
      (N : ℚ_[ℓ]) • integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L hL := by
  have : (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).left_adjoint_additive
  have hs := intertwines_smul (N : ℤ_[ℓ]) (intertwines_one fun g => (τ₂ g).val)
  rw [integralIntertwinerCohomologyMap_congr B X x f j kbar i hτ₁ hτ₂ _ (intertwines_mul hL hs)
      (show (N : ℤ_[ℓ]) • L = ((N : ℤ_[ℓ]) • (1 : Matrix (Fin r₂) (Fin r₂) ℤ_[ℓ])) * L by
        rw [Matrix.smul_mul, Matrix.one_mul]),
    integralIntertwinerCohomologyMap_mul B X x f j kbar i hτ₁ hτ₂ hτ₂ L hL _ hs]
  rw [integralIntertwinerCohomologyMap, representationLAdicSheafMap_natCast_smul_one,
    LAdicSheaf.geometricCompactlySupportedCohomologyMap_nsmul_id, CategoryTheory.Functor.map_nsmul,
    CategoryTheory.Functor.map_id]
  ext v
  simp only [ModuleCat.hom_nsmul, LinearMap.smul_apply, ModuleCat.hom_id]
  exact (Nat.cast_smul_eq_nsmul ℚ_[ℓ] N _).symm

/-- The map of an integral intertwiner commutes with every `π_X^*`. -/
theorem integralIntertwinerCohomologyMap_frobenius (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hL : ∀ g, L * (τ₁ g).val = (τ₂ g).val * L)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        τ₁ hτ₁) i) :
    integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L hL
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (representationLAdicSheaf B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) τ₁ hτ₁) i).hom v) =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (representationLAdicSheaf B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) τ₂ hτ₂) i).hom
        (integralIntertwinerCohomologyMap B X x f j kbar i hτ₁ hτ₂ L hL v) := by
  have h := congrArg
    (fun t => ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map t).hom v)
    (LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius f j kbar p q hcard
      (representationLAdicSheafMap B X x _ hτ₁ hτ₂ L hL) i)
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp] at h
  exact h.symm

end Integral

/-! ### Rational intertwiners -/

section Rational

variable {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℚ_[ℓ]} (hρ₁ : Continuous ρ₁)
  {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℚ_[ℓ]} (hρ₂ : Continuous ρ₂)
  {ρ₃ : EtaleFundamentalGroup X.1 x →* GL (Fin r₃) ℚ_[ℓ]} (hρ₃ : Continuous ρ₃)

/-- The conjugate `P₂⁻¹ A P₁` of a matrix by the matrices `Pᵢ` of the integral models of the
`ρᵢ`. -/
def rationalIntertwinerConj (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) :
    Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ] :=
  ((representationSheafConj B X x ρ₂ hρ₂)⁻¹ : GL (Fin r₂) ℚ_[ℓ]).val * A *
    (representationSheafConj B X x ρ₁ hρ₁).val

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- Over `ℚ_ℓ`, the integral model of `ρ` is its conjugate by `representationSheafConj`. -/
theorem map_integralModel_representationSheafConj {r : ℕ}
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (g : EtaleFundamentalGroup X.1 x) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    (integralModel ρ hρ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((representationSheafConj B X x ρ hρ)⁻¹ * ρ g * representationSheafConj B X x ρ hρ).val := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  exact congrArg Units.val (map_integralModel ρ hρ g)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- An integral matrix which is `ℓᴺ P₂⁻¹ A P₁` for an intertwiner `A` intertwines the integral
models. -/
theorem intertwines_of_map_eq_pow_smul (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (N : ℕ) (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hL : L.map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ N) • rationalIntertwinerConj B X x hρ₁ hρ₂ A)
    (g : EtaleFundamentalGroup X.1 x) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    L * (integralModel ρ₁ hρ₁ g).val = (integralModel ρ₂ hρ₂ g).val * L := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  apply Matrix.map_injective (f := (PadicInt.Coe.ringHom (p := ℓ))) (fun a b h => PadicInt.ext h)
  simp only [Matrix.map_mul]
  rw [hL, map_integralModel_representationSheafConj, map_integralModel_representationSheafConj,
    Matrix.smul_mul, Matrix.mul_smul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
  exact congrArg _ (conj_mul_conj_eq_of_mul_eq _ _ (hA g))

/-- The power of `ℓ` making `P₂⁻¹ A P₁` integral. -/
def rationalIntertwinerExp (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) : ℕ :=
  (exists_pow_mul_norm_le_one (ℓ := ℓ) (rationalIntertwinerConj B X x hρ₁ hρ₂ A)).choose

/-- The integral matrix `ℓᴺ P₂⁻¹ A P₁`. -/
def rationalIntertwinerLift (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) :
    Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ] :=
  Matrix.of fun a b =>
    ⟨_, (exists_pow_mul_norm_le_one (ℓ := ℓ) (rationalIntertwinerConj B X x hρ₁ hρ₂ A)).choose_spec
      a b⟩

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- Over `ℚ_ℓ`, `rationalIntertwinerLift A` is `ℓᴺ P₂⁻¹ A P₁`, where
`N = rationalIntertwinerExp A`. -/
theorem map_rationalIntertwinerLift (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) :
    (rationalIntertwinerLift B X x hρ₁ hρ₂ A).map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ rationalIntertwinerExp B X x hρ₁ hρ₂ A) •
        rationalIntertwinerConj B X x hρ₁ hρ₂ A := by
  ext a b
  rfl

/-- **The map on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` of a `ℚ_ℓ`-intertwiner** `A : ρ₁ → ρ₂`: the map of the
integral intertwiner `ℓᴺ P₂⁻¹ A P₁` of the integral models, divided by `ℓᴺ`. -/
def rationalIntertwinerCohomologyMap (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (integralModel ρ₁ hρ₁) (continuous_integralModel ρ₁ hρ₁)) i →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (integralModel ρ₂ hρ₂) (continuous_integralModel ρ₂ hρ₂)) i :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  ((ℓ : ℚ_[ℓ]) ^ rationalIntertwinerExp B X x hρ₁ hρ₂ A)⁻¹ •
    integralIntertwinerCohomologyMap B X x f j kbar i (continuous_integralModel ρ₁ hρ₁)
      (continuous_integralModel ρ₂ hρ₂) (rationalIntertwinerLift B X x hρ₁ hρ₂ A)
      (intertwines_of_map_eq_pow_smul B X x hρ₁ hρ₂ A hA _ _
        (map_rationalIntertwinerLift B X x hρ₁ hρ₂ A))

/-- Equal rational intertwiners induce equal maps on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`. -/
theorem rationalIntertwinerCohomologyMap_congr {A A' : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]}
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (hA' : ∀ g, A' * (ρ₁ g).val = (ρ₂ g).val * A')
    (h : A = A') :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA =
      rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A' hA' := by
  subst h
  rfl

/-- **The rational map does not depend on the power of `ℓ`**: the map of any integral
`ℓᴹ P₂⁻¹ A P₁` is `ℓᴹ` times it. -/
theorem integralIntertwinerCohomologyMap_eq_smul_rationalIntertwinerCohomologyMap
    (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (M : ℕ)
    (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hLm : L.map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ M) • rationalIntertwinerConj B X x hρ₁ hρ₂ A)
    (hL : haveI := compactSpace_etaleFundamentalGroup X.1 x
      ∀ g, L * (integralModel ρ₁ hρ₁ g).val = (integralModel ρ₂ hρ₂ g).val * L) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    integralIntertwinerCohomologyMap B X x f j kbar i (continuous_integralModel ρ₁ hρ₁)
        (continuous_integralModel ρ₂ hρ₂) L hL =
      ((ℓ : ℚ_[ℓ]) ^ M) • rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  set N := rationalIntertwinerExp B X x hρ₁ hρ₂ A
  set L₀ := rationalIntertwinerLift B X x hρ₁ hρ₂ A
  have hL₀m := map_rationalIntertwinerLift B X x hρ₁ hρ₂ A
  have hL₀ := intertwines_of_map_eq_pow_smul B X x hρ₁ hρ₂ A hA _ _ hL₀m
  have key : ((ℓ ^ N : ℕ) : ℤ_[ℓ]) • L = ((ℓ ^ M : ℕ) : ℤ_[ℓ]) • L₀ := by
    apply Matrix.map_injective (f := (PadicInt.Coe.ringHom (p := ℓ))) (fun a b h => PadicInt.ext h)
    ext a b
    have h1 := congrFun (congrFun hLm a) b
    have h2 := congrFun (congrFun hL₀m a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [map_mul, map_mul, h1, h2, map_natCast, map_natCast]
    push_cast
    ring
  have hne : ((ℓ : ℚ_[ℓ]) ^ N) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  have hc₁ := continuous_integralModel ρ₁ hρ₁
  have hc₂ := continuous_integralModel ρ₂ hρ₂
  have h := (integralIntertwinerCohomologyMap_natCast_smul B X x f j kbar i hc₁ hc₂ (ℓ ^ N) L
    hL).symm.trans ((integralIntertwinerCohomologyMap_congr B X x f j kbar i hc₁ hc₂ _ _ key).trans
      (integralIntertwinerCohomologyMap_natCast_smul B X x f j kbar i hc₁ hc₂ (ℓ ^ M) L₀ hL₀))
  refine LinearMap.ext fun v => eq_of_pow_smul_eq_pow_smul (ℓ := ℓ) N ?_
  have hv := LinearMap.congr_fun h v
  simp only [LinearMap.smul_apply] at hv
  push_cast at hv
  rw [hv]
  simp only [rationalIntertwinerCohomologyMap, LinearMap.smul_apply, smul_smul]
  congr 1
  have hne' : ((ℓ : ℚ_[ℓ]) ^ rationalIntertwinerExp B X x hρ₁ hρ₂ A) ≠ 0 := hne
  field_simp
  rfl

/-- The rational map of `A` is the map of any integral `ℓᴹ P₂⁻¹ A P₁`, divided by `ℓᴹ`. -/
private theorem rationalIntertwinerCohomologyMap_eq_inv_pow_smul
    (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ]) (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (M : ℕ)
    (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hLm : L.map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ M) • rationalIntertwinerConj B X x hρ₁ hρ₂ A)
    (hL : haveI := compactSpace_etaleFundamentalGroup X.1 x
      ∀ g, L * (integralModel ρ₁ hρ₁ g).val = (integralModel ρ₂ hρ₂ g).val * L) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA =
      ((ℓ : ℚ_[ℓ]) ^ M)⁻¹ • integralIntertwinerCohomologyMap B X x f j kbar i
        (continuous_integralModel ρ₁ hρ₁) (continuous_integralModel ρ₂ hρ₂) L hL := by
  rw [integralIntertwinerCohomologyMap_eq_smul_rationalIntertwinerCohomologyMap B X x f j kbar i
    hρ₁ hρ₂ A hA M L hLm hL, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2
      (Fact.out : ℓ.Prime).ne_zero)), one_smul]

/-- The map of an integral intertwiner which is `P₂⁻¹ A P₁` over `ℚ_ℓ` is the rational map of
`A`. -/
theorem rationalIntertwinerCohomologyMap_eq_of_map_eq (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (L : Matrix (Fin r₂) (Fin r₁) ℤ_[ℓ])
    (hLm : L.map (PadicInt.Coe.ringHom (p := ℓ)) = rationalIntertwinerConj B X x hρ₁ hρ₂ A)
    (hL : haveI := compactSpace_etaleFundamentalGroup X.1 x
      ∀ g, L * (integralModel ρ₁ hρ₁ g).val = (integralModel ρ₂ hρ₂ g).val * L) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    integralIntertwinerCohomologyMap B X x f j kbar i (continuous_integralModel ρ₁ hρ₁)
        (continuous_integralModel ρ₂ hρ₂) L hL =
      rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA := by
  have h := integralIntertwinerCohomologyMap_eq_smul_rationalIntertwinerCohomologyMap B X x f j
    kbar i hρ₁ hρ₂ A hA 0 L (by rw [pow_zero, one_smul]; exact hLm) hL
  rwa [pow_zero, one_smul] at h

/-- The identity matrix induces the identity of `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)`. -/
theorem rationalIntertwinerCohomologyMap_one :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₁ 1
      (fun g => by rw [Matrix.one_mul, Matrix.mul_one]) = LinearMap.id := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have hm : (1 : Matrix (Fin r₁) (Fin r₁) ℤ_[ℓ]).map (PadicInt.Coe.ringHom (p := ℓ)) =
      rationalIntertwinerConj B X x hρ₁ hρ₁ 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), rationalIntertwinerConj, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← rationalIntertwinerCohomologyMap_eq_of_map_eq B X x f j kbar i hρ₁ hρ₁ _ _ 1 hm
    (intertwines_one _)]
  exact integralIntertwinerCohomologyMap_one B X x f j kbar i _

/-- The rational map of a product `A' * A` of intertwiners is the composite of their maps. -/
theorem rationalIntertwinerCohomologyMap_mul (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (A' : Matrix (Fin r₃) (Fin r₂) ℚ_[ℓ])
    (hA' : ∀ g, A' * (ρ₂ g).val = (ρ₃ g).val * A') :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₃ (A' * A)
        (fun g => by rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hA', Matrix.mul_assoc]) =
      (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₂ hρ₃ A' hA').comp
        (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA) := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have hLm := map_rationalIntertwinerLift B X x hρ₁ hρ₂ A
  have hL'm := map_rationalIntertwinerLift B X x hρ₂ hρ₃ A'
  have hL := intertwines_of_map_eq_pow_smul B X x hρ₁ hρ₂ A hA _ _ hLm
  have hL' := intertwines_of_map_eq_pow_smul B X x hρ₂ hρ₃ A' hA' _ _ hL'm
  set L := rationalIntertwinerLift B X x hρ₁ hρ₂ A
  set L' := rationalIntertwinerLift B X x hρ₂ hρ₃ A'
  set N := rationalIntertwinerExp B X x hρ₁ hρ₂ A
  set N' := rationalIntertwinerExp B X x hρ₂ hρ₃ A'
  have hprod : (L' * L).map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ (N' + N)) • rationalIntertwinerConj B X x hρ₁ hρ₃ (A' * A) := by
    rw [Matrix.map_mul, hLm, hL'm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
    congr 1
    simp only [rationalIntertwinerConj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (representationSheafConj B X x ρ₂ hρ₂).val, Units.mul_inv,
      Matrix.one_mul]
  rw [rationalIntertwinerCohomologyMap_eq_inv_pow_smul B X x f j kbar i hρ₁ hρ₃ _ _ (N' + N)
      (L' * L) hprod (intertwines_mul hL hL'),
    rationalIntertwinerCohomologyMap_eq_inv_pow_smul B X x f j kbar i hρ₁ hρ₂ A hA N L hLm hL,
    rationalIntertwinerCohomologyMap_eq_inv_pow_smul B X x f j kbar i hρ₂ hρ₃ A' hA' N' L' hL'm hL',
    integralIntertwinerCohomologyMap_mul B X x f j kbar i _ (continuous_integralModel ρ₂ hρ₂) _
      L hL L' hL', LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, pow_add, mul_inv]

/-- The rational map of a sum `A + A'` of intertwiners is the sum of their maps. -/
theorem rationalIntertwinerCohomologyMap_add (A A' : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (hA' : ∀ g, A' * (ρ₁ g).val = (ρ₂ g).val * A') :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ (A + A')
        (fun g => by rw [Matrix.add_mul, Matrix.mul_add, hA, hA']) =
      rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA +
        rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A' hA' := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have hLm := map_rationalIntertwinerLift B X x hρ₁ hρ₂ A
  have hL'm := map_rationalIntertwinerLift B X x hρ₁ hρ₂ A'
  have hL := intertwines_of_map_eq_pow_smul B X x hρ₁ hρ₂ A hA _ _ hLm
  have hL' := intertwines_of_map_eq_pow_smul B X x hρ₁ hρ₂ A' hA' _ _ hL'm
  set L := rationalIntertwinerLift B X x hρ₁ hρ₂ A
  set L' := rationalIntertwinerLift B X x hρ₁ hρ₂ A'
  set N := rationalIntertwinerExp B X x hρ₁ hρ₂ A
  set N' := rationalIntertwinerExp B X x hρ₁ hρ₂ A'
  have hsum : (((ℓ ^ N' : ℕ) : ℤ_[ℓ]) • L + ((ℓ ^ N : ℕ) : ℤ_[ℓ]) • L').map
      (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ (N' + N)) • rationalIntertwinerConj B X x hρ₁ hρ₂ (A + A') := by
    ext a b
    have h1 := congrFun (congrFun hLm a) b
    have h2 := congrFun (congrFun hL'm a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply] at h1 h2 ⊢
    rw [map_add, map_mul, map_mul, h1, h2, map_natCast, map_natCast, rationalIntertwinerConj,
      rationalIntertwinerConj, rationalIntertwinerConj, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_apply]
    push_cast
    ring
  have hs := intertwines_smul ((ℓ ^ N' : ℕ) : ℤ_[ℓ]) hL
  have hs' := intertwines_smul ((ℓ ^ N : ℕ) : ℤ_[ℓ]) hL'
  rw [rationalIntertwinerCohomologyMap_eq_inv_pow_smul B X x f j kbar i hρ₁ hρ₂ _ _ (N' + N) _
      hsum (intertwines_add hs hs'),
    integralIntertwinerCohomologyMap_add B X x f j kbar i _ _ _ _ hs hs',
    integralIntertwinerCohomologyMap_natCast_smul B X x f j kbar i _ _ _ L hL,
    integralIntertwinerCohomologyMap_natCast_smul B X x f j kbar i _ _ _ L' hL',
    rationalIntertwinerCohomologyMap_eq_inv_pow_smul B X x f j kbar i hρ₁ hρ₂ A hA N L hLm hL,
    rationalIntertwinerCohomologyMap_eq_inv_pow_smul B X x f j kbar i hρ₁ hρ₂ A' hA' N' L' hL'm
      hL', smul_add, smul_smul, smul_smul]
  have hne : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  push_cast
  congr 2 <;> field_simp <;> ring

/-- The zero matrix induces the zero map. -/
theorem rationalIntertwinerCohomologyMap_zero :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ 0
      (fun g => by rw [Matrix.zero_mul, Matrix.mul_zero]) = 0 := by
  have h := rationalIntertwinerCohomologyMap_add B X x f j kbar i hρ₁ hρ₂ 0 0
    (intertwines_zero _ _) (intertwines_zero _ _)
  rw [rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ₁ hρ₂ _
    (intertwines_zero _ _) (add_zero 0)] at h
  exact left_eq_add.mp h

/-- The rational map of a finite sum of intertwiners is the sum of their maps. -/
theorem rationalIntertwinerCohomologyMap_sum {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ t g, A t * (ρ₁ g).val = (ρ₂ g).val * A t) :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ (∑ t ∈ s, A t)
        (fun g => by
          rw [Matrix.sum_mul, Matrix.mul_sum]
          exact Finset.sum_congr rfl fun t _ => hA t g) =
      ∑ t ∈ s, rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ (A t) (hA t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ₁ hρ₂ _
      (intertwines_zero _ _) Finset.sum_empty).trans
      ((rationalIntertwinerCohomologyMap_zero B X x f j kbar i hρ₁ hρ₂).trans Finset.sum_empty.symm)
  | insert a s ha ih =>
    have hs : ∀ g, (∑ t ∈ s, A t) * (ρ₁ g).val = (ρ₂ g).val * ∑ t ∈ s, A t := fun g => by
      rw [Matrix.sum_mul, Matrix.mul_sum]
      exact Finset.sum_congr rfl fun t _ => hA t g
    refine (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ₁ hρ₂ _
      (intertwines_add (hA a) hs) (Finset.sum_insert ha)).trans
      ((rationalIntertwinerCohomologyMap_add B X x f j kbar i hρ₁ hρ₂ _ _ (hA a) hs).trans ?_)
    rw [ih, Finset.sum_insert ha]

/-- **The map of a rational intertwiner commutes with `π_X^*`.** -/
theorem rationalIntertwinerCohomologyMap_frobenius (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A)
    (v : haveI := compactSpace_etaleFundamentalGroup X.1 x
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (integralModel ρ₁ hρ₁) (continuous_integralModel ρ₁ hρ₁)) i) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (representationLAdicSheaf B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
            (integralModel ρ₁ hρ₁) (continuous_integralModel ρ₁ hρ₁)) i).hom v) =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (representationLAdicSheaf B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
            (integralModel ρ₂ hρ₂) (continuous_integralModel ρ₂ hρ₂)) i).hom
        (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA v) := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  simp only [rationalIntertwinerCohomologyMap, LinearMap.smul_apply]
  rw [integralIntertwinerCohomologyMap_frobenius, map_smul]

end Rational

/-! ### The action of the coefficients -/

section Commutant

variable {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℚ_[ℓ]} (hρ : Continuous ρ)
  {E : Type} [CommRing E] [Algebra ℚ_[ℓ] E] (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r₁) (Fin r₁) ℚ_[ℓ])
  (hα : ∀ e g, α e * (ρ g).val = (ρ g).val * α e)

/-- **The action of `e ∈ E` on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` is the map of the intertwiner `α(e)`.** -/
theorem rationalRingHom_representationSheafCommutantCoefficientSheaf (e : E)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).toLAdicSheaf i) :
    (representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).rationalRingHom
        f j kbar i E e v =
      rationalIntertwinerCohomologyMap B X x f j kbar i hρ hρ (α e) (hα e) v := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  let φ : E →+* Module.End ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).toLAdicSheaf i) :=
    { toFun := fun e => rationalIntertwinerCohomologyMap B X x f j kbar i hρ hρ (α e) (hα e)
      map_one' := by
        refine (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ hρ _
          (intertwines_one _) (map_one α)).trans ?_
        exact rationalIntertwinerCohomologyMap_one B X x f j kbar i hρ
      map_mul' := fun e e' => by
        refine (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ hρ _
          (intertwines_mul (hα e') (hα e)) (map_mul α e e')).trans ?_
        exact rationalIntertwinerCohomologyMap_mul B X x f j kbar i hρ hρ hρ (α e') (hα e') (α e)
          (hα e)
      map_zero' := by
        refine (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ hρ _
          (intertwines_zero _ _) (map_zero α)).trans ?_
        exact rationalIntertwinerCohomologyMap_zero B X x f j kbar i hρ hρ
      map_add' := fun e e' => by
        refine (rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ hρ _
          (intertwines_add (hα e) (hα e')) (map_add α e e')).trans ?_
        exact rationalIntertwinerCohomologyMap_add B X x f j kbar i hρ hρ _ _ (hα e) (hα e') }
  have hφ : (representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).rationalRingHom f j kbar
      i E = φ := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (ℓ : conjIntegralSubring (representationSheafConj B X x ρ hρ) α))
      (RingHom.ext fun o => LinearMap.ext fun v => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply,
      LAdicSheaf.CoefficientSheaf.rationalRingHom_algebraMap_apply]
    exact LinearMap.congr_fun (rationalIntertwinerCohomologyMap_eq_of_map_eq B X x f j kbar i hρ hρ
      (α o) (hα o) (conjIntegralLift _ α o) (mapMatrix_conjIntegralLift _ α o)
      (conjIntegralLift_mul_integralModel B X x ρ hρ α hα o)) v
  rw [hφ]
  rfl

end Commutant

section CommutantLinear

variable {ρ₁ : EtaleFundamentalGroup X.1 x →* GL (Fin r₁) ℚ_[ℓ]} (hρ₁ : Continuous ρ₁)
  {ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r₂) ℚ_[ℓ]} (hρ₂ : Continuous ρ₂)
  {E₁ E₂ : Type} [CommRing E₁] [Algebra ℚ_[ℓ] E₁] [CommRing E₂] [Algebra ℚ_[ℓ] E₂]
  (α₁ : E₁ →ₐ[ℚ_[ℓ]] Matrix (Fin r₁) (Fin r₁) ℚ_[ℓ])
  (hα₁ : ∀ e g, α₁ e * (ρ₁ g).val = (ρ₁ g).val * α₁ e)
  (α₂ : E₂ →ₐ[ℚ_[ℓ]] Matrix (Fin r₂) (Fin r₂) ℚ_[ℓ])
  (hα₂ : ∀ e g, α₂ e * (ρ₂ g).val = (ρ₂ g).val * α₂ e)

/-- **An intertwiner carrying the action of `e₁` to that of `e₂` carries `e₁ • v` to
`e₂ • A v`** on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` of the commutant sheaves. -/
theorem rationalIntertwinerCohomologyMap_rationalRingHom (A : Matrix (Fin r₂) (Fin r₁) ℚ_[ℓ])
    (hA : ∀ g, A * (ρ₁ g).val = (ρ₂ g).val * A) (e₁ : E₁) (e₂ : E₂)
    (he : A * α₁ e₁ = α₂ e₂ * A)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (representationSheafCommutantCoefficientSheaf B X x ρ₁ hρ₁ α₁ hα₁).toLAdicSheaf i) :
    rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA
        ((representationSheafCommutantCoefficientSheaf B X x ρ₁ hρ₁ α₁ hα₁).rationalRingHom f j
          kbar i E₁ e₁ v) =
      (representationSheafCommutantCoefficientSheaf B X x ρ₂ hρ₂ α₂ hα₂).rationalRingHom f j kbar
        i E₂ e₂ (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA v) := by
  refine (congrArg (rationalIntertwinerCohomologyMap B X x f j kbar i hρ₁ hρ₂ A hA)
    (rationalRingHom_representationSheafCommutantCoefficientSheaf B X x f j kbar i hρ₁ α₁ hα₁ e₁
      v)).trans (Eq.trans ?_
    (rationalRingHom_representationSheafCommutantCoefficientSheaf B X x f j kbar i hρ₂ α₂ hα₂ e₂
      _).symm)
  have h₁ := rationalIntertwinerCohomologyMap_mul B X x f j kbar i hρ₁ hρ₁ hρ₂ (α₁ e₁) (hα₁ e₁) A hA
  have h₂ := rationalIntertwinerCohomologyMap_mul B X x f j kbar i hρ₁ hρ₂ hρ₂ A hA (α₂ e₂) (hα₂ e₂)
  rw [rationalIntertwinerCohomologyMap_congr B X x f j kbar i hρ₁ hρ₂ _
    (intertwines_mul hA (hα₂ e₂)) he] at h₁
  exact (LinearMap.congr_fun h₁ v).symm.trans (LinearMap.congr_fun h₂ v)

end CommutantLinear

end Stacks.EtaleCohomology

end
