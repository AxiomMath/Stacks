module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheafHomMatrix
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicCoefficientExtension

/-!
# The `E`-linear representation of a lisse sheaf with coefficients

Let `F` be a lisse ℓ-adic sheaf on a connected scheme `X` with an action of a `ℤ_ℓ`-algebra `O`,
and `E = O[1/ℓ]` a finite extension of `ℚ_ℓ`. Up to isogeny `F` is `ℱ_ρ` for a continuous
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse`):
`φ : F → ℱ_ρ`, `ψ : ℱ_ρ → F` with `φ ψ = ℓᴺ`, `ψ φ = ℓᴺ`. Each `o ∈ O` gives the endomorphism
`ψ ∘ o ∘ φ` of `ℱ_ρ`, which acts on every stalk, along every path, by one matrix commuting with
the integral model `ρ₀` of `ρ` (`Stacks.EtaleCohomology.representationLAdicSheafHomMatrix`);
dividing by `ℓᴺ` and inverting `ℓ` gives a homomorphism of `ℚ_ℓ`-algebras
`α : E → M_r(ℚ_ℓ)` commuting with `ρ₀` (`Stacks.EtaleCohomology.isogenyCoefficientAlgHom`). By
descent of a commuting action (`Stacks.EtaleCohomology.exists_restrictScalarsRep_conj`), `ρ₀` is
conjugate to the restriction of scalars `Res_b τ` of a continuous `τ : π₁(X, x̄) → GL_m(E)`, the
conjugation carrying `α(e)` to `Res_b(e · 1)`
(`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`). This is the passage from the lisse
sheaf with coefficients `G|_V = R¹pr₂!(…)|_V` to the `E`-linear representation `τ` in Laumon's
degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.isogenyCoefficientEnd`,
  `Stacks.EtaleCohomology.isogenyCoefficientMatrix`.
* `Stacks.EtaleCohomology.isogenyCoefficientAlgHom`: `α : E →ₐ[ℚ_ℓ] M_r(ℚ_ℓ)`.

## Main results

* `Stacks.EtaleCohomology.isogenyCoefficientAlgHom_algebraMap`,
  `Stacks.EtaleCohomology.isogenyCoefficientAlgHom_commute`.
* `Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

open scoped IsMulCommutative

universe u

namespace Stacks.EtaleCohomology

section Scalar

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}
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
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')

/-- **Multiplication by `c ∈ ℤ_ℓ` in the middle of a composite multiplies its matrix by `c`.** -/
public theorem representationLAdicSheafHomMatrix_comp_scalarEnd_comp
    {G : LAdicSheaf.{u, u + 1} B X ℓ}
    (θ₁ : representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶ G)
    (θ₂ : G ⟶ representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ') (c : ℤ_[ℓ]) :
    representationLAdicSheafHomMatrix B X x hρ hρ' (θ₁ ≫ LAdicSheaf.scalarEnd G c ≫ θ₂) =
      c • representationLAdicSheafHomMatrix B X x hρ hρ' (θ₁ ≫ θ₂) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  obtain ⟨v, rfl⟩ :=
    (representationLevelTrivialization B X x ρ hρ (Iso.refl _)).stalkEquiv.surjective w
  rw [← representationLevelTrivialization_stalkEquiv_stalkMap_of_hom,
    ← representationLevelTrivialization_stalkEquiv_stalkMap_of_hom, LAdicSheaf.stalkMap_comp,
    LAdicSheaf.stalkMap_comp, LAdicSheaf.stalkMap_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LAdicSheaf.stalkMap_scalarEnd, map_smul, map_smul]

end Scalar

section Isogeny

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime]
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
  (φ : F.toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B X x ρ hρ)
  (ψ : LAdicSheaf.representationSheaf B X x ρ hρ ⟶ F.toLAdicSheaf)

/-- **The endomorphism `ψ ∘ o ∘ φ` of `ℱ_ρ`** induced by `o ∈ O` through an isogeny
`φ : F → ℱ_ρ`, `ψ : ℱ_ρ → F`, as an endomorphism of the sheaf of the integral model of `ρ`. -/
public def isogenyCoefficientEnd (o : O) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    End (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (integralModel ρ hρ) (continuous_integralModel ρ hρ)) :=
  End.of (ψ ≫ (F.act o).asHom ≫ φ)

/-- **The matrix of `ψ ∘ o ∘ φ`**, an integral matrix commuting with the integral model of `ρ`
(`Stacks.EtaleCohomology.representationLAdicSheafHomMatrix`). -/
public def isogenyCoefficientMatrix (o : O) : Matrix (Fin r) (Fin r) ℤ_[ℓ] :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  representationLAdicSheafEndMatrix B X x (continuous_integralModel ρ hρ)
    (isogenyCoefficientEnd B X x F ρ hρ φ ψ o)

/-- The matrix of `ψ ∘ o ∘ φ` commutes with the integral model of `ρ`. -/
public theorem isogenyCoefficientMatrix_mul (o : O) (g : EtaleFundamentalGroup X.1 x) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    isogenyCoefficientMatrix B X x F ρ hρ φ ψ o * (integralModel ρ hρ g).val =
      (integralModel ρ hρ g).val * isogenyCoefficientMatrix B X x F ρ hρ φ ψ o :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  representationLAdicSheafHomMatrix_mul B X x _ _ _ g

variable (N : ℕ)

/-- `(ψ ∘ o ∘ φ)(ψ ∘ o' ∘ φ) = ℓᴺ (ψ ∘ o o' ∘ φ)` when `φ ψ = ℓᴺ`. -/
public theorem isogenyCoefficientEnd_mul (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (o o' : O) :
    isogenyCoefficientEnd B X x F ρ hρ φ ψ o * isogenyCoefficientEnd B X x F ρ hρ φ ψ o' =
      (ℓ ^ N) • isogenyCoefficientEnd B X x F ρ hρ φ ψ (o * o') := by
  ext
  change (ψ ≫ (F.act o').asHom ≫ φ) ≫ (ψ ≫ (F.act o).asHom ≫ φ) =
    (ℓ ^ N) • (ψ ≫ (F.act (o * o')).asHom ≫ φ)
  simp only [Category.assoc]
  rw [reassoc_of% hφψ, Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    Preadditive.comp_nsmul, map_mul, End.mul_asHom, Category.assoc]

/-- `ψ ∘ 1 ∘ φ = ψ ∘ φ`. -/
private theorem isogenyCoefficientEnd_one_eq :
    (isogenyCoefficientEnd B X x F ρ hρ φ ψ 1).asHom = ψ ≫ φ := by
  change ψ ≫ (F.act 1).asHom ≫ φ = _
  rw [map_one, End.one_asHom, Category.id_comp]

/-- `ψ ∘ 1 ∘ φ = ℓᴺ` when `ψ φ = ℓᴺ`. -/
public theorem isogenyCoefficientEnd_one (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) :
    isogenyCoefficientEnd B X x F ρ hρ φ ψ 1 = (ℓ ^ N) • 1 := by
  ext
  rw [isogenyCoefficientEnd_one_eq, hψφ]
  rfl

/-- The matrices of `ψ ∘ o ∘ φ` and `ψ ∘ o' ∘ φ` multiply to `ℓᴺ` times that of `ψ ∘ o o' ∘ φ`
when `φ ψ = ℓᴺ`. -/
public theorem isogenyCoefficientMatrix_mul_mul (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (o o' : O) :
    isogenyCoefficientMatrix B X x F ρ hρ φ ψ o * isogenyCoefficientMatrix B X x F ρ hρ φ ψ o' =
      (ℓ ^ N) • isogenyCoefficientMatrix B X x F ρ hρ φ ψ (o * o') := by
  rw [isogenyCoefficientMatrix, isogenyCoefficientMatrix, isogenyCoefficientMatrix, ← map_mul,
    isogenyCoefficientEnd_mul B X x F ρ hρ φ ψ N hφψ, map_nsmul]

set_option synthInstance.maxHeartbeats 200000 in
/-- The matrix of `ψ ∘ 1 ∘ φ` is `ℓᴺ` when `ψ φ = ℓᴺ`. -/
public theorem isogenyCoefficientMatrix_one (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) :
    isogenyCoefficientMatrix B X x F ρ hρ φ ψ 1 = (ℓ ^ N) • 1 := by
  rw [isogenyCoefficientMatrix, isogenyCoefficientEnd_one B X x F ρ hρ φ ψ N hψφ, map_nsmul,
    map_one]

set_option synthInstance.maxHeartbeats 200000 in
/-- The matrix of `ψ ∘ o ∘ φ` is additive in `o`. -/
public theorem isogenyCoefficientMatrix_add (o o' : O) :
    isogenyCoefficientMatrix B X x F ρ hρ φ ψ (o + o') =
      isogenyCoefficientMatrix B X x F ρ hρ φ ψ o +
        isogenyCoefficientMatrix B X x F ρ hρ φ ψ o' := by
  have h : isogenyCoefficientEnd B X x F ρ hρ φ ψ (o + o') =
      isogenyCoefficientEnd B X x F ρ hρ φ ψ o + isogenyCoefficientEnd B X x F ρ hρ φ ψ o' := by
    ext
    change ψ ≫ (F.act (o + o')).asHom ≫ φ = (ψ ≫ (F.act o).asHom ≫ φ) + (ψ ≫ (F.act o').asHom ≫ φ)
    rw [map_add, End.add_asHom, Preadditive.add_comp, Preadditive.comp_add]
  rw [isogenyCoefficientMatrix, isogenyCoefficientMatrix, isogenyCoefficientMatrix, h, map_add]

/-- The matrix of `ψ ∘ 0 ∘ φ` is zero. -/
public theorem isogenyCoefficientMatrix_zero :
    isogenyCoefficientMatrix B X x F ρ hρ φ ψ 0 = 0 := by
  have h : isogenyCoefficientEnd B X x F ρ hρ φ ψ 0 = 0 := by
    ext
    change ψ ≫ (F.act 0).asHom ≫ φ = 0
    rw [map_zero, End.zero_asHom, Limits.zero_comp, Limits.comp_zero]
  rw [isogenyCoefficientMatrix, h, map_zero]

/-- The matrix of `ψ ∘ c ∘ φ` for `c ∈ ℤ_ℓ` is `c ℓᴺ`. -/
public theorem isogenyCoefficientMatrix_algebraMap (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) (c : ℤ_[ℓ]) :
    isogenyCoefficientMatrix B X x F ρ hρ φ ψ (algebraMap ℤ_[ℓ] O c) = (c * ℓ ^ N) • 1 := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have h1 := isogenyCoefficientMatrix_one B X x F ρ hρ φ ψ N hψφ
  rw [isogenyCoefficientMatrix, representationLAdicSheafEndMatrix_apply,
    isogenyCoefficientEnd_one_eq] at h1
  rw [isogenyCoefficientMatrix, representationLAdicSheafEndMatrix_apply]
  change representationLAdicSheafHomMatrix B X x _ _
    (ψ ≫ (F.act (algebraMap ℤ_[ℓ] O c)).asHom ≫ φ) = _
  rw [F.act_algebraMap]
  refine (representationLAdicSheafHomMatrix_comp_scalarEnd_comp B X x
    (continuous_integralModel ρ hρ) (continuous_integralModel ρ hρ) ψ φ c).trans ?_
  erw [h1, ← Nat.cast_smul_eq_nsmul ℤ_[ℓ] (ℓ ^ N), smul_smul, Nat.cast_pow]

/-- **The rational action** `o ↦ ℓ⁻ᴺ (ψ ∘ o ∘ φ)` of `O` on `ℚ_ℓ^r`, a ring homomorphism. -/
public def isogenyCoefficientRingHom (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) : O →+* Matrix (Fin r) (Fin r) ℚ_[ℓ] where
  toFun o := ((ℓ : ℚ_[ℓ]) ^ N)⁻¹ •
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (isogenyCoefficientMatrix B X x F ρ hρ φ ψ o)
  map_one' := by
    rw [isogenyCoefficientMatrix_one B X x F ρ hρ φ ψ N hψφ, map_nsmul, map_one,
      ← Nat.cast_smul_eq_nsmul ℚ_[ℓ], smul_smul, Nat.cast_pow, inv_mul_cancel₀ (pow_ne_zero _
        (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)), one_smul]
  map_mul' o o' := by
    rw [smul_mul_smul_comm, ← map_mul, isogenyCoefficientMatrix_mul_mul B X x F ρ hρ φ ψ N hφψ,
      map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ_[ℓ], smul_smul, Nat.cast_pow, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)), mul_one]
  map_zero' := by
    rw [isogenyCoefficientMatrix_zero, map_zero, smul_zero]
  map_add' o o' := by
    rw [isogenyCoefficientMatrix_add, map_add, smul_add]

/-- The rational action sends `o` to `ℓ⁻ᴺ` times the matrix of `ψ ∘ o ∘ φ`, read in `ℚ_ℓ`. -/
public theorem isogenyCoefficientRingHom_apply (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) (o : O) :
    isogenyCoefficientRingHom B X x F ρ hρ φ ψ N hφψ hψφ o = ((ℓ : ℚ_[ℓ]) ^ N)⁻¹ •
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (isogenyCoefficientMatrix B X x F ρ hρ φ ψ o) :=
  rfl

/-- The rational action `o ↦ ℓ⁻ᴺ (ψ ∘ o ∘ φ)` commutes with the integral model of `ρ`. -/
public theorem isogenyCoefficientRingHom_commute (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) (o : O) (g : EtaleFundamentalGroup X.1 x) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    isogenyCoefficientRingHom B X x F ρ hρ φ ψ N hφψ hψφ o *
        (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val =
      (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val * isogenyCoefficientRingHom B X x F ρ hρ φ ψ N hφψ hψφ o := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  rw [isogenyCoefficientRingHom_apply, smul_mul_assoc, mul_smul_comm]
  congr 1
  change (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix _ *
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ hρ g).val =
    (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ hρ g).val *
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix _
  rw [← map_mul, ← map_mul, isogenyCoefficientMatrix_mul]

/-- The commutative subalgebra of `M_r(ℚ_ℓ)` generated by the rational action of `O`. -/
public def isogenyCoefficientAlgebra (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) : Subalgebra ℚ_[ℓ] (Matrix (Fin r) (Fin r) ℚ_[ℓ]) :=
  Algebra.adjoin ℚ_[ℓ] (Set.range (isogenyCoefficientRingHom B X x F ρ hρ φ ψ N hφψ hψφ))

/-- The subalgebra generated by the rational action of `O` is commutative, as `O` is. -/
public instance isogenyCoefficientAlgebra.isMulCommutative (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) :
    IsMulCommutative (isogenyCoefficientAlgebra B X x F ρ hρ φ ψ N hφψ hψφ) :=
  Algebra.isMulCommutative_adjoin ℚ_[ℓ] (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ -
    exact (Commute.all a b).map _)

/-- The rational action of `O`, with values in the commutative subalgebra it generates. -/
public def isogenyCoefficientRingHom' (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) : O →+* isogenyCoefficientAlgebra B X x F ρ hρ φ ψ N hφψ hψφ :=
  (isogenyCoefficientRingHom B X x F ρ hρ φ ψ N hφψ hψφ).codRestrict _ fun o =>
    Algebra.subset_adjoin ⟨o, rfl⟩

/-- The powers of `ℓ` act invertibly in the commutative subalgebra generated by the rational
action of `O`. -/
public theorem isUnit_isogenyCoefficientRingHom' (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) (y : Submonoid.powers (ℓ : O)) :
    IsUnit (isogenyCoefficientRingHom' B X x F ρ hρ φ ψ N hφψ hψφ y) := by
  obtain ⟨_, k, rfl⟩ := y
  rw [map_pow, map_natCast,
    ← map_natCast (algebraMap ℚ_[ℓ] (isogenyCoefficientAlgebra B X x F ρ hρ φ ψ N hφψ hψφ))]
  exact ((isUnit_iff_ne_zero.2 (NeZero.ne _)).map _).pow k

variable (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

/-- **The action of `E = O[1/ℓ]` on `ℚ_ℓ^r`** extending `o ↦ ℓ⁻ᴺ (ψ ∘ o ∘ φ)`, as a ring
homomorphism. -/
public def isogenyCoefficientERingHom (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) : E →+* Matrix (Fin r) (Fin r) ℚ_[ℓ] :=
  (isogenyCoefficientAlgebra B X x F ρ hρ φ ψ N hφψ hψφ).val.toRingHom.comp
    (IsLocalization.lift (M := Submonoid.powers (ℓ : O)) (S := E)
      (isUnit_isogenyCoefficientRingHom' B X x F ρ hρ φ ψ N hφψ hψφ))

omit [Algebra ℚ_[ℓ] E] in
/-- The action of `E` extends the rational action of `O`. -/
public theorem isogenyCoefficientERingHom_algebraMap (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) (o : O) :
    isogenyCoefficientERingHom B X x F ρ hρ φ ψ N E hφψ hψφ (algebraMap O E o) =
      isogenyCoefficientRingHom B X x F ρ hρ φ ψ N hφψ hψφ o := by
  change (IsLocalization.lift (M := Submonoid.powers (ℓ : O)) (S := E)
    (isUnit_isogenyCoefficientRingHom' B X x F ρ hρ φ ψ N hφψ hψφ) (algebraMap O E o)).1 = _
  rw [IsLocalization.lift_eq]
  rfl

omit [Algebra ℚ_[ℓ] E] in
/-- The action of `E` takes values in the commutative subalgebra generated by the rational action
of `O`. -/
public theorem isogenyCoefficientERingHom_mem (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _) (e : E) :
    isogenyCoefficientERingHom B X x F ρ hρ φ ψ N E hφψ hψφ e ∈
      isogenyCoefficientAlgebra B X x F ρ hρ φ ψ N hφψ hψφ :=
  (IsLocalization.lift (M := Submonoid.powers (ℓ : O)) (S := E)
    (isUnit_isogenyCoefficientRingHom' B X x F ρ hρ φ ψ N hφψ hψφ) e).2

/-- The action of `E` restricts to the scalars `ℚ_ℓ` when `ℤ_ℓ → O → E` and `ℤ_ℓ → ℚ_ℓ → E`
agree. -/
public theorem isogenyCoefficientERingHom_algebraMap_rat (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    (c : ℚ_[ℓ]) :
    isogenyCoefficientERingHom B X x F ρ hρ φ ψ N E hφψ hψφ (algebraMap ℚ_[ℓ] E c) =
      algebraMap ℚ_[ℓ] _ c := by
  have h : ((isogenyCoefficientERingHom B X x F ρ hρ φ ψ N E hφψ hψφ).comp
      (algebraMap ℚ_[ℓ] E)).comp (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      (algebraMap ℚ_[ℓ] _).comp (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    refine RingHom.ext fun c => ?_
    change isogenyCoefficientERingHom B X x F ρ hρ φ ψ N E hφψ hψφ
      (algebraMap ℚ_[ℓ] E (c : ℚ_[ℓ])) = algebraMap ℚ_[ℓ] _ (c : ℚ_[ℓ])
    rw [← hOE, isogenyCoefficientERingHom_algebraMap, isogenyCoefficientRingHom_apply,
      isogenyCoefficientMatrix_algebraMap B X x F ρ hρ φ ψ N hψφ]
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one, Matrix.algebraMap_matrix_apply, ite_true]
      rw [map_mul, map_pow, map_natCast, mul_comm, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ (NeZero.ne _)), mul_one]
      rfl
    · simp [Matrix.one_apply_ne hij, Matrix.algebraMap_matrix_apply, hij]
  exact RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[ℓ]) h) c

/-- **The action `α : E →ₐ[ℚ_ℓ] M_r(ℚ_ℓ)` of `E` on `ℚ_ℓ^r` through the isogeny**: the
`ℚ_ℓ`-algebra homomorphism extending `o ↦ ℓ⁻ᴺ (ψ ∘ o ∘ φ)`. -/
public def isogenyCoefficientAlgHom (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c) :
    E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ] :=
  { isogenyCoefficientERingHom B X x F ρ hρ φ ψ N E hφψ hψφ with
    commutes' := isogenyCoefficientERingHom_algebraMap_rat B X x F ρ hρ φ ψ N E hφψ hψφ hOE }

/-- **`α(o) = ℓ⁻ᴺ (ψ ∘ o ∘ φ)`** for `o ∈ O`. -/
public theorem isogenyCoefficientAlgHom_algebraMap (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c) (o : O) :
    isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE (algebraMap O E o) =
      ((ℓ : ℚ_[ℓ]) ^ N)⁻¹ •
        (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (isogenyCoefficientMatrix B X x F ρ hρ φ ψ o) :=
  isogenyCoefficientERingHom_algebraMap B X x F ρ hρ φ ψ N E hφψ hψφ o

/-- **`α` commutes with the integral model of `ρ`.** -/
public theorem isogenyCoefficientAlgHom_commute (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _)
    (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    (g : EtaleFundamentalGroup X.1 x) (e : E) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE e *
        (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val =
      (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val *
        isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE e :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  (Algebra.commute_of_mem_adjoin_of_forall_mem_commute
    (isogenyCoefficientERingHom_mem B X x F ρ hρ φ ψ N E hφψ hψφ e) (by
      rintro _ ⟨o, rfl⟩
      exact (isogenyCoefficientRingHom_commute B X x F ρ hρ φ ψ N hφψ hψφ o g).symm)).eq.symm

end Isogeny

section Descent

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime]
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]
  (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
  {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)

include hOE in
omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **A lisse ℓ-adic sheaf with coefficients in `O` comes from a continuous `E`-linear
representation of `π₁`** (`E = O[1/ℓ]` finite over `ℚ_ℓ`, with a `ℚ_ℓ`-basis `b`): there are a
continuous `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` and an isogeny `φ : F → ℱ_ρ`, `ψ : ℱ_ρ → F`
(`φ ψ = ℓᴺ`, `ψ φ = ℓᴺ`), a representation `τ : π₁(X, x̄) → GL_m(E)` with `Res_b τ` continuous,
and mutually inverse matrices `P`, `Q` conjugating the integral model `ρ₀` of `ρ` to `Res_b τ`
and the action `α` of `E` through the isogeny (`Stacks.EtaleCohomology.isogenyCoefficientAlgHom`:
`α(o) = ℓ⁻ᴺ (ψ ∘ o ∘ φ)`, acting on every trivialised stalk of `ℱ_ρ` by
`Stacks.EtaleCohomology.representationLevelTrivialization_stalkEquiv_stalkMap_of_hom`) to the
scalar matrices `Res_b(e · 1)`. -/
public theorem exists_restrictScalarsRep_of_isLisse (hF : F.toLAdicSheaf.IsLisse) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    ∃ (r : ℕ) (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
      (φ : F.toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B X x ρ hρ)
      (ψ : LAdicSheaf.representationSheaf B X x ρ hρ ⟶ F.toLAdicSheaf) (N : ℕ)
      (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
      (m : ℕ) (τ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
      (P : Matrix (Fin r) (Fin (m * d)) ℚ_[ℓ]) (Q : Matrix (Fin (m * d)) (Fin r) ℚ_[ℓ]),
      Continuous (restrictScalarsRep b τ) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      (∀ e : E, Q * isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE e * P =
        restrictScalarsMatrix b (Matrix.scalar (Fin m) e)) ∧
      ∀ g : EtaleFundamentalGroup X.1 x,
        Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  obtain ⟨r, ρ, hρ, φ, ψ, N, hφψ, hψφ⟩ :=
    LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse ℓ (B := B) (X := X) (x := x)
      (F := F.toLAdicSheaf) hF
  let ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ] :=
    (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))).comp (integralModel ρ hρ)
  obtain ⟨m, τ, P, Q, hPQ, hQP, hα, hτ⟩ := exists_restrictScalarsRep_conj b
    (isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE) ρ₀
    (isogenyCoefficientAlgHom_commute B X x F ρ hρ φ ψ N E hφψ hψφ hOE)
  exact ⟨r, ρ, hρ, φ, ψ, N, hφψ, hψφ, m, τ, P, Q,
    continuous_of_conj (((continuous_const.mul hρ).mul continuous_const).congr fun g =>
      (map_integralModel ρ hρ g).symm : Continuous ρ₀) hPQ hQP hτ, hPQ, hQP, hα, hτ⟩

end Descent

end Stacks.EtaleCohomology
