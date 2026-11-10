module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageLevelStalkBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurvePointInertiaStalkRange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralSpecializationRational
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkLevelLimitMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheafMapOfHom

/-!
# The specialization map at a missing point of a curve, through a morphism `G|_V → F_V`

In the setting of `Stacks.EtaleCohomology.CurveSpecializationInput` (`V ⊆ W ⊆ 𝔸¹_k`, `y ∈ W ∖ V`
closed, `G` an ℓ-adic sheaf on `W` with coefficients in `O`, `E = O[1/ℓ]`), let `F_V` be an
ℓ-adic sheaf on `V` with coefficients in `O`, isogenous to `ℱ_ρ` with `ρ` conjugate to `Res_b τ`
(the data of `Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`), and let
`χ : G|_V → F_V` be a morphism compatible with the actions of `O`. If the kernels of the stalks
at `ȳ` of the maps `Gₙ → j_* G|_{V,n} → j_* F_{V,n}` are killed by a fixed power of `ℓ`, the
composite

`ℚ_ℓ ⊗ G_ȳ → ℚ_ℓ ⊗ (j_* F_V)_ȳ → ℚ_ℓ ⊗ (j_* ℱ_ρ)_ȳ ≅ ρ^{I_y} ≅ τ^{I_y}`

is an injective `E`-linear map carrying the geometric Frobenius at `y` to `τ(φ Fr⁻¹)`
(`Stacks.EtaleCohomology.curveSpecializationMapInput`). For `χ = 𝟙` this is
`Stacks.EtaleCohomology.CurveSpecializationInput`
(`Stacks.EtaleCohomology.curveSpecializationInput`).

## Main definitions

* `Stacks.EtaleCohomology.CurveSpecializationMapInput`

## Main results

* `Stacks.EtaleCohomology.curveSpecializationMapInput`
* `Stacks.EtaleCohomology.curveSpecializationInput`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.SmallEtale.LAdicSheaf
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

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

/-- **`ψ ∘ o ∘ φ` is the endomorphism of `ℱ_ρ` induced by its matrix.** -/
public theorem isogenyCoefficientEnd_eq_representationLAdicSheafMap (o : O) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    (isogenyCoefficientEnd B X x F ρ hρ φ ψ o).asHom =
      representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (continuous_integralModel ρ hρ) (continuous_integralModel ρ hρ)
        (isogenyCoefficientMatrix B X x F ρ hρ φ ψ o)
        (isogenyCoefficientMatrix_mul B X x F ρ hρ φ ψ o) :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  eq_representationLAdicSheafMap_representationLAdicSheafHomMatrix B X x _ _ _

end Isogeny

/-- **The specialization map at a missing point of a curve, through a morphism `χ : G|_V → F_V`.**
In the setting of `Stacks.EtaleCohomology.CurveSpecializationInput`, let `F_V` be an ℓ-adic sheaf
on `V` with coefficients in `O`, `χ : G|_V → F_V` a morphism compatible with the actions of `O`,
and `ρ, φ, ψ, N, τ, P, Q` data as produced by
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse` for `F_V`. Suppose that the kernels
of the stalks at `ȳ` of the maps `Gₙ → j_* F_{V,n}` adjoint to `χₙ` are all killed by `ℓᴹ`. Then
there is an injective `E`-linear map from the rational stalk `ℚ_ℓ ⊗ G_ȳ` to the
`τ(I_y)`-invariants of `E^m` carrying the geometric Frobenius at `y` to `τ(φ Fr⁻¹)`. -/
public def CurveSpecializationMapInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Fintype k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (_ : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    -- the curve `W ⊇ V` and the missing point `y`
    (W : B.Scheme) [IsNoetherian W.1] (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
    [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : W.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion eW]
    (_ : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = fW)
    (jW : V.1 ⟶ W.1) [IsOpenImmersion jW]
    (_ : jW ≫ fW = f) (y : W.1) (_ : IsClosed ({y} : Set W.1)) (_ : y ∉ Set.range jW.base)
    (hy : jW.base (genericPoint V.1) ⤳ y)
    -- the local field at `y`
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (V.1.residueField (genericPoint V.1))]
    [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
    [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
    [Finite (IsLocalRing.ResidueField A)]
    (eA : A ≃+* W.1.presheaf.stalk y)
    (_ : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (hFrD :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
    (_ :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    (hyf : Finite (W.1.residueField y))
    -- the sheaf `G` on `W`, with coefficients in `O`
    {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (G : LAdicSheaf.CoefficientSheaf B W ℓ O)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra O E]
    [IsLocalization (Submonoid.powers (ℓ : O)) E]
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
    -- a sheaf `F_V` on `V` with an `O`-compatible morphism `χ : G|_V → F_V`
    (FV : LAdicSheaf.CoefficientSheaf B V ℓ O)
    (χ : (G.inverseImage (ObjectProperty.homMk jW : V ⟶ W)).toLAdicSheaf ⟶ FV.toLAdicSheaf)
    (_ : ∀ o : O, ((G.inverseImage (ObjectProperty.homMk jW : V ⟶ W)).act o).asHom ≫ χ =
      χ ≫ (FV.act o).asHom)
    -- the representation of `F_V` (the data of `exists_restrictScalarsRep_of_isLisse`)
    (r : ℕ) (ρ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : FV.toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V _ ρ hρ)
    (ψ : LAdicSheaf.representationSheaf B V _ ρ hρ ⟶ FV.toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (m : ℕ) (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin m) E)
    (Pm : Matrix (Fin r) (Fin (m * d)) ℚ_[ℓ]) (Qm : Matrix (Fin (m * d)) (Fin r) ℚ_[ℓ])
    (_ : Pm * Qm = 1)
    (_ : ∀ e : E, Qm * isogenyCoefficientAlgHom B V _ FV ρ hρ φ ψ N E hφψ hψφ hOE e * Pm =
      restrictScalarsMatrix b (Matrix.scalar (Fin m) e))
    (_ : ∀ g, Qm * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (haveI := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
          (V.1.residueField (genericPoint V.1)) Ω).map
            (V.1.fromSpecResidueField (genericPoint V.1)))
         integralModel ρ hρ g)).val * Pm = (restrictScalarsRep b τ g).val)
    -- no punctual sections at `y`, through `χ`
    (M : ℕ)
    (_ : ∀ (n : ℕ) (w : finiteLevelStalk B W ℓ G.toLAdicSheaf
        (Stacks.Frobenius.geometricPointAt W.1 y) n),
      (levelAdjunctStalkMap (ObjectProperty.homMk jW : V ⟶ W)
        (Stacks.Frobenius.geometricPointAt W.1 y) G.toLAdicSheaf FV.toLAdicSheaf χ n).hom w = 0 →
        (ℓ ^ M) • w = 0),
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    letI := G.rationalStalkModule (Stacks.Frobenius.geometricPointAt W.1 y) E
    ∃ sp : LAdicSheaf.rationalStalkLeft B W ℓ G.toLAdicSheaf
        (Stacks.Frobenius.geometricPointAt W.1 y) →ₗ[E]
        Representation.invariants ((matrixRepresentation τ).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype),
      Function.Injective sp ∧
      sp ∘ₗ G.rationalStalkFrobenius E y hyf =
        ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
          GL (Fin m) E) : Matrix (Fin m) (Fin m) E)).restrict
        (toLin'_mem_invariants_of_mem_normalizer τ
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
          (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
            (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) ∘ₗ sp


attribute [local instance] moduleCat_hasLimitsOfSize

/-- Scalar multiplication by `ℓ ^ k ∈ ℤ_[ℓ]` is the `ℓ ^ k`-fold natural multiple. -/
private theorem padic_pow_smul_eq_nsmul {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M]
    [Module ℤ_[ℓ] M] (k : ℕ) (w : M) : (ℓ ^ k : ℤ_[ℓ]) • w = (ℓ ^ k) • w := by
  rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow]

/-- **`Stacks.EtaleCohomology.CurveSpecializationMapInput` holds.** -/
theorem curveSpecializationMapInput : CurveSpecializationMapInput.{u} := by
  intro B V ℓ _ _ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓp W _ fW _ _ _ _ eW _
    heW jW _ hjW y hyc hyV hy L Ω _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ eA hA P _ Fr hFrD hFr hyf
    O _ _ G E _ _ _ _ _ hOE d b FV χ hχ r ρ hρ φ ψ N hφψ hψφ m τ Pm Qm hPQ hα hτ M hker
  let := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
    (integralClosure A L)
  have : Finite (W.1.residueField y) := hyf
  let x : GeometricPoint V.1 := (algebraicClosureGeometricPoint
    (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
  have := compactSpace_etaleFundamentalGroup V.1 x
  let ρ₀ := integralModel ρ hρ
  have hρ₀ : Continuous ρ₀ := continuous_integralModel ρ hρ
  let s : GeometricPoint W.1 := Stacks.Frobenius.geometricPointAt W.1 y
  let jV : V ⟶ W := ObjectProperty.homMk jW
  let ℱ := LAdicSheaf.representationSheaf B V x ρ hρ
  let χ' : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage jV G.toLAdicSheaf ⟶
    FV.toLAdicSheaf := χ
  have hφψ' : φ ≫ ψ = (ℓ ^ N) • 𝟙 FV.toLAdicSheaf := hφψ
  obtain ⟨ε, hε1, hε2, hε3, hε4, hε5, hε7⟩ := curvePointInertiaStalkRangeInput.{u} B V ℓ k f j
    kbar p n hcard hℓp W fW eW heW jW hjW y hyc hyV hy L Ω A eA hA P Fr hFrD hFr r ρ₀ hρ₀
  let Pn : ∀ n : ℕ, _ := fun n => levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ (χ' ≫ φ) n
  let S : ∀ n : ℕ, finiteLevelStalk B W ℓ G.toLAdicSheaf s n →+ (Fin r → ZMod (ℓ ^ (n + 1))) :=
    fun n => (ε n).comp (Pn n).hom.toAddMonoidHom
  have hSdef : ∀ n w, S n w = ε n ((Pn n).hom w) := fun _ _ => rfl
  have hS : ∀ n (c : ℤ_[ℓ]) (w : finiteLevelStalk B W ℓ G.toLAdicSheaf s n),
      S n (c • w) = PadicInt.toZModPow (n + 1) c • S n w := by
    intro n c w
    rw [hSdef, hSdef, show (Pn n).hom (c • w) = c • (Pn n).hom w from (Pn n).hom.map_smul c w]
    exact hε2 n c _
  have hT : ∀ n (w : finiteLevelStalk B W ℓ G.toLAdicSheaf s (n + 1)),
      S n (LAdicSheaf.stalkTransition B W ℓ G.toLAdicSheaf s n w) =
        levelReduction (n + 1) (S (n + 1) w) := by
    intro n w
    rw [hSdef, hSdef]
    change ε n ((levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ (χ' ≫ φ) n).hom
      (LAdicSheaf.stalkTransition B W ℓ G.toLAdicSheaf s n w)) = _
    rw [levelAdjunctPadicStalkMap_transition]
    exact hε3 n _
  let sI := LAdicSheaf.stalkLevelLimitMap S hS hT
  have hχφψ : (χ' ≫ φ) ≫ ψ = (ℓ ^ N) • χ' := by
    rw [Category.assoc, hφψ', Preadditive.comp_nsmul, Category.comp_id]
  have hM : ∀ n (w : finiteLevelStalk B W ℓ G.toLAdicSheaf s n), S n w = 0 →
      (ℓ ^ (M + N) : ℤ_[ℓ]) • w = 0 := by
    intro n w hw
    have h1 : (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ (χ' ≫ φ) n).hom w = 0 :=
      hε1 n (hw.trans (map_zero _).symm)
    have h2 : (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf FV.toLAdicSheaf
        ((χ' ≫ φ) ≫ ψ) n).hom w = 0 :=
      (levelAdjunctPadicStalkMap_comp jV s _ (χ' ≫ φ) ψ n w).trans (by rw [h1, map_zero])
    rw [hχφψ, levelAdjunctPadicStalkMap_nsmul] at h2
    have h2' : (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf FV.toLAdicSheaf χ' n).hom
        ((ℓ ^ N) • w) = 0 :=
      (map_nsmul (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf FV.toLAdicSheaf χ' n).hom
        (ℓ ^ N) w).trans h2
    calc (ℓ ^ (M + N) : ℤ_[ℓ]) • w = (ℓ ^ (M + N)) • w := padic_pow_smul_eq_nsmul _ w
      _ = (ℓ ^ M) • ((ℓ ^ N) • w) := by rw [pow_add ℓ M N, smul_smul]
      _ = 0 := hker n _ (levelAdjunctStalkMap_eq_zero_of_padic jV s _ _ χ' n _ h2')
  have hker' : ∀ v, sI v = 0 → (ℓ ^ (M + N) : ℤ_[ℓ]) • v = 0 :=
    LAdicSheaf.pow_smul_eq_zero_of_stalkLevelLimitMap_eq_zero S hS hT (M + N) hM
  have hsv : ∀ (v : LAdicSheaf.stalk B W ℓ G.toLAdicSheaf s) (n : ℕ),
      (fun i => PadicInt.toZModPow (n + 1) (sI v i)) = S n (v.1 n) := fun v n =>
    funext fun i => LAdicSheaf.toZModPow_stalkLevelLimitMap S hS hT v n i
  have hmv : ∀ (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (v : LAdicSheaf.stalk B W ℓ G.toLAdicSheaf s)
      (n : ℕ), A.map (PadicInt.toZModPow (n + 1)) *ᵥ S n (v.1 n) =
        fun i => PadicInt.toZModPow (n + 1) ((A *ᵥ sI v) i) := by
    intro A v n
    funext i
    rw [RingHom.map_mulVec, ← hsv v n]
    rfl
  let := G.rationalStalkModule s E
  have := G.rationalStalkModule_isScalarTower s E hOE
  have hact : ∀ (o : O) (v : LAdicSheaf.stalk B W ℓ G.toLAdicSheaf s),
      algebraMap O E o • ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v) =
        (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] LAdicSheaf.stalkMap (G.act o).asHom s v := by
    intro o v
    change G.rationalStalkRingHom s E (algebraMap O E o) ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v) = _
    rw [G.rationalStalkRingHom_algebraMap_apply]
    exact LinearMap.baseChange_tmul _ _ _
  have hO : ∀ (o : O) (v : LAdicSheaf.stalk B W ℓ G.toLAdicSheaf s),
      (ℓ ^ N : ℤ_[ℓ]) • sI (LAdicSheaf.stalkMap (G.act o).asHom s v) =
        isogenyCoefficientMatrix B V x FV ρ hρ φ ψ o *ᵥ sI v := by
    intro o v
    rw [← map_smul, LAdicSheaf.stalkLevelLimitMap_eq_iff]
    intro n
    let w := v.1 n
    let θ := (isogenyCoefficientEnd B V x FV ρ hρ φ ψ o).asHom
    have hθ : (χ' ≫ φ) ≫ θ = (ℓ ^ N) • (χ' ≫ (FV.act o).asHom ≫ φ) := by
      change (χ' ≫ φ) ≫ ψ ≫ (FV.act o).asHom ≫ φ = _
      rw [Category.assoc, ← Category.assoc φ, hφψ', Preadditive.nsmul_comp, Category.id_comp,
        Preadditive.comp_nsmul]
    have hsrc :
        AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap jV (G.act o).asHom ≫ χ' ≫ φ =
        χ' ≫ (FV.act o).asHom ≫ φ := by
      have h : AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap jV (G.act o).asHom ≫ χ' =
          χ' ≫ (FV.act o).asHom := hχ o
      rw [← Category.assoc, h, Category.assoc]
    have e1 : (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ (χ' ≫ φ) n).hom
        ((finiteLevelStalkMap (G.act o).asHom s n).hom w) =
        (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ (χ' ≫ (FV.act o).asHom ≫ φ) n).hom w := by
      rw [← hsrc]
      exact (levelAdjunctPadicStalkMap_inverseImageMap_comp jV s (G.act o).asHom (χ' ≫ φ) n w).symm
    have e2a := levelAdjunctPadicStalkMap_nsmul jV s G.toLAdicSheaf ℱ (χ' ≫ (FV.act o).asHom ≫ φ) n
      (ℓ ^ N) w
    have e2b : (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ ((χ' ≫ φ) ≫ θ) n).hom w =
        (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ
          ((ℓ ^ N) • (χ' ≫ (FV.act o).asHom ≫ φ)) n).hom w :=
      congrArg (fun c => (levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ c n).hom w) hθ
    have e3 := levelAdjunctPadicStalkMap_comp jV s G.toLAdicSheaf (χ' ≫ φ) θ n w
    have heq := isogenyCoefficientEnd_eq_representationLAdicSheafMap B V x FV ρ hρ φ ψ o
    have h4 := hε4 (isogenyCoefficientMatrix B V x FV ρ hρ φ ψ o)
      (isogenyCoefficientMatrix_mul B V x FV ρ hρ φ ψ o) n
      ((levelAdjunctPadicStalkMap jV s G.toLAdicSheaf ℱ (χ' ≫ φ) n).hom w)
    rw [← heq] at h4
    exact (hS n _ _).trans ((congrArg (fun z => PadicInt.toZModPow (n + 1) (ℓ ^ N : ℤ_[ℓ]) • ε n z)
      e1).trans ((hε2 n _ _).symm.trans ((congrArg (ε n)
        ((padic_pow_smul_eq_nsmul N _).trans (e2a.symm.trans (e2b.symm.trans e3)))).trans
          (h4.trans (hmv _ v n)))))
  have hα' : ∀ o, Qm * (((ℓ : ℚ_[ℓ]) ^ N)⁻¹ •
      (isogenyCoefficientMatrix B V x FV ρ hρ φ ψ o).map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) * Pm =
      restrictScalarsMatrix b (Matrix.scalar (Fin m) (algebraMap O E o)) := by
    intro o
    have h := hα (algebraMap O E o)
    rwa [isogenyCoefficientAlgHom_algebraMap] at h
  have hτ' : ∀ g, Qm * (ρ₀ g).val.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) * Pm =
      restrictScalarsMatrix b (τ g : Matrix (Fin m) (Fin m) E) := fun g => hτ g
  have hinv : ∀ v, ∀ g ∈ Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P,
      (ρ₀ g).val *ᵥ sI v = sI v := by
    intro v g hg
    refine ((LAdicSheaf.stalkLevelLimitMap_eq_iff S hS hT v _).2 fun n => ?_).symm
    exact (hε7 n _ g hg).symm.trans (hmv _ v n)
  let Fs := LAdicSheaf.stalkEnd B W ℓ G.toLAdicSheaf (Stacks.Frobenius.frobeniusPointHom W.1 y)
  let gF := (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹
  have hF : ∀ v, sI (Fs v) = (ρ₀ gF).val *ᵥ sI v := by
    intro v
    refine (LAdicSheaf.stalkLevelLimitMap_eq_iff S hS hT _ _).2 fun n => ?_
    exact (congrArg (ε n) (levelAdjunctPadicStalkMap_stalkEnd jV s G.toLAdicSheaf ℱ (χ' ≫ φ) n
      (Stacks.Frobenius.frobeniusPointHom W.1 y) (v.1 n))).trans ((hε5 n _).trans (hmv _ v n))
  have hFE : ∀ v, G.rationalStalkFrobenius E y hyf ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] Fs v := fun v =>
    LAdicSheaf.rationalStalkEnd_tmul B W ℓ G.toLAdicSheaf
      (Stacks.Frobenius.frobeniusPointHom W.1 y) 1 v
  exact exists_linearMap_invariants_of_integral b
    (fun o => LAdicSheaf.stalkMap (G.act o).asHom s) hact sI (M + N) hker' N
    (fun o => isogenyCoefficientMatrix B V x FV ρ hρ φ ψ o) hO Pm Qm hPQ hα'
    (fun g => (ρ₀ g).val) τ hτ' (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P) hinv
    Fs gF hF (G.rationalStalkFrobenius E y hyf) hFE
    (toLin'_mem_invariants_of_mem_normalizer τ
      (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
      (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
        (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))

/-- **`Stacks.EtaleCohomology.CurveSpecializationInput` holds.** -/
theorem curveSpecializationInput : CurveSpecializationInput.{u} := by
  intro B V ℓ _ _ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓp W _ fW _ _ _ _ eW _
    heW jW _ hjW y hyc hyV hy L Ω _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ eA hA P _ Fr hFrD hFr hyf
    O _ _ G E _ _ _ _ _ hOE d b r ρ hρ φ ψ N hφψ hψφ m τ Pm Qm _ hPQ _ hα hτ M hker
  exact curveSpecializationMapInput B V ℓ k f j kbar p n hcard hℓp W fW eW heW jW hjW y hyc hyV hy
    L Ω A eA hA P Fr hFrD hFr hyf G E hOE b (G.inverseImage (ObjectProperty.homMk jW : V ⟶ W))
    (𝟙 _) (fun o => by rw [Category.comp_id, Category.id_comp]) r ρ hρ φ ψ N hφψ hψφ m τ Pm Qm hPQ
    hα hτ M (fun n w h => hker n w ((congrArg (fun g => g.hom w)
      (levelAdjunctStalkMap_id (ObjectProperty.homMk jW : V ⟶ W)
        (Stacks.Frobenius.geometricPointAt W.1 y) G.toLAdicSheaf n)).symm.trans h))

end Stacks.EtaleCohomology

end
