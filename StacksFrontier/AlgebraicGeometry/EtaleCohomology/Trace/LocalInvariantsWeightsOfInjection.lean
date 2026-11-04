module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearDegreeOneWeakBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineOpenPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SmoothAffineCurveCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectCurveFinite

/-!
# Weil II 1.8.4 at a missing point of a curve from the injection of the local invariants

Weil II 1.8: for `V ⊆ W ⊆ 𝔸¹_k` and `y ∈ W ∖ V`, the `E`-subspace of `τ(I_y)`-invariants
(`H⁰_loc`, the stalk of `j_* ℱ_τ` at `ȳ`) maps injectively and `E`-linearly into
`H¹_c(V_k̄, ℱ_{Res_b τ} ⊗ ℚ_ℓ)`, carrying the geometric Frobenius at `y` to `(π^*) ^ deg y`
(`Stacks.EtaleCohomology.CurveLocalInvariantsInjectionInput`). Since `H¹_c` has weights
`≤ w' + 2` for every `τ` mixed of weights `≤ w'` (the `E`-linear trace formula, `H⁰_c = 0`,
`H²_c` the twisted coinvariants, and `#V(k_N) ≤ q ^ N`), the weak estimate of Weil II 1.8.4
holds, and with it Weil II 1.8.4 (`Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput`).

## Main definitions

* `Stacks.EtaleCohomology.CurveLocalInvariantsInjectionInput`.

## Main results

* `Stacks.EtaleCohomology.curveLocalInvariantsWeightInput_of_injection`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale
open scoped Pointwise

universe u

namespace Stacks.EtaleCohomology

/-- **The local invariants inject into `H¹_c`** (Weil II 1.8, `H⁰_loc ⊆ H¹_c`): in the setting of
`Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput`, there is an injective `E`-linear map from
the `E`-subspace of `τ(I_y)`-invariants to `H¹_c(V_k̄, ℱ_{Res_b τ} ⊗ ℚ_ℓ)` intertwining the
geometric Frobenius `τ(φ Fr⁻¹)` at `y` with `(π^*) ^ deg y`, where `#κ(y) = q ^ deg y`. -/
public def CurveLocalInvariantsInjectionInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Fintype k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    -- the curve `W ⊇ V` and the missing point `y`
    (W : B.Scheme) (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW]
    [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
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
    -- the representation
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
    (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin m) E)
    (hτ : Continuous (restrictScalarsRep b τ)),
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    letI := (restrictScalarsRepCoefficientSheaf B V ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        b τ hτ).rationalCohomologyModule f j kbar 1 E
    ∃ dy : ℕ, 0 < dy ∧ Nat.card (IsLocalRing.ResidueField A) = (p ^ n) ^ dy ∧
      ∃ J : Representation.invariants ((matrixRepresentation τ).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype) →ₗ[E]
          LAdicSheaf.rationalGeometricCompactlySupportedCohomology B V ℓ f j kbar
            (restrictScalarsRepCoefficientSheaf B V ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
              b τ hτ).toLAdicSheaf 1,
        Function.Injective J ∧
        J ∘ₗ ((Matrix.toLin' ((τ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹) :
            GL (Fin m) E) : Matrix (Fin m) (Fin m) E)).restrict
          (toLin'_mem_invariants_of_mem_normalizer τ
            (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P)
            (map_inv_mem_normalizer_map_inertia A (V.1.residueField (genericPoint V.1)) L P
              (galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr hFrD))) =
          (((restrictScalarsRepCoefficientSheaf B V ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
              b τ hτ).rationalGeometricCompactlySupportedFrobenius
            f j kbar 1 E p n hcard) ^ dy) ∘ₗ J

/-- **Weil II 1.8.4 at a missing point of a curve, from the injection of the local invariants**,
the `E`-linear trace formula and the `E`-linear identification of `H²_c` with the twisted
coinvariants. -/
public theorem curveLocalInvariantsWeightInput_of_injection
    (hD8 : CurveLinearTraceFormulaInput.{u}) (hC : CurveLinearCoinvariantsInput.{u})
    (hinj : CurveLocalInvariantsInjectionInput.{u}) : CurveLocalInvariantsWeightInput.{u} := by
  intro B V ℓ _ _ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓp W fW _ _ _ _ eW _ heW
    jW _ hjW y hyc hyV hy L Ω _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ eA hA P _ Fr hFrD hFr E _ _ _ d b
    m τ hτ ι' w hpure
  classical
  let := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
    (integralClosure A L)
  let x : GeometricPoint V.1 := (algebraicClosureGeometricPoint
    (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
  have : Nonempty V.1 := ⟨genericPoint V.1⟩
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hdim : topologicalKrullDim V.1 ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  have hq₀ : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) := by exact_mod_cast pow_pos (Fact.out : p.Prime).pos n
  -- the residue characteristic at `y` is `p`
  obtain ⟨dy₀, hdy₀, hcardA, -⟩ := hinj B V ℓ k f j kbar p n hcard hℓp W fW eW heW jW hjW y hyc hyV
    hy L Ω A eA hA P Fr hFrD hFr E b τ hτ
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := k)
    rw [hcard, pow_zero] at this
    exact lt_irrefl _ this
  have hℓA : ℓ ≠ ringChar (IsLocalRing.ResidueField A) := by
    have : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
    obtain ⟨r, hr, s, hrp, hcs⟩ := FiniteField.card' (IsLocalRing.ResidueField A)
    rw [← Nat.card_eq_fintype_card, hcardA, ← pow_mul] at hcs
    have hpr := (Nat.Prime.pow_inj' (Fact.out : p.Prime) hrp (mul_ne_zero hn0 hdy₀.ne')
      s.pos.ne' hcs).1
    rw [ringChar.eq (IsLocalRing.ResidueField A) r, ← hpr]
    exact hℓp
  refine isCharpolyNormMixedOfWeightLE_invariants_of_weakInertiaBound A
    (V.1.residueField (genericPoint V.1)) L P (G := EtaleFundamentalGroup V.1 x)
    (Frob := fun z : closedPoints V.1 => geometricFrobeniusFamily f x z)
    (deg := fun z : closedPoints V.1 => residueDegree f z.1) (q₀ := ((p ^ n : ℕ) : ℝ)) hℓA
    (galoisToFundamentalGroup V.1 L Ω).toMonoidHom (galoisToFundamentalGroup V.1 L Ω).continuous
    b τ hτ ι' Fr hFrD hFr hq₀ w (fun z c hc => by
      rw [hpure z c hc]
      norm_cast) ?_
  refine weakInertiaBound_of_forall_isRoot_charpoly_restrict A (V.1.residueField (genericPoint V.1))
    L P (galoisToFundamentalGroup V.1 L Ω).toMonoidHom b ι' Fr hFrD ?_
  intro N τ' hτ' w' hmix z hz
  obtain ⟨dy, hdy, hcardy, J, hJ, hJT⟩ := hinj B V ℓ k f j kbar p n hcard hℓp W fW eW heW jW hjW
    y hyc hyV hy L Ω A eA hA P Fr hFrD hFr E b τ' hτ'
  let F := restrictScalarsRepCoefficientSheaf B V x b τ' hτ'
  let := F.rationalCohomologyModule f j kbar 1 E
  have := F.rationalCohomologyModule_isScalarTower f j kbar 1 E
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : ∀ i, Module.Finite ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B V ℓ
      f j kbar F.toLAdicSheaf i) := fun i =>
    LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one
      B V ℓ f j kbar p n hcard hdim F.toLAdicSheaf i
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B V ℓ f j
      kbar F.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  -- `H⁰_c = 0`
  have h0 : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B V ℓ f j kbar
      F.toLAdicSheaf 0) :=
    open LAdicSheaf in
    subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_smoothOfRelativeDimension
      B V ℓ f j kbar F.toLAdicSheaf (LAdicSheaf.representationSheaf_isLisse B V x _ _)
  -- `H²_c`
  obtain ⟨φ₀, hφ₀⟩ := AlgebraicGeometry.exists_etaleFundamentalGroupMap_eq_finiteFieldFrobenius_inv
    p n hcard f x kbar
  obtain ⟨e, he⟩ := hC B V ℓ k f j kbar p n hcard hℓp x E b τ' hτ' φ₀ hφ₀
  have h2 := norm_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_two_linear B V ℓ k f j
    kbar p n hcard x E b τ' hτ' ι' hmix φ₀ hφ₀ e he
  -- the point count
  have hpt : ∀ N : ℕ, 0 < N →
      (∑ᶠ (z : closedPoints V.1) (_ : residueDegree f z.1 ∣ N), (residueDegree f z.1 : ℝ)) ≤
        1 * ((p ^ n : ℕ) : ℝ) ^ N := fun N hN => by
    rw [one_mul, ← hcard]
    exact finsum_residueDegree_le_of_isOpenImmersion_affineLine p f (jW ≫ eW)
      (by rw [Category.assoc, heW, hjW]) N hN
  have h1 := norm_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_one_linear B V ℓ k f j
    kbar p n hcard x E b τ' hτ' hD8 hℓp ι' w' hmix h0 h2 hpt
  have := norm_le_pow_of_isRoot_charpoly_of_injective ι' _ _ J hJ hdy hJT h1 z hz
  refine this.trans (le_of_eq ?_)
  rw [hcardy, Nat.cast_pow (p ^ n) dy, ← Real.rpow_natCast (((p ^ n : ℕ) : ℝ) ^ ((w' + 2) / 2)) dy,
    ← Real.rpow_mul hq₀.le, ← Real.rpow_natCast ((p ^ n : ℕ) : ℝ) dy, ← Real.rpow_mul hq₀.le,
    mul_comm]

end Stacks.EtaleCohomology

end
