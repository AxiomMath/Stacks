module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLatticeChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientTwistedTraceFormulaPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTraceFormulaPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve

/-!
# The `E`-linear trace formula on a smooth curve

This proves `Stacks.EtaleCohomology.CurveLinearTraceFormulaInput`: for `σ : π₁(U, x̄) → GL_m(E)`
with `E` finite over `ℚ_ℓ`, `∑_{deg y ∣ N} deg y · tr σ(F_y)^{N / deg y}` is the alternating sum
of the `E`-traces of `(π_U^*)^N` on `Hⁱ_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`.

Both sides are elements of `E`, so it suffices that their traces against every `c` of
`O ∩ O_E` agree (`Stacks.EtaleCohomology.eq_of_forall_trace_mul_eq`), `O` the integral part of `E`
acting on `ℱ_{Res_b σ}` and `O_E` the ring of integers. On the cohomological side,
`Tr_{E/ℚ_ℓ}(c · Tr_E(φ)) = Tr_{ℚ_ℓ}(c ∘ φ)`, the twisted traces of `ℱ_{Res_b σ}` are those of the
sheaf of the model of `σ` over `O_E`
(`Stacks.EtaleCohomology.trace_rationalIntegralRingHom_restrictScalarsRep_eq_model`), which are
computed by the twisted trace formula
(`Stacks.EtaleCohomology.alternating_trace_coefficientScalar_comp_pow`) in terms of
`Tr_{O_E/ℤ_ℓ}(c · tr σ'(F_y)^{N / deg y}) = Tr_{E/ℚ_ℓ}(c · tr σ(F_y)^{N / deg y})`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.curveLinearTraceFormulaInput`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Module

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- The trace of an endomorphism of a module which is not finite is zero. -/
public theorem LinearMap.trace_eq_zero_of_not_finite' {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (h : ¬ Module.Finite R M) (φ : M →ₗ[R] M) : LinearMap.trace R M φ = 0 := by
  classical
  rw [LinearMap.trace, dite_eq_right]
  · rfl
  rintro ⟨s, ⟨b⟩⟩
  exact h (Module.Finite.of_basis b)

/-- **A linear form commutes with the sum over the closed points of degree dividing `N`.** -/
public theorem map_finsum_residueDegree_dvd {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] {M M' : Type*}
    [AddCommMonoid M] [AddCommMonoid M'] (L : M →+ M') (g : closedPoints X → M) (N : ℕ)
    (hN : 0 < N) :
    L (∑ᶠ (y : closedPoints X) (_ : residueDegree f y.1 ∣ N), g y) =
      ∑ᶠ (y : closedPoints X) (_ : residueDegree f y.1 ∣ N), L (g y) := by
  classical
  set S := (closedPointsDegreeLE f N).filter (fun y => residueDegree f y.1 ∣ N)
  have hS : ∀ {y : closedPoints X}, y ∈ S ↔ residueDegree f y.1 ∣ N := by
    intro y
    rw [Finset.mem_filter]
    simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨And.right, fun hy => ⟨Nat.le_of_dvd hN hy, hy⟩⟩
  rw [finsum_cond_eq_sum_of_cond_iff (t := S) _ fun _ => hS.symm,
    finsum_cond_eq_sum_of_cond_iff (t := S) _ fun _ => hS.symm, map_sum]

section Curve

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
  [IsNoetherian X.1]

omit [IsSeparated f] in
/-- **On a smooth curve the alternating sum of traces of any family of endomorphisms of
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` runs over `i ∈ {0, 1, 2}`.** -/
public theorem LAdicSheaf.finsum_sign_trace_eq_sum_range_three [SmoothOfRelativeDimension 1 f]
    (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (φ : ∀ i : ℤ,
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _ (φ i) =
      ∑ i ∈ Finset.range 3, (-1 : ℚ_[ℓ]) ^ i * LinearMap.trace ℚ_[ℓ] _ (φ (i : ℤ)) := by
  have hz : ∀ i : ℤ, (i < 0 ∨ 2 < i) → LinearMap.trace ℚ_[ℓ] _ (φ i) = 0 := by
    intro i hi
    have : Subsingleton
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
      rcases hi with h | h
      · exact ModuleCat.subsingleton_of_isZero
          (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg B X ℓ f j kbar
            F i h)
      · exact LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_two_lt B X
          ℓ f j kbar F i h
    rw [Subsingleton.elim (φ i) 0, map_zero]
  have hs : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (0 : ℤ) 2) ?_]
  · rw [hs, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [add_assoc]
    rfl
  · intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra h
    exact hi (by rw [hz i (by omega), mul_zero])

end Curve

section ETrace

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
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
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The `E`-trace of `(π_X^*)^N`, twisted by `o ∈ O` and traced down to `ℚ_ℓ`, is the
`ℚ_ℓ`-trace of `o ∘ (π_X^*)^N`.** -/
public theorem trace_mul_trace_rationalGeometricCompactlySupportedFrobenius_pow
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (o : O) (N : ℕ) :
    letI := F.rationalCohomologyModule f j kbar i E
    Algebra.trace ℚ_[ℓ] E (algebraMap O E o * LinearMap.trace E _
        ((F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard) ^ N)) =
      LinearMap.trace ℚ_[ℓ] _ (F.rationalIntegralRingHom f j kbar i o ∘ₗ
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          F.toLAdicSheaf i).hom ^ N) := by
  let := F.rationalCohomologyModule f j kbar i E
  let := F.rationalCohomologyModule_isScalarTower f j kbar i E hOE
  have hpow : ∀ v, ((F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard) ^ N) v =
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F.toLAdicSheaf i).hom ^ N) v := by
    induction N with
    | zero => exact fun v => rfl
    | succ N ih =>
        intro v
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
        rfl
  have hφ : ((algebraMap O E o • (F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q
      hcard) ^ N).restrictScalars ℚ_[ℓ]) =
      F.rationalIntegralRingHom f j kbar i o ∘ₗ
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          F.toLAdicSheaf i).hom ^ N := by
    refine LinearMap.ext fun v => ?_
    change F.rationalRingHom f j kbar i E (algebraMap O E o)
      (((F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard) ^ N) v) = _
    rw [hpow, F.rationalRingHom_algebraMap_apply]
    rfl
  by_cases hfin : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
    f j kbar F.toLAdicSheaf i)
  · rw [← trace_restrictScalars_smul_eq, hφ]
  · rw [LinearMap.trace_eq_zero_of_not_finite' hfin, mul_zero, map_zero,
      LinearMap.trace_eq_zero_of_not_finite']
    intro h
    exact hfin (Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _)

end ETrace

/-- **The `E`-linear trace formula on a smooth curve** ([Stacks, Tag 03V2] with coefficients in a
finite extension `E` of `ℚ_ℓ`): `Stacks.EtaleCohomology.CurveLinearTraceFormulaInput`. -/
public theorem curveLinearTraceFormulaInput : CurveLinearTraceFormulaInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b m σ hσ
    N hN
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := (Algebra.charP_iff k kbar p).1 inferInstance
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have := compactSpace_etaleFundamentalGroup U.1 x
  let := padicIntAlgebraOfRat ℓ E
  have hgc : GeometricallyConnected f :=
    (geometricallyConnected_iff_connectedSpace_baseChange k kbar f).2 ‹_›
  have hdim : topologicalKrullDim U.1 ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rcases isEmpty_or_nonempty U.1 with hX | hX
    · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hX]
      exact bot_le
    · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  set P := representationSheafConj B U x (restrictScalarsRep b σ) hσ
  set α := restrictScalarsScalarAlgHom b m
  refine eq_of_forall_trace_mul_eq (ℓ := ℓ) {c : E | ∃ c0 : conjIntegralSubring P α,
      ∃ c' : integralClosure ℤ_[ℓ] E, (c0 : E) = c ∧ (c' : E) = c} ?_ _ _ ?_
  · intro e
    obtain ⟨t, ht, h1, h2⟩ := exists_smul_mem_conjIntegralSubring_padicIntegerRing P α e
    exact ⟨t, ht, ⟨t • e, h1⟩, ⟨t • e, h2⟩, rfl, rfl⟩
  rintro c ⟨c0, c', rfl, hc'⟩
  have hT := alternating_trace_coefficientScalar_comp_pow (padicIntegerRingBasisOf b) B U x
    (modelRep b σ hσ) (continuous_modelRestrictScalarsRep b σ hσ) f j kbar p n hcard hℓp hdim hgc
    c' N hN.ne'
  have hL : Algebra.trace ℚ_[ℓ] E ((c0 : E) *
      ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : E) *
        (((σ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace) =
      ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : ℚ_[ℓ]) *
        algebraMap ℤ_[ℓ] ℚ_[ℓ] (Algebra.trace ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) (c' *
          ((modelRep b σ hσ (geometricFrobeniusFamily f x y)).val ^
            (N / residueDegree f y.1)).trace)) := by
    refine (map_finsum_residueDegree_dvd f ((Algebra.trace ℚ_[ℓ] E).toAddMonoidHom.comp
      (AddMonoidHom.mulLeft (c0 : E))) _ N hN).trans
      (finsum_congr fun y => finsum_congr fun _ => ?_)
    change Algebra.trace ℚ_[ℓ] E ((c0 : E) * ((residueDegree f y.1 : E) * _)) = _
    rw [algebraMap_trace_padicIntegerRing b, MulMemClass.coe_mul, hc']
    have htr : ((((modelRep b σ hσ (geometricFrobeniusFamily f x y)).val ^
        (N / residueDegree f y.1)).trace : integralClosure ℤ_[ℓ] E) : E) =
        (((σ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace := by
      rw [← trace_map_modelRep_pow b σ hσ]
      exact AddMonoidHom.map_trace (algebraMap (integralClosure ℤ_[ℓ] E) E) _
    rw [htr, show (residueDegree f y.1 : E) = algebraMap ℚ_[ℓ] E (residueDegree f y.1 : ℚ_[ℓ]) from
      (map_natCast _ _).symm, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  refine hL.trans (hT.trans ?_)
  rw [Finset.mul_sum, map_sum]
  refine (LAdicSheaf.finsum_sign_trace_eq_sum_range_three B U ℓ f j kbar _ (fun i =>
    LAdicSheaf.rationalCohomologyMap f j kbar
      (representationLAdicSheafMap B U x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B U x)
        (continuous_modelRestrictScalarsRep b σ hσ) (continuous_modelRestrictScalarsRep b σ hσ)
        (coefficientScalarRingHom (padicIntegerRingBasisOf b) m c')
        (fun g => coefficientScalarRingHom_commute (padicIntegerRingBasisOf b) m c'
          (modelRep b σ hσ g).val)) i ∘ₗ
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
        (representationLAdicSheaf B U x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B U x)
          (modelRestrictScalarsRep b σ hσ) (continuous_modelRestrictScalarsRep b σ hσ)) i).hom ^
        N)).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_left_comm, show ((-1 : E) ^ i) = algebraMap ℚ_[ℓ] E ((-1 : ℚ_[ℓ]) ^ i) by simp,
    ← Algebra.smul_def, map_smul, smul_eq_mul]
  congr 1
  rw [show (c0 : E) = algebraMap (conjIntegralSubring P α) E c0 from rfl,
    trace_mul_trace_rationalGeometricCompactlySupportedFrobenius_pow _ f j kbar (i : ℤ) E
      (algebraMap_conjIntegralSubring_algebraMap _ _) p n hcard c0 N]
  exact (trace_rationalIntegralRingHom_restrictScalarsRep_eq_model B U x b σ hσ f j kbar p n hcard
    c0 c' hc'.symm (i : ℤ) N).symm

end Stacks.EtaleCohomology

end
