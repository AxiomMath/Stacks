module

public import StacksFrontier.NumberTheory.Drinfeld.SupersingularCuspForm
public import StacksFrontier.NumberTheory.Drinfeld.EqualCharacteristicEigenform
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassCurveExists
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FunctionField
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap

/-!
# Theorem 03VT is false as written for `ℓ = p`

Let `X₀ ⊆ ℙ²_{𝔽₂}` be the supersingular elliptic curve `y² + y = x³ + x + 1`. It is a smooth
proper geometrically irreducible curve over `𝔽₂`, its function field is
`Stacks.Drinfeld.SupersingularCurve.K`, and its module `C(Ω)` of unramified cusp forms with
`q_v · U_v f = f` is nonzero (`Stacks.Drinfeld.SupersingularCurve.cuspFormsCentralChar_ne_bot`).
Hence the reduction
`Stacks.Drinfeld.exists_eigenform_not_isFrobeniusCompatible_of_cuspFormsCentralChar_ne_bot`
applies: for `ℓ = p = 2` there is an eigenform satisfying the hypotheses of Stacks Theorem 03VT
with no compatible `ℓ`-adic representation.

## Main results

* `Stacks.Drinfeld.SupersingularCurve.functionFieldEquiv` — `K ≃+* k(X₀)`, through the affine
  chart `z ≠ 0`, whose coordinate ring has fraction field `K`.
* `Stacks.Drinfeld.SupersingularCurve.instGeometricallyIrreducibleF₀` — `𝔽₂` is algebraically
  closed in `K` (Stacks 054Q).
* `Stacks.Drinfeld.SupersingularCurve.exists_eigenform_not_isFrobeniusCompatible` — the
  counterexample to 03VT for `ℓ = p`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Stacks.Adeles Stacks.Adeles.GlobalFunctionField
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass IntermediateField

namespace Stacks.Drinfeld.SupersingularCurve

/-- The function field of `Spec R` is any fraction field of `R`. -/
public def _root_.AlgebraicGeometry.specFunctionFieldEquiv (R : CommRingCat.{0}) [IsDomain R]
    (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] : (Spec R).functionField ≃+* L :=
  (IsLocalization.algEquiv (nonZeroDivisors R) (Spec R).functionField L).toRingEquiv

/-! ### Constants of `K` -/

/-- **`𝔽₂` is algebraically closed in `K`.** An element of `K` integral over `𝔽₂` lies in `𝔽₂`:
it is a root of unity or zero, hence integral at every place, hence in `L(0) ⊆ L(2∞) = 𝔽₂ + 𝔽₂ x`,
and it has no pole at infinity. -/
public theorem eq_algebraMap_of_isIntegral {z : K} (hz : IsIntegral (ZMod 2) z) :
    ∃ c : ZMod 2, z = algebraMap (ZMod 2) K c := by
  classical
  have := IntermediateField.adjoin.finiteDimensional hz
  have : Finite (ZMod 2)⟮z⟯ := Module.finite_of_finite (ZMod 2)
  let := Fintype.ofFinite (ZMod 2)⟮z⟯
  have hpow : z ^ Fintype.card (ZMod 2)⟮z⟯ = z := by
    have := FiniteField.pow_card (⟨z, mem_adjoin_simple_self (ZMod 2) z⟩ : (ZMod 2)⟮z⟯)
    exact congrArg Subtype.val this
  have hcard : 1 < Fintype.card (ZMod 2)⟮z⟯ := Fintype.one_lt_card
  have hv : ∀ v : Place K, z ∈ v.1 := by
    intro v
    by_contra hzv
    have hz0 : z ≠ 0 := fun h0 => hzv (h0 ▸ v.1.zero_mem)
    have hlt : 1 < v.1.valuation z := by
      rw [← not_le, ValuationSubring.valuation_le_one_iff]; exact hzv
    have h1 : z ^ (Fintype.card (ZMod 2)⟮z⟯ - 1) = 1 := by
      have : z ^ (Fintype.card (ZMod 2)⟮z⟯ - 1) * z = 1 * z := by
        rw [← pow_succ, Nat.sub_add_cancel hcard.le, hpow, one_mul]
      exact mul_right_cancel₀ hz0 this
    have h2 := congrArg v.1.valuation h1
    rw [map_pow, map_one] at h2
    exact (one_lt_pow₀ hlt (by omega)).ne' h2
  obtain ⟨c, d, hcd⟩ := eq_add_mul_x_of_mem z (fun v _ => hv v) fun h0 => by
    have := (Place.ord_nonneg_iff (isDiscrete (ZMod 2) infPlace) h0).2 (hv infPlace)
    omega
  rcases zmod_two_cases d with rfl | rfl
  · exact ⟨c, by rw [hcd, map_zero, zero_mul, add_zero]⟩
  · exfalso
    refine x_notMem_infPlace ?_
    have : x = z - algebraMap (ZMod 2) K c := by rw [hcd, map_one, one_mul, add_sub_cancel_left]
    rw [this]
    exact sub_mem (hv infPlace) (algebraMap_mem_place infPlace c)

/-- A field isomorphic to `K` has `𝔽₂` separably closed in it. -/
public theorem separableClosure_eq_bot_of_ringEquiv {L : Type*} [Field L] [Algebra (ZMod 2) L]
    (e : L ≃+* K) : separableClosure (ZMod 2) L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hint : IsIntegral (ZMod 2) z := (mem_separableClosure_iff.1 hz).isIntegral
  let eA : L →ₐ[ZMod 2] K :=
    { e.toRingHom with
      commutes' := fun r => RingHom.congr_fun
        (Subsingleton.elim (e.toRingHom.comp (algebraMap (ZMod 2) L)) (algebraMap (ZMod 2) K)) r }
  obtain ⟨c, hc⟩ := eq_algebraMap_of_isIntegral (hint.map eA)
  rw [IntermediateField.mem_bot]
  exact ⟨c, e.injective ((eA.commutes c).trans hc.symm)⟩

/-! ### The curve -/

/-- The Weierstrass curve `y² + y = x³ + x + 1` over `𝔽₂`. -/
public def W₀ : WeierstrassCurve (ZMod 2) := ⟨0, 0, 1, 1, 1⟩

public theorem W₀_Δ : W₀.Δ = 1 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, W₀]
  decide

public instance : W₀.IsElliptic := ⟨by rw [W₀_Δ]; exact isUnit_one⟩

/-- The plane cubic `X₀ : y² + y = x³ + x + 1` in `ℙ²_{𝔽₂}`. -/
public abbrev X₀ : Scheme.{0} := projOf W₀

/-- The structure morphism `X₀ → Spec 𝔽₂`. -/
public abbrev f₀ : X₀ ⟶ Spec (.of (ZMod 2)) := projectionOf W₀

public instance instIsCurveF₀ : IsCurve (ZMod 2) f₀ := isCurve_projectionOf W₀

public instance instIsIntegralX₀ : IsIntegral X₀ := instIsCurveF₀.toIsVariety.toIsIntegral

public instance instSmoothF₀ : Smooth f₀ :=
  haveI := smoothOfRelativeDimension_projectionOf_of_isElliptic W₀
  SmoothOfRelativeDimension.smooth 1 _

public instance instIsProperF₀ : IsProper f₀ := isProper_projectionOf W₀

/-! ### The function field -/

/-- The coordinate ring `𝔽₂[x, y] / (y² + y - x³ - x - 1)` of the chart `z ≠ 0`. -/
public abbrev CR : Type := W₀.toAffine.CoordinateRing

public theorem eval₂_polynomial :
    (W₀.toAffine.polynomial).eval₂ (aeval x).toRingHom y = 0 := by
  simp only [WeierstrassCurve.Affine.polynomial, W₀, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_pow, aeval_X,
    map_zero, map_one, zero_mul, zero_add, one_mul, add_zero]
  linear_combination y_sq_add_y

/-- The map `CR → K`, `x ↦ x`, `y ↦ y`. -/
public def coordHom : CR →+* K := AdjoinRoot.lift (aeval x).toRingHom y eval₂_polynomial

public theorem coordHom_mk_C (p : (ZMod 2)[X]) :
    coordHom (AdjoinRoot.mk W₀.toAffine.polynomial (C p)) = aeval x p := by
  rw [AdjoinRoot.mk_C, coordHom, AdjoinRoot.lift_of]; rfl

public theorem coordHom_mk_Y : coordHom (AdjoinRoot.mk W₀.toAffine.polynomial X) = y := by
  rw [← AdjoinRoot.root, coordHom, AdjoinRoot.lift_root]

public theorem coordHom_smul_basis (p q : (ZMod 2)[X]) :
    coordHom (p • (1 : CR) + q • WeierstrassCurve.Affine.CoordinateRing.mk W₀.toAffine X) =
      aeval x p + aeval x q * y := by
  rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
    map_add, map_mul, map_mul, map_one, mul_one, coordHom_mk_C, coordHom_mk_C, coordHom_mk_Y]

public theorem coordHom_injective : Function.Injective coordHom := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  rw [coordHom_smul_basis] at hz
  have h := add_mul_y_eq_zero (a := algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) p)
    (b := algebraMap (ZMod 2)[X] (RatFunc (ZMod 2)) q) (by rwa [ofR_algebraMap, ofR_algebraMap])
  have inj := IsFractionRing.injective (ZMod 2)[X] (RatFunc (ZMod 2))
  rw [(map_eq_zero_iff _ inj).1 h.1, (map_eq_zero_iff _ inj).1 h.2, zero_smul, zero_smul, add_zero]

public instance : IsDomain (CommRingCat.of CR) := inferInstanceAs (IsDomain CR)

/-- The algebra structure `CR → K`. -/
public abbrev algebraCR : Algebra (CommRingCat.of CR) K := coordHom.toAlgebra

attribute [local instance] algebraCR

/-- **`K` is the fraction field of the coordinate ring of the chart `z ≠ 0`.** -/
public theorem isFractionRing_CR : IsFractionRing (CommRingCat.of CR) K := by
  have : FaithfulSMul (CommRingCat.of CR) K :=
    (faithfulSMul_iff_algebraMap_injective (CommRingCat.of CR) K).2 coordHom_injective
  refine IsFractionRing.of_field (CommRingCat.of CR) K fun z => ?_
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_y z
  obtain ⟨a1, a2, ha2, rfl⟩ := IsFractionRing.div_surjective (A := (ZMod 2)[X]) a
  obtain ⟨b1, b2, hb2, rfl⟩ := IsFractionRing.div_surjective (A := (ZMod 2)[X]) b
  have h1 := aeval_ne_zero (nonZeroDivisors.ne_zero ha2)
  have h2 := aeval_ne_zero (nonZeroDivisors.ne_zero hb2)
  refine ⟨(a1 * b2) • (1 : CR) +
      (b1 * a2) • WeierstrassCurve.Affine.CoordinateRing.mk W₀.toAffine X,
    (a2 * b2) • (1 : CR) +
      (0 : (ZMod 2)[X]) • WeierstrassCurve.Affine.CoordinateRing.mk W₀.toAffine X,
    ?_⟩
  show _ = coordHom _ / coordHom _
  simp only [coordHom_smul_basis, map_div₀, ofR_algebraMap]
  rw [map_zero, zero_mul, add_zero, map_mul, map_mul, map_mul]
  field_simp

public instance : IsDominant (chartZ W₀) :=
  ⟨IsOpen.dense (chartZ W₀).isOpenEmbedding.isOpen_range (Set.range_nonempty _)⟩

/-- **The function field of `X₀` is `K`.** -/
public def functionFieldEquiv : K ≃+* X₀.functionField :=
  ((Stacks.Chow.functionFieldEquiv_openImmersion (chartZ W₀)).trans
    (@specFunctionFieldEquiv (CommRingCat.of CR) _ K _ algebraCR isFractionRing_CR)).symm

/-- **`X₀` is geometrically irreducible over `𝔽₂`** (Stacks 054Q: `𝔽₂` is separably closed in
the function field). -/
public instance instGeometricallyIrreducibleF₀ : GeometricallyIrreducible f₀ := by
  let : Algebra (ZMod 2) (X₀.residueField (genericPoint X₀)) :=
    ((Scheme.ΓSpecIso (.of (ZMod 2))).inv ≫ f₀.appTop ≫
      X₀.Γevaluation (genericPoint X₀)).hom.toAlgebra
  exact ((geometricallyIrreducible_tfae_functionField (ZMod 2) X₀ f₀ (genericPoint X₀)
    (genericPoint_spec X₀)).out 1 3).2
      (separableClosure_eq_bot_of_ringEquiv
        ((genericResidueEquiv X₀).symm.trans functionFieldEquiv.symm))

/-! ### The counterexample -/

/-- `C(Ω) ≠ 0` for the function field of `X₀`. -/
public theorem cuspFormsCentralChar_functionField_ne_bot {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (hp : IsUnit (ringChar (ZMod 2) : Ω)) : cuspFormsCentralChar X₀.functionField Ω ≠ ⊥ := by
  obtain ⟨_, _, _, _⟩ := exists_functionField_of_isCurve f₀
  exact cuspFormsCentralChar_ne_bot_of_ringEquiv functionFieldEquiv (ZMod 2) hp
    (cuspFormsCentralChar_ne_bot hp)

/-- **Stacks Theorem 03VT is false as written for `ℓ = p`.** The curve
`X₀ : y² + y = x³ + x + 1` over `k = 𝔽₂` satisfies every hypothesis of Theorem 03VT on the curve:
it is integral, connected, a smooth proper geometrically irreducible curve over `𝔽₂`. Take
`ℓ = p = 2` and `Ω` an algebraic closure of `ℚ₂`. There is an eigenform `φ` with values in `Ω`
(an unramified cusp form with a unit value, `T_v φ = t_v φ`, `U_v φ = u_v φ`) whose central
eigenvalues `u_v` are units of `Z̄₂`, as Theorem 03VT requires, and yet no continuous
`ρ : π₁(X₀) → GL₂(E)`, `E` a finite extension of `ℚ₂` in `Ω`, has `t_v = Tr ρ(F_v)` and
`u_v = q_v⁻¹ det ρ(F_v)`. Theorem 03VT is therefore registered with the hypothesis `ℓ ≠ p`, which
its source (Drinfeld, for `ℓ ≠ p`) uses. -/
public theorem exists_eigenform_not_isFrobeniusCompatible :
    IsIntegral X₀ ∧ ConnectedSpace X₀ ∧ IsCurve (ZMod 2) f₀ ∧ Smooth f₀ ∧ IsProper f₀ ∧
      GeometricallyIrreducible f₀ ∧
      ∀ (base : GeometricPoint X₀) (Ω : Type) [Field Ω] [Algebra ℚ_[2] Ω] [IsAlgClosure ℚ_[2] Ω]
        [Algebra ℤ_[2] Ω] [IsScalarTower ℤ_[2] ℚ_[2] Ω],
        ∃ (φ : GL (Fin 2) (AdeleRing X₀.functionField) → Ω) (t u : Place X₀.functionField → Ω),
          IsEigenform φ t u ∧
          (∀ v, ∃ w : (integralClosure ℤ_[2] Ω)ˣ, ((w : integralClosure ℤ_[2] Ω) : Ω) = u v) ∧
          ∀ (E : TopologicalFieldExtension ℚ_[2]) (j : E.carrier →ₐ[ℚ_[2]] Ω)
            (ρ : EtaleFundamentalGroup X₀ base →* GL (Fin 2) E.carrier),
            Continuous (fun g => (ρ g : Matrix (Fin 2) (Fin 2) E.carrier)) →
              ¬ IsFrobeniusCompatible base ρ j.toRingHom t u := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun base Ω _ _ _ _ _ => ?_⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ_[2]
  have hp : IsUnit (ringChar (ZMod 2) : Ω) := by
    rw [ZMod.ringChar_zmod_n]
    refine IsUnit.mk0 _ ?_
    rw [← map_natCast (algebraMap ℚ_[2] Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 two_ne_zero)
  exact exists_eigenform_not_isFrobeniusCompatible_of_cuspFormsCentralChar_ne_bot f₀ base
    (ZMod.ringChar_zmod_n 2).symm (cuspFormsCentralChar_functionField_ne_bot hp)

end Stacks.Drinfeld.SupersingularCurve

end
