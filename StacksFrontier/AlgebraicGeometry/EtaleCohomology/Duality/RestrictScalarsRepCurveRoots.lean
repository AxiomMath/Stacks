module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RepresentationCurveRationalPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCoefficientLatticeChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairingBalanced
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsTraceGram

/-!
# Frobenius roots of `ℱ_{Res_b σ}` and of its dual on an open curve, `E`-linearly

Let `X` be a nonempty connected noetherian scheme, separated of finite type over a finite field
`k` (`#k = q`, characteristic `p ≠ ℓ`), with a compactification `j` such that `X̄_k̄` is a smooth
curve. Let `σ : π₁(X, x̄) → GL_m(E)`, `E / ℚ_ℓ` finite, with `Res_b σ` continuous, and suppose the
local terms at the boundary of `ℱ_{Res_b σ}` are killed by a power of `ℓ`. Let `P`, `Q` be the
`E`-linear characteristic polynomials of the Frobenius on `H¹_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` and on
`H¹_c(X_k̄, ℱ_{Res_b(σ^∨)} ⊗ ℚ_ℓ)`. Then the latter is finite dimensional, and for every
embedding `ι : E → ℂ` every root `z` of `P` along `ι` is nonzero with `q / z` a root of `Q`
(`Stacks.EtaleCohomology.LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient`).

Write `τ = Res_b σ`, `ρ₀ = P₁⁻¹ τ P₁` for its integral model and `S` for the integral part of `E`,
acting on `ℤ_ℓ^{md}` by `A(s) = P₁⁻¹ α(s) P₁`. The perfect pairing of `H¹_c(ℱ_{ρ₀})` and
`H¹_c(ℱ_{ρ₀^∨})` of `Stacks.EtaleCohomology.LAdicSheaf.exists_isPerfPair_representationCurve` is
balanced for `A(s)` and `A(s)ᵀ`, so for the `S`-sheaf `ℱ_{ρ₀^∨}` with `S` acting by `A(s)ᵀ`, and
then for `E`. That `S`-sheaf is isogenous to the dual fibre `ℱ_{Res_b(σ^∨)}`, compatibly with the
actions of `E`, through `M = P₁ᵀ G P₂`, where `G` is the trace Gram matrix of `b`
(`Stacks.EtaleCohomology.restrictScalarsTraceGram_mul_transpose`: `G Res_b(Nᵀ) = Res_b(N)ᵀ G`).
Transporting the pairing along the isogeny gives a perfect, `E`-balanced pairing scaled by `q`
under Frobenius, and `Stacks.EtaleCohomology.isRoot_div_charpoly_of_isPerfPair_balanced`
concludes. This is Poincaré duality on the fibres of the Fourier family in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The compactly supported cohomology lives in the standard model of the derived category
(`HasDerivedCategory.standard`), whence the local instance.

## Main definitions

* `Stacks.EtaleCohomology.transposeRingHom`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **The transpose of a ring homomorphism from a commutative ring into matrices**, again a ring
homomorphism: `(A(o) A(o'))ᵀ = A(o')ᵀ A(o)ᵀ` and `o o' = o' o`. -/
public def transposeRingHom {O : Type*} [CommRing O] {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (A : O →+* Matrix n n R) : O →+* Matrix n n R where
  toFun o := (A o)ᵀ
  map_one' := by rw [map_one, Matrix.transpose_one]
  map_mul' o o' := by rw [mul_comm o o', map_mul, Matrix.transpose_mul]
  map_zero' := by rw [map_zero, Matrix.transpose_zero]
  map_add' o o' := by rw [map_add, Matrix.transpose_add]

/-- `transposeRingHom A` sends `o` to the transpose `(A o)ᵀ`. -/
@[simp]
public theorem transposeRingHom_apply {O : Type*} [CommRing O] {n R : Type*} [Fintype n]
    [DecidableEq n] [CommRing R] (A : O →+* Matrix n n R) (o : O) :
    transposeRingHom A o = (A o)ᵀ :=
  rfl

/-- The transpose of an invertible matrix, as an invertible matrix. -/
public def GL.transpose {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (P : GL n R) : GL n R :=
  ⟨P.valᵀ, (P⁻¹).valᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

/-- **Conjugating a transposed conjugate.** For `M = P₁ᵀ G P₂` and `G Y = X G`:
`M⁻¹ (P₁ᵀ X P₁⁻ᵀ) M = P₂⁻¹ Y P₂`. -/
theorem conj_transpose_gram {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (P₁ G P₂ : GL n R) (X Y : Matrix n n R) (h : G.val * Y = X * G.val) :
    (GL.transpose P₁ * G * P₂)⁻¹.val * (P₁.valᵀ * X * (P₁⁻¹).valᵀ) *
        (GL.transpose P₁ * G * P₂).val = (P₂⁻¹).val * Y * P₂.val := by
  have hY : Y = (G⁻¹).val * X * G.val := by
    rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hP : (P₁⁻¹).valᵀ * P₁.valᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hT : (GL.transpose P₁)⁻¹.val = (P₁⁻¹).valᵀ := rfl
  rw [hY]
  simp only [_root_.mul_inv_rev, Units.val_mul, hT]
  show (P₂⁻¹).val * ((G⁻¹).val * (P₁⁻¹).valᵀ) * (P₁.valᵀ * X * (P₁⁻¹).valᵀ) *
      (P₁.valᵀ * G.val * P₂.val) = _
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P₁⁻¹).valᵀ P₁.valᵀ, hP, Matrix.one_mul,
    ← Matrix.mul_assoc (P₁⁻¹).valᵀ P₁.valᵀ, hP, Matrix.one_mul]

section Roots

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime] [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The restriction of scalars of the contragredient is conjugate, by the trace Gram matrix, to
the contragredient of the restriction of scalars. -/
theorem restrictScalarsTraceGram_mul_restrictScalarsRep_contragredient
    (g : EtaleFundamentalGroup X.1 x) :
    restrictScalarsTraceGram b m * (restrictScalarsRep b (contragredient σ) g).val =
      ((restrictScalarsRep b σ g⁻¹).val)ᵀ * restrictScalarsTraceGram b m := by
  show restrictScalarsTraceGram b m * restrictScalarsMatrix b ((σ g)⁻¹).valᵀ =
    (restrictScalarsMatrix b (σ g⁻¹).val)ᵀ * restrictScalarsTraceGram b m
  rw [restrictScalarsTraceGram_mul_transpose, map_inv]

/-- The trace Gram matrix carries the transpose of the action of `E` to the action of `E`. -/
theorem restrictScalarsTraceGram_mul_restrictScalarsScalarAlgHom (e : E) :
    restrictScalarsTraceGram b m * restrictScalarsScalarAlgHom b m e =
      (restrictScalarsScalarAlgHom b m e)ᵀ * restrictScalarsTraceGram b m := by
  show restrictScalarsTraceGram b m * restrictScalarsMatrix b (Matrix.scalar (Fin m) e) =
    (restrictScalarsMatrix b (Matrix.scalar (Fin m) e))ᵀ * restrictScalarsTraceGram b m
  have h : (Matrix.scalar (Fin m) e)ᵀ = Matrix.scalar (Fin m) e := by
    rw [Matrix.scalar_apply, Matrix.diagonal_transpose]
  conv_lhs => rw [← h]
  exact restrictScalarsTraceGram_mul_transpose b _

/-- **`ℱ_{ρ₀^∨}` with the transposed action of the integral part of `E`**: `ρ₀` is the integral
model of `Res_b σ`, and `s` acts by `A(s)ᵀ`, `A(s) = P₁⁻¹ α(s) P₁` the integral intertwiner of
`ρ₀`. -/
public def restrictScalarsRepDualCoefficientSheaf :
    LAdicSheaf.CoefficientSheaf B X ℓ (conjIntegralSubring
      (representationSheafConj B X x (restrictScalarsRep b σ) hσ)
      (restrictScalarsScalarAlgHom b m)) :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  representationCoefficientSheaf B X x (contragredient (integralModel _ hσ))
    (continuous_contragredient (continuous_integralModel _ hσ))
    (transposeRingHom (conjIntegralLift _ (restrictScalarsScalarAlgHom b m)))
    (fun o g => transpose_mul_contragredient
      (fun g => conjIntegralLift_mul_integralModel B X x _ hσ _
        (restrictScalarsScalarAlgHom_commute b σ) o g) g)

variable [FiniteDimensional ℚ_[ℓ] E]

/-- **The lattice change of the dual fibre** (S7): `ℱ_{ρ₀^∨}` with the transposed action and
`ℱ_{Res_b(σ^∨)}` with its own action are isogenous, compatibly with the actions of `E`, through
`M = P₁ᵀ G P₂`, `G` the trace Gram matrix of `b`. -/
theorem exists_restrictScalarsRepDualCoefficientSheaf_isogeny :
    ∃ (φ : (restrictScalarsRepDualCoefficientSheaf B X ℓ x E b σ hσ).toLAdicSheaf ⟶
        (restrictScalarsRepCoefficientSheaf B X x b (contragredient σ)
          (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf)
      (ψ : (restrictScalarsRepCoefficientSheaf B X x b (contragredient σ)
          (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf ⟶
        (restrictScalarsRepDualCoefficientSheaf B X ℓ x E b σ hσ).toLAdicSheaf) (N : ℕ),
      φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : conjIntegralSubring (representationSheafConj B X x (restrictScalarsRep b σ) hσ)
          (restrictScalarsScalarAlgHom b m))
        (o₂ : conjIntegralSubring (representationSheafConj B X x
          (restrictScalarsRep b (contragredient σ))
          (continuous_restrictScalarsRep_contragredient b hσ)) (restrictScalarsScalarAlgHom b m)),
        algebraMap _ E o₁ = algebraMap _ E o₂ →
        φ ≫ ((restrictScalarsRepCoefficientSheaf B X x b (contragredient σ)
          (continuous_restrictScalarsRep_contragredient b hσ)).act o₂).asHom =
          ((restrictScalarsRepDualCoefficientSheaf B X ℓ x E b σ hσ).act o₁).asHom ≫ φ := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have hσ' := continuous_restrictScalarsRep_contragredient b hσ
  have hP : ∀ (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin (m * d)) ℚ_[ℓ]) (hρ : Continuous ρ) g,
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ hρ g).val =
        (representationSheafConj B X x ρ hρ)⁻¹.val * (ρ g).val *
          (representationSheafConj B X x ρ hρ).val := fun ρ hρ g => by
    have h := congrArg Units.val (map_integralModel ρ hρ g)
    simp only [Units.val_mul] at h
    exact h
  have hT : ∀ (Q : GL (Fin (m * d)) ℚ_[ℓ]) (Y : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ]),
      (Q⁻¹.val * Y * Q.val)ᵀ = Q.valᵀ * Yᵀ * (Q⁻¹).valᵀ := fun Q Y => by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  let P₁ := representationSheafConj B X x (restrictScalarsRep b σ) hσ
  let P₂ := representationSheafConj B X x (restrictScalarsRep b (contragredient σ)) hσ'
  let G := (isUnit_restrictScalarsTraceGram b m).unit
  refine exists_representationCoefficientSheaf_isogeny_of_conj B X x
    (continuous_contragredient (continuous_integralModel _ hσ))
    (continuous_integralModel _ hσ') _ _ _ _ E (GL.transpose P₁ * G * P₂)
    (fun g => ?_) (fun o₁ o₂ ho => ?_)
  · rw [hP _ hσ' g, contragredient_val, ← map_inv, RingHom.mapMatrix_apply, Matrix.transpose_map,
      ← RingHom.mapMatrix_apply, hP _ hσ, hT, conj_transpose_gram]
    exact restrictScalarsTraceGram_mul_restrictScalarsRep_contragredient B X ℓ x E b σ g
  · have he : (o₁ : E) = (o₂ : E) := ho
    show (GL.transpose P₁ * G * P₂)⁻¹.val *
        (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (conjIntegralLift P₁ _ o₁)ᵀ *
        (GL.transpose P₁ * G * P₂).val = _
    rw [RingHom.mapMatrix_apply, Matrix.transpose_map, ← RingHom.mapMatrix_apply,
      mapMatrix_conjIntegralLift, mapMatrix_conjIntegralLift, hT, he, conj_transpose_gram]
    exact restrictScalarsTraceGram_mul_restrictScalarsScalarAlgHom ℓ E b (o₂ : E)

end Roots

section Balance

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ} [Fact ℓ.Prime]
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
  (F F' : LAdicSheaf.CoefficientSheaf B X ℓ O)
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i i' : ℤ)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

/-- **A pairing balanced for the actions of `O` is balanced for the actions of `E = O[1/ℓ]`.** -/
theorem LAdicSheaf.CoefficientSheaf.rationalRingHom_balanced
    (Bp : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i
      →ₗ[ℚ_[ℓ]] LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        F'.toLAdicSheaf i' →ₗ[ℚ_[ℓ]] ℚ_[ℓ])
    (h : ∀ o v w, Bp (F.rationalIntegralRingHom f j kbar i o v) w =
      Bp v (F'.rationalIntegralRingHom f j kbar i' o w)) (e : E) (v w) :
    Bp (F.rationalRingHom f j kbar i E e v) w = Bp v (F'.rationalRingHom f j kbar i' E e w) := by
  obtain ⟨a, o, ho⟩ := LAdicSheaf.CoefficientSheaf.exists_natCast_pow_mul_eq_algebraMap (ℓ := ℓ) E
    (R := O) e
  have hR : ∀ (G : LAdicSheaf.CoefficientSheaf B X ℓ O) (n : ℤ)
      (y : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        G.toLAdicSheaf n),
      G.rationalRingHom f j kbar n E (algebraMap O E o) y =
        ((ℓ ^ a : ℕ) : ℚ_[ℓ]) • G.rationalRingHom f j kbar n E e y := by
    intro G n y
    rw [← ho, map_mul, Module.End.mul_apply, map_pow, map_natCast, ← Nat.cast_pow,
      Module.End.natCast_apply, map_nsmul, Nat.cast_smul_eq_nsmul]
  have hne : ((ℓ ^ a : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have hmain := h o v w
  rw [← F.rationalRingHom_algebraMap_apply f j kbar i E, ← F'.rationalRingHom_algebraMap_apply f j
    kbar i' E, hR F i v, hR F' i' w, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_eq_mul] at hmain
  exact mul_left_cancel₀ hne hmain

end Balance

section Main

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime] [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- **Poincaré duality for `ℱ_{Res_b σ}` and `ℱ_{Res_b(σ^∨)}` on an open curve, on Frobenius
roots.** If `X̄_k̄` is a smooth curve, `X` is nonempty, `ℓ ≠ p`, the local terms of
`ℱ_{Res_b σ}` at the boundary are killed by `ℓ ^ K` and `H¹_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` is finite
dimensional, then so is `H¹_c(X_k̄, ℱ_{Res_b(σ^∨)} ⊗ ℚ_ℓ)`, and for every `ι : E →+* ℂ` every
root `z` along `ι` of the `E`-linear Frobenius characteristic polynomial of the first is nonzero,
with `q / z` a root of that of the second (`q = p ^ q'`). -/
theorem LAdicSheaf.isRoot_div_charpoly_restrictScalarsRep_contragredient
    [Algebra.IsAlgebraic k kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Nonempty X.1] (hℓp : ℓ ≠ p) {K : ℕ}
    (hF : LAdicSheaf.LocalTermsKilledBy B X ℓ f j kbar
      (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b σ) hσ) K)
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b σ) hσ) 1)] :
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI := (restrictScalarsRepCoefficientSheaf B X x b σ
      hσ).rationalCohomologyModule_isScalarTower
      f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf 1) := hV
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    ∃ hV' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b (contragredient σ))
          (continuous_restrictScalarsRep_contragredient b hσ)) 1),
      letI := (restrictScalarsRepCoefficientSheaf B X x b _
        (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule f j kbar 1 E
      haveI := (restrictScalarsRepCoefficientSheaf B X x b _
        (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule_isScalarTower
          f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
          ℓ f j kbar (restrictScalarsRepCoefficientSheaf B X x b _
            (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1) := hV'
      haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          j kbar (restrictScalarsRepCoefficientSheaf B X x b _
            (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1) :=
        Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      ∀ (ι : E →+* ℂ) (z : ℂ),
        ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius
            f j kbar 1 E p q hcard)).map ι).IsRoot z →
        z ≠ 0 ∧ ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B X x b _
          (continuous_restrictScalarsRep_contragredient b
            hσ)).rationalGeometricCompactlySupportedFrobenius
            f j kbar 1 E p q hcard)).map ι).IsRoot (((p ^ q : ℕ) : ℂ) / z) := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  obtain ⟨Bp, hperf, hfrob, hbal⟩ := LAdicSheaf.exists_isPerfPair_representationCurve B X ℓ x
    (integralModel _ hσ) (continuous_integralModel _ hσ) f j kbar p q hcard hℓp hF
    (conjIntegralLift (representationSheafConj B X x (restrictScalarsRep b σ) hσ)
      (restrictScalarsScalarAlgHom b m))
    (conjIntegralLift_mul_integralModel B X x _ hσ _ (restrictScalarsScalarAlgHom_commute b σ))
  have hbalE := LAdicSheaf.CoefficientSheaf.rationalRingHom_balanced
    (restrictScalarsRepCoefficientSheaf B X x b σ hσ)
    (restrictScalarsRepDualCoefficientSheaf B X ℓ x E b σ hσ) f j kbar 1 1 E Bp
    (fun o v w => hbal o v w)
  obtain ⟨φ, ψ, N, h₁, h₂, hφ⟩ :=
    exists_restrictScalarsRepDualCoefficientSheaf_isogeny B X ℓ x E b σ hσ
  obtain ⟨c, hcE, hcF⟩ : ∃ c : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepDualCoefficientSheaf B X ℓ x E b σ hσ).toLAdicSheaf 1 ≃ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b _
          (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1,
      (∀ e w, c ((restrictScalarsRepDualCoefficientSheaf B X ℓ x E b σ hσ).rationalRingHom
        f j kbar 1 E e w) = (restrictScalarsRepCoefficientSheaf B X x b _
          (continuous_restrictScalarsRep_contragredient b hσ)).rationalRingHom f j kbar 1 E e
            (c w)) ∧
      ∀ w, c ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
        hcard (restrictScalarsRepDualCoefficientSheaf B X ℓ x E b σ hσ).toLAdicSheaf 1).hom w) =
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (restrictScalarsRepCoefficientSheaf B X x b _
            (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1).hom (c w) :=
    ⟨(LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
      h₁ h₂ 1).toLinearEquiv,
      fun e w => LAdicSheaf.CoefficientSheaf.rationalIsogeny_rationalRingHom _ _ f j kbar 1 E φ ψ N
        h₁ h₂ hφ e w,
      fun w => LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius _ _ f j kbar 1 E φ ψ
        N h₁ h₂ hφ p q hcard w⟩
  have hcs : ∀ g₁ g₂, Function.Semiconj c g₁ g₂ → Function.Semiconj c.symm g₂ g₁ :=
    fun _ _ h w => by rw [LinearEquiv.symm_apply_eq, h, LinearEquiv.apply_symm_apply]
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf 1 →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b _
          (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1 →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      ∀ v w, B₁ v w = Bp v (c.symm w) :=
    ⟨Bp.compl₁₂ LinearMap.id c.symm.toLinearMap, fun _ _ => rfl⟩
  have := hperf
  have hB₁p : B₁.IsPerfPair := LinearMap.IsPerfPair.congr (p := Bp) (LinearEquiv.refl ℚ_[ℓ] _)
    c.symm B₁ (LinearMap.ext₂ fun v w => by
      show B₁ ((LinearEquiv.refl ℚ_[ℓ] _).symm v) (c.symm.symm w) = Bp v w
      rw [hB₁]
      exact congrArg (Bp v) (c.symm_apply_apply w))
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf 1) := hV
  have hV' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X
      ℓ f j kbar (restrictScalarsRepCoefficientSheaf B X x b _
        (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1) :=
    FiniteDimensional.of_injective B₁.flip (LinearMap.IsPerfPair.bijective_right B₁).injective
  refine ⟨hV', ?_⟩
  intro ι z hz
  let := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar 1 E
  have := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf 1) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  let := (restrictScalarsRepCoefficientSheaf B X x b _
    (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule f j kbar 1 E
  have := (restrictScalarsRepCoefficientSheaf B X x b _
    (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule_isScalarTower
      f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (restrictScalarsRepCoefficientSheaf B X x b _
        (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  have hc : ((p ^ q : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have key := isRoot_div_charpoly_of_isPerfPair_balanced B₁
    (f := (restrictScalarsRepCoefficientSheaf B X x b σ
      hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p q hcard)
    (g := (restrictScalarsRepCoefficientSheaf B X x b _
      (continuous_restrictScalarsRep_contragredient b
        hσ)).rationalGeometricCompactlySupportedFrobenius
        f j kbar 1 E p q hcard)
    (fun e v w => by
      rw [hB₁, hB₁]
      exact (hbalE e v (c.symm w)).trans (congrArg (Bp v)
        (hcs _ _ (hcE e) w).symm))
    (fun v w => by
      rw [hB₁, hB₁]
      exact (congrArg (Bp _)
        (hcs _ _ hcF w)).trans
          (hfrob v (c.symm w))) hc ι hz
  refine ⟨key.1, ?_⟩
  have h2 := key.2
  rwa [map_natCast, map_natCast] at h2

end Main

end Stacks.EtaleCohomology

end
