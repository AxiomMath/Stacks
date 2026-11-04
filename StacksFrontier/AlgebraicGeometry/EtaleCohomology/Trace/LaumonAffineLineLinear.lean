module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundAffineLineInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsCharpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCommutantCohomology

/-!
# Laumon's theorem on the affine line, `E`-linearly

For a finite extension `E` of `ℚ_ℓ` with a basis `b` and `σ : π₁(U, x̄) → GL_m(E)`, the scalar
matrices of `E` commute with `σ`, so their restrictions of scalars commute with `Res_b σ` and `E`
acts on `H¹_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`, with `π_U^*` `E`-linear
(`LAdicSheaf.CoefficientSheaf.rationalGeometricCompactlySupportedFrobenius`). The characteristic
roots of `π_U^*` over `ℚ_ℓ` along `ι` are those of `π_U^*` over `E` along the embeddings `ι'` of
`E` over `ι` (`isCharpolyNormMixedOfWeightLE_restrictScalars_iff`). Hence `LaumonAffineLineInput`
(Laumon's theorem on `𝔸¹`), where the hypothesis is purity of `σ` along every `ι'` with possibly
different weights, follows from its `E`-linear form `LaumonAffineLineLinearInput`, which concerns
one embedding `ι'` of `E` at a time: if `σ` is `ι'`-pure of weight `β`, the roots of the
`E`-characteristic polynomial of `π_U^*` on `H¹_c` have weights `≤ β + 1` along `ι'` (Weil II 3.2.3
for `σ`).

## Main definitions

* `Stacks.EtaleCohomology.restrictScalarsScalarAlgHom`: `e ↦ Res_b (e · 1_m)`.
* `Stacks.EtaleCohomology.restrictScalarsRepCoefficientSheaf`: `ℱ_{Res_b σ}` with the action of the
  integral part of `E`.
* `Stacks.EtaleCohomology.LaumonAffineLineInput`: Laumon's theorem on `𝔸¹` for `Res_b σ`.
* `Stacks.EtaleCohomology.LaumonAffineLineLinearInput`: its `E`-linear form, one embedding `ι'` at
  a time.
* `Stacks.EtaleCohomology.CurveLinearTraceFormulaInput`: the `E`-linear trace formula on curves.

## Main results

* `Stacks.EtaleCohomology.laumonAffineLineInput_of_linear`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

section Matrix

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- Restriction of scalars of matrices is additive: `Res_b (M + N) = Res_b M + Res_b N`. -/
public theorem restrictScalarsMatrix_add {m n : ℕ} (M N : Matrix (Fin m) (Fin n) E) :
    restrictScalarsMatrix b (M + N) = restrictScalarsMatrix b M + restrictScalarsMatrix b N := by
  ext p q
  simp [restrictScalarsMatrix]

/-- Restriction of scalars sends the zero matrix to the zero matrix. -/
public theorem restrictScalarsMatrix_zero {m n : ℕ} :
    restrictScalarsMatrix b (0 : Matrix (Fin m) (Fin n) E) = 0 := by
  ext p q
  simp [restrictScalarsMatrix]

/-- **`e ↦ Res_b (e · 1_m)`**, the action of `E` on `F^{m d}` by restriction of scalars of the
scalar matrices. -/
public def restrictScalarsScalarAlgHom (m : ℕ) :
    E →ₐ[F] Matrix (Fin (m * d)) (Fin (m * d)) F where
  toFun e := restrictScalarsMatrix b (Matrix.scalar (Fin m) e)
  map_one' := by rw [map_one, restrictScalarsMatrix_one]
  map_mul' e e' := by rw [map_mul, restrictScalarsMatrix_mul]
  map_zero' := by rw [map_zero, restrictScalarsMatrix_zero]
  map_add' e e' := by rw [map_add, restrictScalarsMatrix_add]
  commutes' c := by
    have : Matrix.scalar (Fin m) (algebraMap F E c) =
        (Matrix.scalar (Fin m) c).map (algebraMap F E) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
    rw [this]
    ext p q
    obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
    rw [restrictScalarsMatrix_map_algebraMap, Algebra.algebraMap_eq_smul_one c, Matrix.smul_apply,
      smul_eq_mul, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.one_apply]
    simp only [finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    by_cases hij : i = j <;> by_cases hll : l = l' <;> simp [hij, hll]

/-- The scalar matrices commute with a representation over `E`, so their restrictions of scalars
commute with `Res_b σ`. -/
public theorem restrictScalarsScalarAlgHom_commute {G : Type*} [Monoid G] {m : ℕ}
    (σ : G →* GL (Fin m) E) (e : E) (g : G) :
    restrictScalarsScalarAlgHom b m e * (restrictScalarsRep b σ g).val =
      (restrictScalarsRep b σ g).val * restrictScalarsScalarAlgHom b m e := by
  show restrictScalarsMatrix b _ * restrictScalarsMatrix b _ =
    restrictScalarsMatrix b _ * restrictScalarsMatrix b _
  rw [← restrictScalarsMatrix_mul, ← restrictScalarsMatrix_mul,
    (Matrix.scalar_commute e (fun _ => mul_comm _ _) (σ g).val)]

end Matrix

section Sheaf

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
  {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))

/-- **`ℱ_{Res_b σ}` with the action of the integral part of `E`**, through the restrictions of
scalars of the scalar matrices. -/
public abbrev restrictScalarsRepCoefficientSheaf :=
  representationSheafCommutantCoefficientSheaf B X x (restrictScalarsRep b σ) hσ
    (restrictScalarsScalarAlgHom b m) (restrictScalarsScalarAlgHom_commute b σ)

end Sheaf

/-- **Laumon's theorem on opens of the affine line, `E`-linearly** (Weil II 3.2.3 for pure lisse
sheaves on opens of `𝔸¹`, by the `ℓ`-adic Fourier transform): for `σ : π₁(U, x̄) → GL_m(E)`, `E`
finite over `ℚ_ℓ`, and an embedding `ι' : E → ℂ` along which `σ` is pure of an integer weight
`β`, the characteristic roots along `ι'` of the `E`-linear `π_U^*` on
`H¹_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` have weights `≤ β + 1`. -/
public def LaumonAffineLineLinearInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (ι' : E →+* ℂ) (β : ℤ)
    [hV : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI :=
      (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
        f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) := hV
    haveI : FiniteDimensional E
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    IsCharpolyNormMixedOfWeightLE (p ^ n) ι' (β + 1)
      ((restrictScalarsRepCoefficientSheaf
          B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
        f j kbar 1 E p n hcard)

/-- **The `E`-linear trace formula for `ℱ_{Res_b σ}` on a smooth curve** (Tag 03V2 with
coefficients in `E`): for `σ : π₁(U, x̄) → GL_m(E)`,
`∑_{deg y ∣ N} deg y · tr_E σ(F_y)^{N / deg y}` is the alternating sum of the `E`-traces of
`(π_U^*)^N` on the `E`-vector spaces `Hⁱ_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`. The `ℚ_ℓ`-trace formula
(`Stacks.EtaleCohomology.CurveTraceFormulaInput`) is its image under `Tr_{E/ℚ_ℓ}`. -/
public def CurveLinearTraceFormulaInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (N : ℕ),
    0 < N →
    ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : E) *
        (((σ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace =
      ∑ i ∈ Finset.range 3, (-1 : E) ^ i *
        (letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar
          (i : ℤ) E
        LinearMap.trace E _
          (((restrictScalarsRepCoefficientSheaf
              B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
            f j kbar (i : ℤ) E p n hcard) ^ N))

/-- **Laumon's theorem on the affine line** (Weil II 3.2.3 for pure lisse sheaves on `𝔸¹`, by the
`ℓ`-adic Fourier transform), for the restriction of scalars `Res_b σ` of a representation
`σ : π₁(𝔸¹_k, x̄) → GL_m(E)` with `E` finite over `ℚ_ℓ`: if along every embedding `ι' : E → ℂ` over
`ι` the representation `σ` is pure of some integer weight `≤ w`, then the characteristic roots of
`π^*` on `H¹_c(𝔸¹_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` have weights `≤ w + 1`.  This is
`Stacks.EtaleCohomology.LaumonOpenAffineLineInput` for the open `U = 𝔸¹` (`e` an isomorphism). -/
public def LaumonAffineLineInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ ι' : E →+* ℂ, (∀ c, ι' (algebraMap ℚ_[ℓ] E c) = ι c) → ∃ β : ℤ, β ≤ w ∧
      ∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    IsCharpolyNormMixedOfWeightLE (p ^ n) ι (w + 1)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1).hom

/-- **`Stacks.EtaleCohomology.LaumonAffineLineInput` from its `E`-linear form**: the roots along
`ι` of `π^*` on `H¹_c(𝔸¹_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` are the roots along the embeddings `ι'` of `E`
over `ι` of the `E`-linear `π^*`, which have weights `≤ β(ι') + 1 ≤ w + 1`. -/
public theorem laumonAffineLineInput_of_linear (h : LaumonAffineLineLinearInput.{u}) :
    LaumonAffineLineInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ ι w hV hP
  let := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
  have := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
      j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) := hV
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  show IsCharpolyNormMixedOfWeightLE (p ^ n) ι (w + 1)
    (((restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
      f j kbar 1 E p n hcard).restrictScalars ℚ_[ℓ])
  refine (isCharpolyNormMixedOfWeightLE_restrictScalars_iff _ _ ι _).2 fun ι' hι' => ?_
  obtain ⟨β, hβ, hpure⟩ := hP ι' hι'
  intro z hz
  obtain ⟨w', hw', hz'⟩ := h B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ ι' β hpure z hz
  exact ⟨w', hw'.trans (by omega), hz'⟩

end Stacks.EtaleCohomology

end
