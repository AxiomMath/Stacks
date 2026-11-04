module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsFiltrationBlockWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDegreeOneWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsTower

/-!
# Laumon's theorem on the affine line: reduction to absolutely irreducible representations

Laumon's theorem on the affine line (Weil II 3.2.3 on `𝔸¹`;
`Stacks.EtaleCohomology.LaumonAffineLineInput`) for a representation `σ : π₁(𝔸¹_k, x̄) → GL_m(E)`
follows from its case `Stacks.EtaleCohomology.LaumonAffineLineAbsIrrInput` of the representations
that are absolutely irreducible and whose coefficients `E` contain a primitive `p`-th root of
unity.

## References

* Kedlaya, *Fourier transforms and p-adic Weil II*, §6

## Main definitions

* `Stacks.EtaleCohomology.LaumonAffineLineAbsIrrInput`.

## Main results

* `Stacks.EtaleCohomology.laumonAffineLineInput_of_absIrr`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology


/-- **Laumon's theorem on the affine line for absolutely irreducible representations with
`ζ_p` in the coefficients**: `Stacks.EtaleCohomology.LaumonAffineLineInput` for those
`σ : π₁(𝔸¹_k, x̄) → GL_m(E)` which are irreducible over an algebraically closed field `K ⊇ E` and
whose field of coefficients `E` contains a primitive `p`-th root of unity. -/
public def LaumonAffineLineAbsIrrInput : Prop :=
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
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ)
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


/-- **Laumon's theorem on the affine line from the absolutely irreducible case with `ζ_p` in
the coefficients.** `Stacks.EtaleCohomology.LaumonAffineLineAbsIrrInput` implies
`Stacks.EtaleCohomology.LaumonAffineLineInput`. -/
public theorem laumonAffineLineInput_of_absIrr (h : LaumonAffineLineAbsIrrInput.{u}) :
    LaumonAffineLineInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ ι w _ hP
  classical
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  have hdim : topologicalKrullDim U.1 ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le
  have hFD : ∀ {N : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ),
      FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (LAdicSheaf.representationSheaf B U x τ hτ) 1) := fun τ hτ =>
    LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one
      B U ℓ f j kbar p n hcard hdim _ 1
  let K := AlgebraicClosure E
  obtain ⟨E₁, hE₁, P, δ, hup, hirr⟩ := exists_finiteDimensional_isGradedUpper_absolutelyIrreducible
    (k := E) (K := K) (fun g : EtaleFundamentalGroup U.1 x => (σ g).val)
  have := hE₁
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] K).injective
  have : NeZero ((p : ℕ) : K) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  let E₂ : IntermediateField E K := E₁ ⊔ IntermediateField.adjoin E {ζ}
  have hζint : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  have : FiniteDimensional E (IntermediateField.adjoin E {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hζint
  have : FiniteDimensional E E₂ := IntermediateField.finiteDimensional_sup E₁ _
  have : FiniteDimensional ℚ_[ℓ] E₂ := Module.Finite.trans E E₂
  have hle : E₁ ≤ E₂ := le_sup_left
  have hζ₂ : ζ ∈ E₂ := (le_sup_right : IntermediateField.adjoin E {ζ} ≤ E₂)
    (IntermediateField.mem_adjoin_simple_self E ζ)
  let ι₁₂ : E₁ →+* E₂ := (IntermediateField.inclusion hle).toRingHom
  let P₂ : (Matrix (Fin m) (Fin m) E₂)ˣ := Units.map (RingHom.mapMatrix ι₁₂).toMonoidHom P
  obtain ⟨σ₂, hσ₂v⟩ : ∃ σ₂ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E₂,
      ∀ g, (σ₂ g).val = (σ g).val.map (algebraMap E E₂) :=
    ⟨(Units.map (RingHom.mapMatrix (algebraMap E E₂)).toMonoidHom).comp σ, fun g => rfl⟩
  obtain ⟨Y, hYv⟩ : ∃ Y : EtaleFundamentalGroup U.1 x →* GL (Fin m) E₂,
      ∀ g, (Y g).val = P₂⁻¹.val * (σ g).val.map (algebraMap E E₂) * P₂.val :=
    ⟨(MulAut.conj P₂⁻¹).toMonoidHom.comp σ₂, fun g => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        Units.val_mul, hσ₂v]⟩
  have hYE₁ : ∀ g, (Y g).val = ((P⁻¹ : (Matrix (Fin m) (Fin m) E₁)ˣ).val *
      (σ g).val.map (algebraMap E E₁) * P.val).map ι₁₂ := fun g => by
    rw [hYv, Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
    rfl
  have hYK : ∀ g, (Y g).val.map (algebraMap E₂ K) = ((P⁻¹ : (Matrix (Fin m) (Fin m) E₁)ˣ).val *
      (σ g).val.map (algebraMap E E₁) * P.val).map (algebraMap E₁ K) := fun g => by
    rw [hYE₁, Matrix.map_map]
    rfl
  have hYup : ∀ g, IsGradedUpper δ (Y g).val := fun g i i' hii' => by
    rw [hYE₁, Matrix.map_apply, hup g i i' hii', map_zero]
  let c := Module.finBasis E E₂
  have hd' : 0 < Module.finrank E E₂ := Module.finrank_pos
  let b₂ := towerBasis b c
  have hσc : Continuous fun g => restrictScalarsMatrix b (σ g).val :=
    Units.continuous_val.comp hσ
  have hσ₂c : Continuous (restrictScalarsRep b₂ σ₂) := continuous_restrictScalarsRep b₂ σ₂ (by
    rw [show (fun g => restrictScalarsMatrix b₂ (σ₂ g).val) = fun g =>
        (kronecker (restrictScalarsMatrix b (σ g).val)
          (1 : Matrix (Fin (Module.finrank E E₂)) (Fin (Module.finrank E E₂)) ℚ_[ℓ])).submatrix
            (towerReindex m d _) (towerReindex m d _) from funext fun g => by
      rw [hσ₂v]; exact restrictScalarsMatrix_towerBasis_map b c _]
    refine Continuous.matrix_submatrix ?_ _ _
    exact continuous_pi fun p₁ => continuous_pi fun q₁ =>
      (hσc.matrix_elem p₁.1 q₁.1).mul continuous_const)
  have hYc : Continuous (restrictScalarsRep b₂ Y) := continuous_restrictScalarsRep b₂ Y (by
    have h' : (fun g => restrictScalarsMatrix b₂ (Y g).val) = fun g =>
        restrictScalarsMatrix b₂ P₂⁻¹.val * restrictScalarsMatrix b₂ (σ₂ g).val *
          restrictScalarsMatrix b₂ P₂.val := funext fun g => by
      rw [hYv, restrictScalarsMatrix_mul, restrictScalarsMatrix_mul, hσ₂v]
    rw [h']
    exact (continuous_const.matrix_mul (Units.continuous_val.comp hσ₂c)).matrix_mul
      continuous_const)
  set Pb : (a : ℕ) → (EtaleFundamentalGroup U.1 x → Matrix (Fin a) (Fin a) E₂) → Prop :=
    fun a Z => (∀ W : Submodule K (Fin a → K),
      (∀ g, ∀ v ∈ W, (Z g).map (algebraMap E₂ K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∀ g, (Z g).charpoly ∣ (Y g).val.charpoly with hPb_def
  have hPb : ∀ Z : EtaleFundamentalGroup U.1 x → Matrix (Fin 0) (Fin 0) E₂, Pb 0 Z := fun Z =>
    ⟨fun W _ => Or.inl (Subsingleton.elim _ _), fun g => by rw [charpoly_isEmpty]; exact one_dvd _⟩
  have hbase : ∀ {a : ℕ} (Y' : EtaleFundamentalGroup U.1 x →* GL (Fin a) E₂)
      (hY' : Continuous (restrictScalarsRep b₂ Y'))
      [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b₂ Y') hY') 1)],
      Pb a (fun g => (Y' g).val) →
      IsCharpolyNormMixedOfWeightLE (p ^ n) ι (w + 1)
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b₂ Y') hY') 1).hom := by
    intro a Y' hY' _ hY'P
    refine h B U ℓ k f e he j kbar p n hcard hℓp x E₂ b₂ Y' hY' K hY'P.1
      ⟨⟨ζ, hζ₂⟩, (IsPrimitiveRoot.map_iff_of_injective (algebraMap E₂ K).injective).1 hζ⟩ ι w ?_
    intro ι'' hι''
    have hι' : ∀ c', (ι''.comp (algebraMap E E₂)) (algebraMap ℚ_[ℓ] E c') = ι c' := fun c' => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
      exact hι'' c'
    obtain ⟨β, hβ, hpure⟩ := hP _ hι'
    refine ⟨β, hβ, fun y z hz => hpure y z ?_⟩
    have h1 := hY'P.2 (geometricFrobeniusFamily f x y)
    have h2 : (Y (geometricFrobeniusFamily f x y)).val.charpoly =
        (σ (geometricFrobeniusFamily f x y)).val.charpoly.map (algebraMap E E₂) := by
      rw [hYv, ← Matrix.charpoly_map, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj' P₂ _
    rw [h2] at h1
    obtain ⟨r, hr⟩ := Polynomial.map_dvd ι'' h1
    rw [Polynomial.map_map] at hr
    show Polynomial.eval z _ = 0
    rw [hr, Polynomial.eval_mul, hz.eq_zero, zero_mul]
  have hblk : ∀ (t : ℤ) (a : ℕ) (e₀ : Fin a → Fin m), Function.Injective e₀ →
      (∀ i, δ i = t ↔ ∃ j', e₀ j' = i) → Pb a fun g => (Y g).val.submatrix e₀ e₀ := by
    intro t a e₀ he₀ hre
    refine ⟨fun W hW => ?_, fun g => ?_⟩
    · set X : EtaleFundamentalGroup U.1 x → Matrix (Fin m) (Fin m) K := fun g =>
        ((P⁻¹ : (Matrix (Fin m) (Fin m) E₁)ˣ).val * (σ g).val.map (algebraMap E E₁) *
          P.val).map (algebraMap E₁ K) with hX_def
      have hXd : ∀ g i i', δ i ≠ δ i' → gradedDiag δ (X g) i i' = 0 := fun g i i' hii' => by
        simp [gradedDiag, hii']
      have hirr' : ∀ W' : Submodule K (Fin m → K), W' ≤ coordSubspace (K := K) (fun i => δ i = t) →
          W' ≠ ⊥ → (∀ g, ∀ v ∈ W', gradedDiag δ (X g) *ᵥ v ∈ W') →
          W' = coordSubspace (K := K) (fun i => δ i = t) := fun W' hle' hne hst =>
        hirr t W' hle' hne fun g v hv => by
          rw [gradedDiag_map]
          exact hst g v hv
      have hblk' := forall_block_eq_bot_or_eq_top hXd hirr'
      let eq : Fin a ≃ {i // δ i = t} := Equiv.ofBijective (fun j' => ⟨e₀ j', (hre _).2 ⟨j', rfl⟩⟩)
        ⟨fun j₁ j₂ h12 => he₀ (congrArg Subtype.val h12), fun i =>
          let ⟨j', hj'⟩ := (hre i.1).1 i.2; ⟨j', Subtype.ext hj'⟩⟩
      have hsub : ∀ g, ((Y g).val.submatrix e₀ e₀).map (algebraMap E₂ K) =
          ((gradedDiag δ (X g)).toSquareBlock δ t).submatrix eq eq := fun g => by
        ext j₁ j₂
        rw [Matrix.map_apply, submatrix_apply]
        show _ = gradedDiag δ (X g) (e₀ j₁) (e₀ j₂)
        rw [gradedDiag, if_pos (((hre _).2 ⟨j₁, rfl⟩).trans ((hre _).2 ⟨j₂, rfl⟩).symm)]
        exact congrFun (congrFun (hYK g) (e₀ j₁)) (e₀ j₂)
      set W' : Submodule K ({i // δ i = t} → K) := W.comap (LinearMap.funLeft K K eq) with hW'
      have hW'st : ∀ g, ∀ v ∈ W', (gradedDiag δ (X g)).toSquareBlock δ t *ᵥ v ∈ W' := by
        intro g v hv
        show (fun j' => ((gradedDiag δ (X g)).toSquareBlock δ t *ᵥ v) (eq j')) ∈ W
        rw [show (fun j' => ((gradedDiag δ (X g)).toSquareBlock δ t *ᵥ v) (eq j')) =
            ((gradedDiag δ (X g)).toSquareBlock δ t).submatrix eq eq *ᵥ (v ∘ eq) by
          rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
          rfl, ← hsub g]
        exact hW g _ hv
      have hf := LinearMap.funLeft_surjective_of_injective K K eq eq.injective
      rw [← Submodule.map_comap_eq_of_surjective hf W]
      rcases hblk' W' hW'st with h | h
      · left
        rw [← hW', h, Submodule.map_bot]
      · right
        rw [← hW', h, Submodule.map_top, LinearMap.range_eq_top.2 hf]
    · have hbt : (Y g).val.BlockTriangular δ := fun i i' hii' => hYup g i i' hii'
      rw [charpoly_submatrix_eq_charpoly_toSquareBlock _ δ t he₀ hre, hbt.charpoly]
      by_cases ht : t ∈ Finset.univ.image δ
      · exact Finset.dvd_prod_of_mem _ ht
      · have : IsEmpty {i // δ i = t} :=
          ⟨fun ⟨i, hi⟩ => ht (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩
        rw [charpoly_isEmpty]
        exact one_dvd _
  obtain ⟨_, hYw⟩ := isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper_blocks B U x
    f j kbar p n hcard b₂ 1 (q := p ^ n) (ι := ι) (w := w + 1) Pb hPb (fun τ hτ => hFD τ hτ)
    (fun τ hτ N' => curveFiniteLevelInput B U ℓ k f j kbar p n hcard hℓp x τ hτ 1 N') hbase m Y δ
    hYup hYc hblk
  have := hFD (restrictScalarsRep b₂ σ₂) hσ₂c
  have hPP : P₂.val * P₂⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstep2 := isCharpolyNormMixedOfWeightLE_representationSheaf_of_intertwiner B U x f j kbar
    p n hcard hσ₂c hYc (restrictScalarsMatrix b₂ P₂⁻¹.val)
    (fun g => by
      rw [restrictScalarsRep_val, restrictScalarsRep_val, ← restrictScalarsMatrix_mul,
        ← restrictScalarsMatrix_mul, hYv, hσ₂v]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [hPP, Matrix.mul_one])
    (restrictScalarsMatrix b₂ P₂.val)
    (fun g => by
      rw [restrictScalarsRep_val, restrictScalarsRep_val, ← restrictScalarsMatrix_mul,
        ← restrictScalarsMatrix_mul, hYv, hσ₂v]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul])
    (by rw [← restrictScalarsMatrix_mul, hPP, restrictScalarsMatrix_one]) 1 hYw
  exact isCharpolyNormMixedOfWeightLE_representationSheaf_of_intertwiner B U x f j kbar p n hcard
    hσ hσ₂c (towerSummandInclusion ⟨0, hd'⟩)
    (fun g => by
      rw [restrictScalarsRep_val, restrictScalarsRep_val, hσ₂v]
      exact towerSummandInclusion_mul b c ⟨0, hd'⟩ _)
    (towerSummandProjection ⟨0, hd'⟩)
    (fun g => by
      rw [restrictScalarsRep_val, restrictScalarsRep_val, hσ₂v]
      exact towerSummandProjection_mul b c ⟨0, hd'⟩ _)
    (towerSummandProjection_mul_towerSummandInclusion ⟨0, hd'⟩) 1 hstep2

end Stacks.EtaleCohomology

end
