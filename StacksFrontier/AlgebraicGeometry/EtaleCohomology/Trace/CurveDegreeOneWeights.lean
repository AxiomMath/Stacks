module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RealizableBlockPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDeterminantalWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteFieldFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

/-!
# The weights of `H¹_c` of an `ι`-realizable pointwise mixed lisse sheaf on a curve

Kedlaya, *Fourier transforms and p-adic Weil II*, §6, the proof of Theorem main1 in degree one:
write `ρ ⊗ E` in graded upper-triangular form with absolutely irreducible blocks
(`Stacks.EtaleCohomology.exists_finiteDimensional_isGradedUpper_absolutelyIrreducible`); the
blocks are pure along every embedding of `E` (`ι`-realizability and the trace formula,
`Stacks.EtaleCohomology.exists_norm_eq_pow_toSquareBlock_of_isIotaRealizable`) of integer weights
`≤ w` (pointwise mixedness); Laumon's theorem bounds `H¹_c` of the restriction of scalars of each
pure block by `w + 1`, the filtration by the grade gives the bound for `Res_{E/ℚ_ℓ}(ρ ⊗ E)`
(`Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper`), and
`ρ` is a direct summand of `Res_{E/ℚ_ℓ}(ρ ⊗ E)`.

## Main results

* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_one_of_isIotaRealizable`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
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
  {k : Type u} [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)

/-- **Weil II 3.2.3 in degree one for `ι`-realizable pointwise mixed `ρ`** (Kedlaya, Theorem
main1), from the Frobenius trace formula (in the cohomology-free form
`Stacks.EtaleCohomology.SatisfiesFrobeniusTraceFormula`, for every continuous `ℚ_ℓ`-representation
and every `ι₁`), the finiteness of the cohomology groups in degree one, and Laumon's theorem for
the restrictions of scalars of representations which are pure of integer weights `≤ w` along every
embedding of their coefficient field: the characteristic roots of `π_U^*` on
`H¹_c(U_k̄, ℱ_ρ ⊗ ℚ_ℓ)` have weights `≤ w + 1`. -/
public theorem isCharpolyNormMixedOfWeightLE_one_of_isIotaRealizable (hℓp : ℓ ≠ p)
    (x : GeometricPoint U.1) (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹)
    (htf : ∀ (ι₁ : ℚ_[ℓ] →+* ℂ) (m : ℕ) (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) ℚ_[ℓ]),
      Continuous τ → SatisfiesFrobeniusTraceFormula ((p ^ n : ℕ) : ℝ) ι₁
        (etaleFundamentalGroupMap f x).toMonoidHom.ker φ
        (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y)
        (fun y => residueDegree f y.1) τ)
    (hFD : ∀ {N : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ),
      FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (LAdicSheaf.representationSheaf B U x τ hτ) 1))
    (hfin : ∀ {N : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ)
      (m : ℕ), Finite ((geometricCompactSupportPadicCohomology B U ℓ f j kbar 1).obj
        (LAdicSheaf.padicLevel B U ℓ (LAdicSheaf.representationSheaf B U x τ hτ) m)))
    (hLaumon : ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
      (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
      (hσ : Continuous (restrictScalarsRep b σ)) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ)
      [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
      (∀ ι' : E →+* ℂ, (∀ c, ι' (algebraMap ℚ_[ℓ] E c) = ι c) → ∃ β : ℤ, β ≤ w ∧
        ∀ (y : closedPoints U.1) (z : ℂ),
          ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
          ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
      IsCharpolyNormMixedOfWeightLE (p ^ n) ι (w + 1)
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1).hom)
    {r : ℕ} (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ) (hmix : IsPointwiseMixedOfWeightLE f x (p ^ n) ι w ρ)
    (hreal : IsIotaRealizable f x ι ρ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (LAdicSheaf.representationSheaf B U x ρ hρ) 1)] :
    IsCharpolyNormMixedOfWeightLE (p ^ n) ι (w + 1)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
        (LAdicSheaf.representationSheaf B U x ρ hρ) 1).hom := by
  classical
  obtain ⟨r', ρ', hρ', hre⟩ := hreal
  -- the geometric inputs of the purity theorem
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral U.1 := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f
  have : IsCurve k f := (isCurve_iff k f).2
    ⟨{ toIsIntegral := ‹_›
       toIsSeparated := inferInstance
       toLocallyOfFiniteType := inferInstance
       toQuasiCompact := inferInstance },
      topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f⟩
  have hD1 := forall_eq_zero_of_isCurve (K := ℂ_[ℓ]) p n hcard f x ℓ hℓp φ hφ
  have hcomm := commutator_mem_ker_etaleFundamentalGroupMap_of_finite k f x
  have hFr : ∀ y : closedPoints U.1, (φ ^ residueDegree f y.1)⁻¹ * geometricFrobeniusFamily f x y ∈
      (etaleFundamentalGroupMap f x).toMonoidHom.ker := fun y => by
    have := finite_residueField f y.1 y.2
    exact inv_pow_mul_geometricFrobeniusFamily_mem_ker p n hcard f x y φ hφ
  have hdeg : ∀ y : closedPoints U.1, 0 < residueDegree f y.1 := fun y =>
    residueDegree_pos f y.1 y.2
  have hfinpts : ∀ m : ℕ, 0 < m → {y : closedPoints U.1 | residueDegree f y.1 ∣ m}.Finite :=
    fun m hm => (finite_setOf_closedPoints_residueDegree_le f m).subset fun y hy =>
      Nat.le_of_dvd hm hy
  have : Countable (closedPoints U.1) := by
    have h : (Set.univ : Set (closedPoints U.1)) =
        ⋃ m : ℕ, {y : closedPoints U.1 | residueDegree f y.1 ≤ m} := by
      ext y
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact ⟨_, le_rfl⟩
    exact Set.countable_univ_iff.1 (h ▸ Set.countable_iUnion fun m =>
      (finite_setOf_closedPoints_residueDegree_le f m).countable)
  have hqN : 1 < p ^ n := by
    rw [← hcard]
    exact Fintype.one_lt_card
  have hq : (1 : ℝ) < ((p ^ n : ℕ) : ℝ) := by exact_mod_cast hqN
  -- a block form of `ρ ⊗ E`
  obtain ⟨E, hE, P, δ, hup, hirr⟩ := exists_finiteDimensional_isGradedUpper_absolutelyIrreducible
    (k := ℚ_[ℓ]) (K := ℂ_[ℓ]) (fun g : EtaleFundamentalGroup U.1 x => (ρ g).val)
  obtain ⟨ρE, hρEv⟩ : ∃ ρE : EtaleFundamentalGroup U.1 x →* GL (Fin r) E,
      ∀ g, (ρE g).val = (ρ g).val.map (algebraMap ℚ_[ℓ] E) :=
    ⟨(Units.map (RingHom.mapMatrix (algebraMap ℚ_[ℓ] E)).toMonoidHom).comp ρ, fun g => rfl⟩
  obtain ⟨Y, hYv⟩ : ∃ Y : EtaleFundamentalGroup U.1 x →* GL (Fin r) E,
      ∀ g, (Y g).val = P⁻¹.val * (ρ g).val.map (algebraMap ℚ_[ℓ] E) * P.val :=
    ⟨(MulAut.conj P⁻¹).toMonoidHom.comp ρE, fun g => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        Units.val_mul, hρEv]⟩
  set d := Module.finrank ℚ_[ℓ] E
  set b : Module.Basis (Fin d) ℚ_[ℓ] E := Module.finBasis ℚ_[ℓ] E
  have hd : 0 < d := Module.finrank_pos
  -- continuity of the restrictions of scalars
  have hρc : Continuous fun g => (ρ g).val := Units.continuous_val.comp hρ
  have hρEc : Continuous (restrictScalarsRep b ρE) :=
    continuous_restrictScalarsRep b ρE (by
      simp only [hρEv]
      exact continuous_restrictScalarsMatrix_map b hρc)
  have hYc : Continuous (restrictScalarsRep b Y) := continuous_restrictScalarsRep b Y (by
    have h : (fun g => restrictScalarsMatrix b (Y g).val) = fun g =>
        restrictScalarsMatrix b P⁻¹.val * restrictScalarsMatrix b ((ρ g).val.map
          (algebraMap ℚ_[ℓ] E)) * restrictScalarsMatrix b P.val := funext fun g => by
      rw [hYv, restrictScalarsMatrix_mul, restrictScalarsMatrix_mul]
    rw [h]
    exact (continuous_const.matrix_mul (continuous_restrictScalarsMatrix_map b hρc)).matrix_mul
      continuous_const)
  -- purity of the blocks along every embedding, with integer weights `≤ w`
  set Pc : (closedPoints U.1 → Polynomial E) → Prop := fun C =>
    ∀ ι' : E →+* ℂ, (∀ c, ι' (algebraMap ℚ_[ℓ] E c) = ι c) → ∃ β : ℤ, β ≤ w ∧
      ∀ (y : closedPoints U.1) (z : ℂ), ((C y).map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)
  have hPc1 : Pc fun _ => 1 := fun ι' _ => ⟨w, le_rfl, fun y z hz => by simp at hz⟩
  have hYup : ∀ g, IsGradedUpper δ (Y g).val := fun g => by
    rw [hYv]
    exact hup g
  have hblk : ∀ t,
      Pc fun y => ((Y (geometricFrobeniusFamily f x y)).val.toSquareBlock δ t).charpoly := by
    intro t ι' hι'
    obtain ⟨β, hβ, hpure⟩ := exists_norm_eq_pow_toSquareBlock_of_isIotaRealizable ι
      (etaleFundamentalGroupMap f x).toMonoidHom.ker φ hcomm hD1
      (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y)
      (fun y => residueDegree f y.1) hFr hdeg hfinpts hq htf ρ hρ ρ' hρ' hre E P δ hup hirr ι'
      hι' t
    refine exists_int_weight_of_norm_eq_pow ι ι' hι'
      (fun y : closedPoints U.1 => residueDegree f y.1)
      hdeg hqN _ (fun y => (ρ (geometricFrobeniusFamily f x y)).val.charpoly) (fun y => ?_) hmix
      hβ (fun y z hz => hpure y z (by rwa [← hYv]))
    have hbt : (Y (geometricFrobeniusFamily f x y)).val.BlockTriangular δ :=
      fun i i' h => hYup _ i i' h
    have hc : (Y (geometricFrobeniusFamily f x y)).val.charpoly =
        ((ρ (geometricFrobeniusFamily f x y)).val.charpoly).map (algebraMap ℚ_[ℓ] E) := by
      rw [hYv, ← Matrix.charpoly_map, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj' P _
    rw [← hc, hbt.charpoly]
    by_cases ht : t ∈ Finset.univ.image δ
    · exact Finset.dvd_prod_of_mem _ ht
    · have : IsEmpty {i // δ i = t} := ⟨fun ⟨i, hi⟩ => ht (Finset.mem_image.2 ⟨i, by simp, hi⟩)⟩
      rw [charpoly_isEmpty]
      exact one_dvd _
  -- the filtration by the grade, with Laumon's theorem on the pure pieces
  obtain ⟨hYd, hYw⟩ := isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper B U x f j
    kbar p n hcard b 1 (fun y : closedPoints U.1 => geometricFrobeniusFamily f x y) Pc hPc1
    (fun τ hτ => hFD τ hτ) (fun τ hτ m => hfin τ hτ m)
    (fun Y' hY' _ hP => hLaumon E b Y' hY' ι w hP) r Y δ hYup hYc hblk
  -- `Res (ρ ⊗ E)` is conjugate to `Res Y`
  have := hFD (restrictScalarsRep b ρE) hρEc
  have hstep2 := isCharpolyNormMixedOfWeightLE_representationSheaf_of_intertwiner B U x f j kbar
    p n hcard hρEc hYc (restrictScalarsMatrix b P⁻¹.val)
    (fun g => by
      rw [restrictScalarsRep_val, restrictScalarsRep_val, ← restrictScalarsMatrix_mul,
        ← restrictScalarsMatrix_mul, hYv, hρEv]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [Units.mul_inv, Matrix.mul_one])
    (restrictScalarsMatrix b P.val)
    (fun g => by
      rw [restrictScalarsRep_val, restrictScalarsRep_val, ← restrictScalarsMatrix_mul,
        ← restrictScalarsMatrix_mul, hYv, hρEv]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (by rw [← restrictScalarsMatrix_mul, Units.mul_inv, restrictScalarsMatrix_one]) 1 hYw
  -- `ρ` is a direct summand of `Res (ρ ⊗ E)`
  exact isCharpolyNormMixedOfWeightLE_representationSheaf_of_intertwiner B U x f j kbar p n hcard
    hρ hρEc (summandInclusion ⟨0, hd⟩)
    (fun g => by
      rw [restrictScalarsRep_val, hρEv]
      exact (restrictScalarsMatrix_map_mul_summandInclusion b ⟨0, hd⟩ _).symm)
    (summandProjection ⟨0, hd⟩)
    (fun g => by
      rw [restrictScalarsRep_val, hρEv]
      exact summandProjection_mul_restrictScalarsMatrix_map b ⟨0, hd⟩ _)
    (summandProjection_mul_summandInclusion ⟨0, hd⟩) 1 hstep2

end Stacks.EtaleCohomology

end
