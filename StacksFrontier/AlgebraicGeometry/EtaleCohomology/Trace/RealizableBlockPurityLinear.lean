module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RealizableBlockPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealPurityLinear

/-!
# Purity of the constituents of an `ι`-realizable representation with coefficients in a field `F`

`Stacks.EtaleCohomology.exists_norm_eq_pow_toSquareBlock_of_isIotaRealizable` (Weil II 1.5.1;
Kedlaya, *Fourier transforms and p-adic Weil II*, Theorem 6.5.2) for representations
`ρ, ρ' : Γ → GL(F)` with coefficients in a topological field `F` with a continuous map to `ℂ_ℓ`
(for instance a finite extension `E` of `ℚ_ℓ` embedded in `ℂ_ℓ`), in place of `ℚ_ℓ`: if `ρ ⊕ ρ'`
has `ι`-real Frobenius characteristic polynomials (`ι : F → ℂ`), the diagonal blocks of a graded
upper-triangular form of `ρ` over a subfield `E ⊆ ℂ_ℓ` containing `F` are pure along every
embedding of `E` over `ι`. The group-level input is
`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isGradedUpper_linear`.

## Main results

* `Stacks.EtaleCohomology.exists_norm_eq_pow_toSquareBlock_of_isIotaRealizable_linear`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Purity

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [Algebra F ℂ_[ℓ]]

/-- **The diagonal blocks of an `ι`-realizable representation with coefficients in `F` are pure
along every embedding of the block field** (Weil II 1.5.1; Kedlaya, Theorem 6.5.2), for a
topological field `F` with a continuous map to `ℂ_ℓ` in place of `ℚ_ℓ`
(`Stacks.EtaleCohomology.exists_norm_eq_pow_toSquareBlock_of_isIotaRealizable`). Let `ρ` be
such that `ρ ⊕ ρ'` has `ι`-real Frobenius characteristic polynomials, and `P⁻¹ (ρ ⊗ E) P`
graded upper triangular with `ℂ_ℓ`-irreducible diagonal blocks, `E ⊆ ℂ_ℓ`. Then for every
`ι' : E →+* ℂ` over `ι` and every grade `t` there is `β > 0` with all roots along `ι'` of the
characteristic polynomial of the block `t` of `P⁻¹ ρ(F_y) P` of absolute value `β ^ deg y`. -/
public theorem exists_norm_eq_pow_toSquareBlock_of_isIotaRealizable_linear (ι : F →+* ℂ)
    (H : Subgroup Γ) [H.Normal] (φ : Γ) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → ℂ_[ℓ], (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    {Y : Type*} [Countable Y] (Fr : Y → Γ) (deg : Y → ℕ) (hFr : ∀ y, (φ ^ deg y)⁻¹ * Fr y ∈ H)
    (hdeg : ∀ y, 0 < deg y) (hfin : ∀ m : ℕ, 0 < m → {y : Y | deg y ∣ m}.Finite) {q : ℝ}
    (hq : 1 < q)
    (htf : ∀ (ι₁ : F →+* ℂ) (m : ℕ) (τ : Γ →* GL (Fin m) F), Continuous τ →
      SatisfiesFrobeniusTraceFormula q ι₁ H φ Fr deg τ)
    {r r' : ℕ} (ρ : Γ →* GL (Fin r) F) (hρ : Continuous ρ) (ρ' : Γ →* GL (Fin r') F)
    (hρ' : Continuous ρ') (hFK : Continuous (algebraMap F ℂ_[ℓ]))
    (hreal : ∀ (y : Y) (m : ℕ), ι (((ρ (Fr y)).val.charpoly * (ρ' (Fr y)).val.charpoly).coeff m) ∈
      Set.range ((↑) : ℝ → ℂ))
    (E : IntermediateField ℚ_[ℓ] ℂ_[ℓ]) [Algebra F E] [IsScalarTower F E ℂ_[ℓ]]
    (P : (Matrix (Fin r) (Fin r) E)ˣ) (δ : Fin r → ℤ)
    (hup : ∀ g, IsGradedUpper δ (P⁻¹.val * (ρ g).val.map (algebraMap F E) * P.val))
    (hirr : ∀ (t : ℤ) (W' : Submodule ℂ_[ℓ] (Fin r → ℂ_[ℓ])),
      W' ≤ coordSubspace (K := ℂ_[ℓ]) (fun i => δ i = t) → W' ≠ ⊥ →
      (∀ g, ∀ v ∈ W', (gradedDiag δ (P⁻¹.val * (ρ g).val.map (algebraMap F E) *
        P.val)).map (algebraMap E ℂ_[ℓ]) *ᵥ v ∈ W') →
      W' = coordSubspace (K := ℂ_[ℓ]) (fun i => δ i = t))
    (ι' : E →+* ℂ) (hι' : ∀ c, ι' (algebraMap F E c) = ι c) (t : ℤ) :
    ∃ β : ℝ, 0 < β ∧ ∀ (y : Y) (z : ℂ),
      (((P⁻¹.val * (ρ (Fr y)).val.map (algebraMap F E) * P.val).toSquareBlock δ t).charpoly.map
        ι').IsRoot z → ‖z‖ = β ^ deg y := by
  classical
  -- a block form of `ρ'` over `ℂ_ℓ`
  obtain ⟨P', d', hup', hirr'⟩ := exists_isGradedUpper_irreducible_blocks
    (fun g : Γ => (ρ' g).val.map (algebraMap F ℂ_[ℓ]))
  set hsK := sumSplitting (R := ℂ_[ℓ]) r r'
  set Q : (Matrix (Fin r) (Fin r) ℂ_[ℓ])ˣ :=
    Units.map (RingHom.mapMatrix (algebraMap E ℂ_[ℓ])).toMonoidHom P
  set P₀ := hsK.blockDiagUnit Q P'
  set X : Γ → Matrix (Fin r) (Fin r) E := fun g =>
    P⁻¹.val * (ρ g).val.map (algebraMap F E) * P.val
  set X' : Γ → Matrix (Fin r') (Fin r') ℂ_[ℓ] := fun g =>
    P'⁻¹.val * (ρ' g).val.map (algebraMap F ℂ_[ℓ]) * P'.val
  set X₀ : Γ → Matrix (Fin (r + r')) (Fin (r + r')) ℂ_[ℓ] := fun g =>
    P₀⁻¹.val * (sumRep ρ ρ' g).val.map (algebraMap F ℂ_[ℓ]) * P₀.val
  have hmapK : ∀ g, (ρ g).val.map (algebraMap F ℂ_[ℓ]) =
      ((ρ g).val.map (algebraMap F E)).map (algebraMap E ℂ_[ℓ]) := fun g => by
    rw [Matrix.map_map, IsScalarTower.algebraMap_eq F E ℂ_[ℓ]]
    rfl
  have hX : ∀ g, X₀ g = hsK.blockDiag ((X g).map (algebraMap E ℂ_[ℓ])) (X' g) := fun g => by
    simp only [X₀, X']
    rw [sumRep_val, sumSplitting_blockDiag_map]
    change hsK.blockDiag Q⁻¹.val P'⁻¹.val * hsK.blockDiag _ _ * hsK.blockDiag Q.val P'.val = _
    rw [IsSplitting.blockDiag_mul, IsSplitting.blockDiag_mul, hmapK]
    congr 1
    simp only [X, Matrix.map_mul]
    rfl
  have hne (j : Fin r) (j' : Fin r') : Fin.castAdd r' j ≠ Fin.natAdd r j' := by
    simp [Fin.ext_iff]
    omega
  -- the block form of `ρ ⊕ ρ'`
  have hup₀ : ∀ g, IsGradedUpper (sumGrading δ d') (X₀ g) := fun g => by
    rw [hX]
    refine IsGradedUpper.sumSplitting_blockDiag (fun i j h => ?_) (hup' g)
    exact (congrArg (algebraMap E ℂ_[ℓ]) (hup g i j h)).trans (map_zero _)
  have hirr₀ : ∀ (t : ℤ) (W' : Submodule ℂ_[ℓ] (Fin (r + r') → ℂ_[ℓ])),
      W' ≤ coordSubspace (K := ℂ_[ℓ]) (fun i => sumGrading δ d' i = t) → W' ≠ ⊥ →
      (∀ g, ∀ v ∈ W', gradedDiag (sumGrading δ d') (X₀ g) *ᵥ v ∈ W') →
      W' = coordSubspace (K := ℂ_[ℓ]) (fun i => sumGrading δ d' i = t) := by
    intro t W' hW hW0 hst
    obtain ⟨s, rfl | rfl⟩ := Int.even_or_odd' t
    · refine eq_coordSubspace_of_coordMatrix (Fin.castAdd_injective r r') (sumGrading δ d') (2 * s)
        δ s (fun i => ?_) (fun g => gradedDiag (sumGrading δ d') (X₀ g))
        (fun g => (gradedDiag δ (X g)).map (algebraMap E ℂ_[ℓ]))
        (fun g => ?_) (fun W'' => hirr s W'') W' hW hW0 hst
      · induction i using Fin.addCases with
        | left j =>
          simp only [sumGrading_castAdd]
          exact ⟨fun h => ⟨j, rfl, by omega⟩, fun ⟨j', hj', h⟩ => by
            rw [Fin.castAdd_injective r r' hj'] at h
            omega⟩
        | right j =>
          simp only [sumGrading_natAdd]
          exact ⟨fun h => by omega, fun ⟨j', hj', _⟩ => (hne j' j hj').elim⟩
      · rw [hX, gradedDiag_sumSplitting_blockDiag, ← gradedDiag_map]
        exact IsSplitting.blockDiag_mul_J _ _ _
    · refine eq_coordSubspace_of_coordMatrix (Fin.natAdd_injective r' r) (sumGrading δ d')
        (2 * s + 1) d' s (fun i => ?_) (fun g => gradedDiag (sumGrading δ d') (X₀ g))
        (fun g => gradedDiag d' (X' g))
        (fun g => ?_) (fun W'' => hirr' s W'') W' hW hW0 hst
      · induction i using Fin.addCases with
        | left j =>
          simp only [sumGrading_castAdd]
          exact ⟨fun h => by omega, fun ⟨j', hj', _⟩ => (hne j j' hj'.symm).elim⟩
        | right j =>
          simp only [sumGrading_natAdd]
          exact ⟨fun h => ⟨j, rfl, by omega⟩, fun ⟨j', hj', h⟩ => by
            rw [Fin.natAdd_injective r' r hj'] at h
            omega⟩
      · rw [hX, gradedDiag_sumSplitting_blockDiag]
        exact IsSplitting.blockDiag_mul_K' _ _ _
  -- extend `ι'` to `ℂ_ℓ` on the relevant countable set
  set S : Set E := Set.range (fun p : Y × Fin r × Fin r => X (Fr p.1) p.2.1 p.2.2) ∪
    Set.range (fun p : Y × ℕ => algebraMap F E
      (((ρ (Fr p.1)).val.charpoly * (ρ' (Fr p.1)).val.charpoly).coeff p.2))
  have hS : S.Countable := (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨φK, hφK⟩ := exists_padicComplex_ringHom_eq_on_intermediateField E ι' hS
  have hreal₀ : ∀ (y : Y) (m : ℕ), (φK.comp (algebraMap F ℂ_[ℓ]))
      ((sumRep ρ ρ' (Fr y)).val.charpoly.coeff m) ∈ Set.range ((↑) : ℝ → ℂ) := by
    intro y m
    rw [sumRep_val, charpoly_sumSplitting_blockDiag, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply F E ℂ_[ℓ]]
    change φK ((algebraMap F E _ : E) : ℂ_[ℓ]) ∈ _
    rw [hφK _ (Algebra.subset_adjoin (Or.inr ⟨(y, m), rfl⟩)), hι']
    exact hreal y m
  obtain ⟨β, hβ, hβy⟩ := exists_norm_eq_pow_of_isGradedUpper_linear (ℓ := ℓ) φK H φ hcomm hD1 Fr deg
    hFr hdeg hfin hq (fun m τ hτ => htf _ m τ hτ) (sumRep ρ ρ') (continuous_sumRep hρ hρ') hFK
    hreal₀ P₀ (sumGrading δ d') hup₀ hirr₀ (2 * t)
  refine ⟨β, hβ, fun y z hz => hβy y z ?_⟩
  -- the block `2 t` of `ρ ⊕ ρ'` is the block `t` of `ρ`
  obtain ⟨n', e, he, hre⟩ := exists_injective_forall_iff_exists fun i => δ i = t
  have he' : Function.Injective (Fin.castAdd r' ∘ e) := (Fin.castAdd_injective r r').comp he
  have hre' : ∀ i, sumGrading δ d' i = 2 * t ↔ ∃ j, (Fin.castAdd r' ∘ e) j = i := fun i => by
    induction i using Fin.addCases with
    | left j =>
      simp only [sumGrading_castAdd, Function.comp_apply, (Fin.castAdd_injective r r').eq_iff]
      rw [← hre j]
      omega
    | right j =>
      simp only [sumGrading_natAdd, Function.comp_apply]
      exact ⟨fun h => by omega, fun ⟨j', hj'⟩ => (hne _ _ hj').elim⟩
  have hchar : ((X₀ (Fr y)).toSquareBlock (sumGrading δ d') (2 * t)).charpoly =
      ((X (Fr y)).toSquareBlock δ t).charpoly.map (algebraMap E ℂ_[ℓ]) := by
    have hsub : (hsK.blockDiag ((X (Fr y)).map (algebraMap E ℂ_[ℓ]))
        (X' (Fr y))).submatrix
          (Fin.castAdd r' ∘ e) (Fin.castAdd r' ∘ e) =
        ((X (Fr y)).submatrix e e).map (algebraMap E ℂ_[ℓ]) := by
      ext j j'
      exact sumSplitting_blockDiag_castAdd_castAdd _ _ (e j) (e j')
    rw [hX, ← charpoly_submatrix_eq_charpoly_toSquareBlock _ _ _ he' hre', hsub,
      Matrix.charpoly_map, charpoly_submatrix_eq_charpoly_toSquareBlock _ _ _ he hre]
  have hcoeff : ∀ m, ((X (Fr y)).toSquareBlock δ t).charpoly.coeff m ∈ Algebra.adjoin ℤ S :=
    fun m => charpoly_coeff_mem_of_forall_mem (Algebra.adjoin ℤ S).toSubring _ (fun i j => by
      have hmem : X (Fr y) i.1 j.1 ∈ S := Set.mem_union_left _ ⟨(y, i.1, j.1), rfl⟩
      exact Algebra.subset_adjoin hmem) m
  have hpoly : (((X (Fr y)).toSquareBlock δ t).charpoly.map (algebraMap E ℂ_[ℓ])).map φK =
      ((X (Fr y)).toSquareBlock δ t).charpoly.map ι' := by
    rw [Polynomial.map_map]
    ext m
    rw [Polynomial.coeff_map, Polynomial.coeff_map, RingHom.comp_apply]
    exact hφK _ (hcoeff m)
  rw [hchar, hpoly]
  exact hz


end Purity

end Stacks.EtaleCohomology

end
