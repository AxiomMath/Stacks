module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RealizableBlockPurityLinear

/-!
# Weil II 1.5.1 for an absolutely irreducible `ι'`-realizable `E`-linear representation

Let `E` be a finite extension of `ℚ_ℓ` with a basis `b`, and `ρ, ρ' : Γ → GL(E)` representations
whose restrictions of scalars `Res_b ρ`, `Res_b ρ'` are continuous, such that `ρ ⊕ ρ'` has
Frobenius characteristic polynomials with real coefficients along one embedding `ι' : E → ℂ`. If
`ρ` is absolutely irreducible (no nonzero proper subspace over any algebraically closed field `K`
over `E` is stable), then `ρ` is `ι'`-pure: there is `β > 0` with every root along `ι'` of the
characteristic polynomial of `ρ(F_y)` of absolute value `β ^ deg y`
(`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isIotaRealizable_restrictScalarsRep`; Weil II 1.5.1,
Kedlaya, *Fourier transforms and p-adic Weil II*, Theorem 6.5.2).

The topology on `E` induced by the multiplication matrices in the basis `b` is
`Stacks.EtaleCohomology.leftMulMatrixTopology`; for it a representation is continuous exactly when
its restriction of scalars is
(`Stacks.EtaleCohomology.continuous_iff_continuous_restrictScalarsRep`).

## Main definitions

* `Stacks.EtaleCohomology.leftMulMatrixTopology`.

## Main results

* `Stacks.EtaleCohomology.continuous_iff_continuous_restrictScalarsRep`.
* `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isIotaRealizable_restrictScalarsRep`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Topology

variable {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)

/-- **The topology on `E` induced by the multiplication matrices in the basis `b`**, i.e. by the
embedding `E → M_d(ℚ_ℓ)`, `x ↦ (multiplication by x)`. -/
@[instance_reducible]
public def leftMulMatrixTopology : TopologicalSpace E :=
  TopologicalSpace.induced (Algebra.leftMulMatrix b) inferInstance

/-- `Algebra.leftMulMatrix b` is inducing for the topology `leftMulMatrixTopology b`. -/
public theorem isInducing_leftMulMatrix :
    @Topology.IsInducing E _ (leftMulMatrixTopology b) _ (Algebra.leftMulMatrix b) :=
  @Topology.IsInducing.mk E _ (leftMulMatrixTopology b) _ _ rfl

/-- `E` is a topological ring for `Stacks.EtaleCohomology.leftMulMatrixTopology`. -/
public theorem isTopologicalRing_leftMulMatrixTopology :
    @IsTopologicalRing E (leftMulMatrixTopology b) _ := by
  let := leftMulMatrixTopology b
  have hi := isInducing_leftMulMatrix b
  have hc : Continuous (Algebra.leftMulMatrix b) := hi.continuous
  refine { continuous_add := ?_, continuous_mul := ?_, continuous_neg := ?_ } <;>
    rw [hi.continuous_iff] <;> simp only [Function.comp_def, map_add, map_mul, map_neg]
  · exact (hc.comp continuous_fst).add (hc.comp continuous_snd)
  · exact (hc.comp continuous_fst).mul (hc.comp continuous_snd)
  · exact hc.neg

/-- **A family of matrices over `E` is continuous iff its restriction of scalars is**, for the
topology `Stacks.EtaleCohomology.leftMulMatrixTopology`. -/
public theorem continuous_iff_continuous_restrictScalarsMatrix {X : Type*} [TopologicalSpace X]
    {m : ℕ} (M : X → Matrix (Fin m) (Fin m) E) :
    letI := leftMulMatrixTopology b
    Continuous M ↔ Continuous fun x => restrictScalarsMatrix b (M x) := by
  let := leftMulMatrixTopology b
  have hi := isInducing_leftMulMatrix b
  constructor
  · intro h
    refine continuous_matrix fun p q => ?_
    obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
    simp only [restrictScalarsMatrix_apply]
    exact (hi.continuous.comp (h.matrix_elem i j)).matrix_elem l l'
  · intro h
    refine continuous_matrix fun i j => ?_
    rw [hi.continuous_iff]
    refine continuous_matrix fun l l' => ?_
    have := h.matrix_elem (finProdFinEquiv (i, l)) (finProdFinEquiv (j, l'))
    simp only [restrictScalarsMatrix_apply] at this
    exact this

/-- **A representation over `E` is continuous iff its restriction of scalars is**, for the
topology `Stacks.EtaleCohomology.leftMulMatrixTopology`. -/
public theorem continuous_iff_continuous_restrictScalarsRep {G : Type*} [Group G]
    [TopologicalSpace G] {m : ℕ} (σ : G →* GL (Fin m) E) :
    letI := leftMulMatrixTopology b
    Continuous σ ↔ Continuous (restrictScalarsRep b σ) := by
  let := leftMulMatrixTopology b
  have hinv : ∀ g, (((restrictScalarsRep b σ g)⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]) :
      Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ]) =
      restrictScalarsMatrix b (((σ g)⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) :=
    fun g => rfl
  rw [Units.continuous_iff, Units.continuous_iff, continuous_iff_continuous_restrictScalarsMatrix b,
    continuous_iff_continuous_restrictScalarsMatrix b]
  simp only [hinv]
  exact Iff.rfl

/-- **An embedding of `E` into a normed `ℚ_ℓ`-algebra is continuous** for the topology
`Stacks.EtaleCohomology.leftMulMatrixTopology`: the coordinates of `x` in `b` are linear in the
entries of the multiplication matrix of `x`. -/
public theorem continuous_algHom_leftMulMatrixTopology {K : Type*} [NormedRing K]
    [NormedAlgebra ℚ_[ℓ] K] (j : E →ₐ[ℚ_[ℓ]] K) :
    letI := leftMulMatrixTopology b
    Continuous j := by
  let := leftMulMatrixTopology b
  have hi := isInducing_leftMulMatrix b
  have hrepr : ∀ (x : E) (l : Fin d),
      b.repr x l = ∑ l', b.repr 1 l' * Algebra.leftMulMatrix b x l l' := by
    intro x l
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
    have h1 : ∑ l', b.repr 1 l' • (x * b l') = x := by
      rw [show ∑ l', b.repr 1 l' • (x * b l') = x * ∑ l', b.repr 1 l' • b l' by
        simp only [Finset.mul_sum, mul_smul_comm], b.sum_repr, mul_one]
    calc b.repr x l = b.repr (∑ l', b.repr 1 l' • (x * b l')) l := by rw [h1]
      _ = ∑ l', b.repr 1 l' * b.repr (x * b l') l := by
        rw [map_sum, Finsupp.finsetSum_apply]
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hj : (j : E → K) = fun x =>
      ∑ l, (∑ l', b.repr 1 l' * Algebra.leftMulMatrix b x l l') • j (b l) := by
    funext x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
    exact Finset.sum_congr rfl fun l _ => by rw [hrepr x l]
  rw [hj]
  refine continuous_finsetSum _ fun l _ => Continuous.smul ?_ continuous_const
  exact continuous_finsetSum _ fun l' _ =>
    continuous_const.mul (hi.continuous.matrix_elem l l')

end Topology

section Purity

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

/-- **An absolutely irreducible `ι'`-realizable `E`-linear representation is `ι'`-pure**
(Weil II 1.5.1; Kedlaya, *Fourier transforms and p-adic Weil II*, Theorem 6.5.2). Let `E` be a
finite extension of `ℚ_ℓ` with basis `b`, and `Γ, H, φ, Fr, deg` as in
`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock_linear`, every `E`-linear
representation with continuous restriction of scalars satisfying the Frobenius trace formula
along every embedding of `E`. Let `ρ, ρ'` be `E`-linear with continuous restrictions of scalars,
`ρ ⊕ ρ'` with `ι'`-real Frobenius characteristic polynomials, and `ρ` absolutely irreducible.
Then there is `β > 0` with every root along `ι'` of the characteristic polynomial of `ρ(F_y)` of
absolute value `β ^ deg y`. -/
public theorem exists_norm_eq_pow_of_isIotaRealizable_restrictScalarsRep
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (H : Subgroup Γ) [H.Normal] (φ : Γ)
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → ℂ_[ℓ], (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    {Y : Type*} [Countable Y] (Fr : Y → Γ) (deg : Y → ℕ) (hFr : ∀ y, (φ ^ deg y)⁻¹ * Fr y ∈ H)
    (hdeg : ∀ y, 0 < deg y) (hfin : ∀ m : ℕ, 0 < m → {y : Y | deg y ∣ m}.Finite) {q : ℝ}
    (hq : 1 < q)
    (htf : ∀ (ι₁ : E →+* ℂ) (m : ℕ) (τ : Γ →* GL (Fin m) E),
      Continuous (restrictScalarsRep b τ) → SatisfiesFrobeniusTraceFormula q ι₁ H φ Fr deg τ)
    {r r' : ℕ} (ρ : Γ →* GL (Fin r) E) (hρ : Continuous (restrictScalarsRep b ρ))
    (ρ' : Γ →* GL (Fin r') E) (hρ' : Continuous (restrictScalarsRep b ρ')) (ι' : E →+* ℂ)
    (hreal : ∀ (y : Y) (m : ℕ),
      ι' (((ρ (Fr y)).val.charpoly * (ρ' (Fr y)).val.charpoly).coeff m) ∈ Set.range ((↑) : ℝ → ℂ))
    (hirr : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra E K] (W : Submodule K (Fin r → K)),
      (∀ g, ∀ v ∈ W, (ρ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ β : ℝ, 0 < β ∧ ∀ (y : Y) (z : ℂ),
      ((ρ (Fr y)).val.charpoly.map ι').IsRoot z → ‖z‖ = β ^ deg y := by
  classical
  let := leftMulMatrixTopology b
  have := isTopologicalRing_leftMulMatrixTopology b
  have : Algebra.IsAlgebraic ℚ_[ℓ] E := Algebra.IsAlgebraic.of_finite ℚ_[ℓ] E
  let j : E →ₐ[ℚ_[ℓ]] ℂ_[ℓ] := IsAlgClosed.lift
  let : Algebra E ℂ_[ℓ] := j.toRingHom.toAlgebra
  let E₀ : IntermediateField ℚ_[ℓ] ℂ_[ℓ] := j.fieldRange
  let j₀ : E ≃ₐ[ℚ_[ℓ]] E₀ := AlgEquiv.ofInjectiveField j
  let : Algebra E E₀ := j₀.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower E E₀ ℂ_[ℓ] := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hFK : Continuous (algebraMap E ℂ_[ℓ]) := continuous_algHom_leftMulMatrixTopology b j
  have hmap : ∀ T : Matrix (Fin r) (Fin r) E₀,
      ((1 : (Matrix (Fin r) (Fin r) E₀)ˣ)⁻¹ : (Matrix (Fin r) (Fin r) E₀)ˣ) * T *
        ((1 : (Matrix (Fin r) (Fin r) E₀)ˣ) : Matrix (Fin r) (Fin r) E₀) = T := fun T => by
    rw [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  have hgd : ∀ T : Matrix (Fin r) (Fin r) E₀, gradedDiag (fun _ : Fin r => (0 : ℤ)) T = T :=
    fun T => funext fun i => funext fun i' => ite_eq_left rfl
  obtain ⟨β, hβ, hβy⟩ := exists_norm_eq_pow_toSquareBlock_of_isIotaRealizable_linear ι' H φ hcomm
    hD1 Fr deg hFr hdeg hfin hq
    (fun ι₁ m τ hτ => htf ι₁ m τ ((continuous_iff_continuous_restrictScalarsRep b τ).1 hτ)) ρ
    ((continuous_iff_continuous_restrictScalarsRep b ρ).2 hρ) ρ'
    ((continuous_iff_continuous_restrictScalarsRep b ρ').2 hρ') hFK hreal E₀ 1
    (fun _ => (0 : ℤ)) (fun _ _ _ h => absurd h (lt_irrefl 0))
    (fun t W' hW' hne hst => by
      by_cases ht : t = 0
      · subst ht
        have htop : coordSubspace (K := ℂ_[ℓ]) (fun _ : Fin r => (0 : ℤ) = 0) = ⊤ :=
          eq_top_iff.2 fun v _ i hi => absurd rfl hi
        rw [htop]
        refine (hirr ℂ_[ℓ] W' fun g v hv => ?_).resolve_left hne
        have h := hst g v hv
        rwa [hmap, hgd, Matrix.map_map, ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq] at h
      · exact absurd (eq_bot_iff.2 fun v hv => (Submodule.mem_bot _).2 (funext fun i =>
          hW' hv i (Ne.symm ht))) hne)
    (ι'.comp j₀.symm.toAlgHom.toRingHom)
    (fun c => congrArg ι' (j₀.symm_apply_apply c)) 0
  refine ⟨β, hβ, fun y z hz => hβy y z ?_⟩
  have hchar : ∀ T : Matrix (Fin r) (Fin r) E₀,
      ((((1 : (Matrix (Fin r) (Fin r) E₀)ˣ)⁻¹ : (Matrix (Fin r) (Fin r) E₀)ˣ) * T *
        ((1 : (Matrix (Fin r) (Fin r) E₀)ˣ) : Matrix (Fin r) (Fin r) E₀)).toSquareBlock
          (fun _ => (0 : ℤ)) 0).charpoly = T.charpoly := fun T => by
    rw [hmap, ← charpoly_submatrix_eq_charpoly_toSquareBlock _ _ _ Function.injective_id
      (fun i => ⟨fun _ => ⟨i, rfl⟩, fun _ => rfl⟩), Matrix.submatrix_id_id]
  rw [hchar, Matrix.charpoly_map, Polynomial.map_map]
  rwa [show (ι'.comp j₀.symm.toAlgHom.toRingHom).comp (algebraMap E E₀) = ι' from
    RingHom.ext fun c => congrArg ι' (j₀.symm_apply_apply c)]

end Purity

end Stacks.EtaleCohomology

end
