module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantWeightBoundLinear

/-!
# Weil II 1.5.1 with coefficients in any topological field

The group-level form of Weil II 1.5.1 (Kedlaya, *Fourier transforms and p-adic Weil II*,
Theorem 6.5.2) of `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock` and
`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isGradedUpper`, for a representation
`ρ : Γ → GL_r(F)` with coefficients in a topological field `F` (with an algebra structure towards
the complete algebraically closed field `K` of the block form) in place of `ℚ_ℓ`: the
`ι`-reality hypothesis and the Frobenius trace formula are asked for `F`-linear representations.

## Main results

* `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock_linear`.
* `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isGradedUpper_linear`.
-/

@[expose] public noncomputable section

open Filter Topology NormedSpace Matrix Polynomial Stacks.LAdic

namespace Stacks.EtaleCohomology

section Purity

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] [IsAlgClosed K]
  {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [Algebra F K]

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {r : ℕ}

/-- A matrix that vanishes between different values of `d` stabilizes the coordinate subspace
of any union of the level sets of `d`. -/
private theorem mem_stabilizerSubalgebra_coordSubspace_of_blockDiag {L : Type*}
    [NontriviallyNormedField L] {d : Fin r → ℤ} {M : Matrix (Fin r) (Fin r) L}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) (Q : ℤ → Prop) :
    M ∈ stabilizerSubalgebra (coordSubspace (K := L) fun i => Q (d i)) :=
  fun _ hv => mulVec_mem_coordSubspace (fun i j hj hi => hM i j fun e => hi (e ▸ hj)) hv

include ℓ in
/-- **The constituents of an `ι`-real representation are `ι`-pure** (Weil II 1.5.1; Kedlaya,
*Fourier transforms and p-adic Weil II*, Theorem 6.5.2), at the level of groups, with coefficients
in a topological field `F` with an algebra structure towards `K` (for `F = ℚ_ℓ` this is
`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock`).

Let `Γ` be a compact group, `H ⊴ Γ` with `Γ / H` abelian (the geometric fundamental group),
`φ ∈ Γ` (a geometric Frobenius) satisfying the geometric input `hD1` of Weil II 1.3.4, and
`Fr y ∈ φ ^ deg y H` (`deg y > 0`) Frobenius elements at the points `y` of `Y`, finitely many of
each degree.  Let `ρ : Γ → GL_r(ℚ_ℓ)` be continuous, with `ι`-real Frobenius characteristic
polynomials (`ι = ι_K ∘ (ℚ_ℓ → K)`), and assume that every continuous representation of `Γ`
satisfies the Frobenius trace formula with `q > 1`.  Over `K`, let `P₀⁻¹ ρ P₀` be block upper
triangular along `d`, with block diagonal part `σ'` continuous and semisimple and with
irreducible blocks.  Then on every block `t` the Frobenius eigenvalues are pure: there is
`β > 0` such that every root of the characteristic polynomial of the `t`-th diagonal block of
`σ'(Fr y)` has absolute value `β ^ deg y` along `ι_K`. -/
public theorem exists_norm_eq_pow_of_isRoot_toSquareBlock_linear (ι : K →+* ℂ) (H : Subgroup Γ)
    [H.Normal] (φ : Γ) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    {Y : Type*} (Fr : Y → Γ) (deg : Y → ℕ) (hFr : ∀ y, (φ ^ deg y)⁻¹ * Fr y ∈ H)
    (hdeg : ∀ y, 0 < deg y) (hfin : ∀ m : ℕ, 0 < m → {y : Y | deg y ∣ m}.Finite)
    {q : ℝ} (hq : 1 < q)
    (htf : ∀ (m : ℕ) (τ : Γ →* GL (Fin m) F), Continuous τ →
      SatisfiesFrobeniusTraceFormula q (ι.comp (algebraMap F K)) H φ Fr deg τ)
    (ρ : Γ →* GL (Fin r) F) (hρ : Continuous ρ)
    (hreal : ∀ (y : Y) (m : ℕ), (ι.comp (algebraMap F K))
      ((ρ (Fr y) : Matrix (Fin r) (Fin r) F).charpoly.coeff m) ∈ Set.range ((↑) : ℝ → ℂ))
    (P₀ : (Matrix (Fin r) (Fin r) K)ˣ) (d : Fin r → ℤ) (σ' : Γ →* (Matrix (Fin r) (Fin r) K)ˣ)
    (hup : ∀ g, IsGradedUpper d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
      (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
        (P₀ : Matrix (Fin r) (Fin r) K)))
    (hσ' : ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) = gradedDiag d
      (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
        (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
          (P₀ : Matrix (Fin r) (Fin r) K)))
    (hσc : Continuous fun g => (σ' g : Matrix (Fin r) (Fin r) K))
    (hss : ∀ W : Submodule K (Fin r → K),
      (∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (Fin r → K), IsCompl W W' ∧
        ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W')
    (hirr : ∀ (t : ℤ) (W' : Submodule K (Fin r → K)),
      W' ≤ coordSubspace (K := K) (fun i => d i = t) → W' ≠ ⊥ →
      (∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W') →
        W' = coordSubspace (K := K) (fun i => d i = t))
    (t : ℤ) :
    ∃ β : ℝ, 0 < β ∧ ∀ (y : Y) (c : ℂ),
      (((σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlock d t).charpoly.map ι).IsRoot c →
        ‖c‖ = β ^ deg y := by
  classical
  obtain ⟨U, -, -, hk, hG, hu, N, A, B, hA, hAn, hBn, hBG, -, hAB, hsum, hW⟩ :=
    exists_monodromy_weights (ℓ := ℓ) ι σ' hσc H φ hcomm hD1 hss
  have hH : ∀ ψ : H → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a) → ψ = 0 := by
    intro ψ hadd hcont hinv
    have hmem : ∀ a : ↥(H ⊓ ⊤), (a : Γ) ∈ H := fun a => a.2.1
    set ψ' : ↥(H ⊓ ⊤) → K := fun a => ψ ⟨a, hmem a⟩
    have h0 := hD1 ⊤ inferInstance isOpen_univ ψ'
      (fun a b => hadd ⟨a, hmem a⟩ ⟨b, hmem b⟩)
      (hcont.comp ((continuous_subtype_val).subtype_mk _))
      (fun a b hab => hinv _ _ (by rw [Subgroup.index_top, pow_one] at hab; exact hab))
    funext a
    exact congrFun h0 ⟨a, a.2, Subgroup.mem_top _⟩
  have hGH : ∀ g ∈ (H ⊓ U).map σ', ∃ h ∈ H, σ' h = g := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨h, hh.1, rfl⟩
  set e : ℕ := U.index * ℓ ^ N with he_def
  have he : 0 < e := Nat.mul_pos hk (pow_pos (Fact.out : ℓ.Prime).pos N)
  have hzu : IsUnit (exp B) := isUnit_exp_of_mem_ball (𝕂 := ℚ_[ℓ]) (mem_eball_expSeries hBn)
  have hσbd : ∀ g i j, d i ≠ d j → (σ' g : Matrix (Fin r) (Fin r) K) i j = 0 := by
    intro g i j h
    rw [hσ' g]
    exact if_neg h
  have hstab : ∀ (Q : ℤ → Prop) [DecidablePred Q] (g : Γ), (σ' g : Matrix (Fin r) (Fin r) K) ∈
      stabilizerSubalgebra (coordSubspace (K := K) fun i => Q (d i)) := fun Q _ g =>
    mem_stabilizerSubalgebra_coordSubspace_of_blockDiag (hσbd g) Q
  have hV : ∀ t : ℤ, ∃ rt : ℝ, ∀ (μ : K) (v : Fin r → K), v ≠ 0 → (∀ i, d i ≠ t → v i = 0) →
      exp B *ᵥ v = μ • v → ‖ι μ‖ = rt := by
    intro t
    obtain ⟨hzt, -, rt, hrt, -⟩ := hW _ (hstab (· = t)) (hirr t)
    refine ⟨rt, fun μ v hv hvt hzv => hrt μ ?_⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvt⟩) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨Subtype.ext ?_, fun h => hv (congrArg Subtype.val h)⟩
    rw [stabRestrict_apply]
    exact hzv
  choose rr hrr using hV
  have hzbd : ∀ i j, d i ≠ d j → exp B i j = 0 := by
    intro i j hij
    obtain ⟨hzt, -⟩ := hW _ (hstab (· = d j)) (hirr (d j))
    have h1 : (Pi.single j 1 : Fin r → K) ∈ coordSubspace (K := K) fun i => d i = d j := by
      intro i hi
      have : i ≠ j := fun e => hi (congrArg d e)
      simp [this]
    have h2 := hzt _ h1 i hij
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h2
  have hrootnorm : ∀ (P : ℤ → Prop) [DecidablePred P] (x : K),
      x ∈ ((exp B).toSquareBlockProp fun i => P (d i)).charpoly.roots →
        ∃ i, P (d i) ∧ ‖ι x‖ = rr (d i) := fun P _ x hx =>
    exists_norm_eq_of_isRoot_toSquareBlockProp ι hzbd hrr P
      ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hx)
  by_cases hne : ∃ i, d i = t
  swap
  · refine ⟨1, one_pos, fun y c hc => ?_⟩
    have : IsEmpty {i // d i = t} := ⟨fun i => hne ⟨i.1, i.2⟩⟩
    rw [Matrix.charpoly, Matrix.det_isEmpty, Polynomial.map_one] at hc
    simp at hc
  obtain ⟨i₀, hi₀⟩ := hne
  set β := rr t with hβ_def
  have hβ : 0 < β := by
    have : Nonempty {i // d i = t} := ⟨⟨i₀, hi₀⟩⟩
    have hdeg0 : ((exp B).toSquareBlockProp fun i => d i = t).charpoly.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero,
        Matrix.charpoly_natDegree_eq_dim]
      exact_mod_cast Fintype.card_ne_zero
    obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_root _ hdeg0
    obtain ⟨i, hi, hni⟩ := exists_norm_eq_of_isRoot_toSquareBlockProp ι hzbd hrr (· = t) hc0
    have h0 := ne_zero_of_isRoot_toSquareBlockProp hzu
      (fun i j hj hi => hzbd i j fun e => hi (e ▸ hj)) hc0
    have hi' : d i = t := hi
    rw [hi'] at hni
    rw [hβ_def, ← hni]
    exact norm_pos_iff.mpr ((map_ne_zero ι).mpr h0)
  set p : Fin r → Prop := fun i => β < rr (d i) with hp_def
  set W := coordSubspace (K := K) p with hW_def
  set N' := Fintype.card {i // p i} with hN'_def
  set k := N' + 1 with hk_def
  set Zp := (exp B).toSquareBlockProp p with hZp_def
  set Zq := (exp B).toSquareBlockProp fun i => ¬ p i with hZq_def
  have hzc : (exp B).charpoly = Zp.charpoly * Zq.charpoly :=
    charpoly_eq_mul_toSquareBlockProp _ p fun i hi j hj =>
      hzbd i j fun e => hi (by show β < rr (d i); rw [e]; exact hj)
  have hroots : (exp B).charpoly.roots = Zp.charpoly.roots + Zq.charpoly.roots := by
    rw [hzc, Polynomial.roots_mul]
    exact ((Matrix.charpoly_monic _).mul (Matrix.charpoly_monic _)).ne_zero
  have hM1 : ∀ x ∈ Zp.charpoly.roots.map (fun c => ‖ι c‖), β < x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨i, hi, hn⟩ := hrootnorm (fun s => β < rr s) c hc
    rw [hn]
    exact hi
  have hM2 : ∀ x ∈ Zq.charpoly.roots.map (fun c => ‖ι c‖), 0 ≤ x ∧ x ≤ β := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨i, hi, hn⟩ := hrootnorm (fun s => ¬ β < rr s) c hc
    refine ⟨norm_nonneg _, ?_⟩
    rw [hn]
    exact not_lt.mp hi
  have hcardp : Multiset.card Zp.charpoly.roots = N' := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
  set D := (Zp.charpoly.roots.map fun c => ‖ι c‖).prod with hD_def
  have hD : ‖ι Zp.det‖ = D := by
    rw [Matrix.det_eq_prod_roots_charpoly, norm_map_multiset_prod]
  have hDpos : 0 < D := Multiset.prod_pos fun x hx => hβ.trans (hM1 x hx)
  have hT : 0 < D * β := mul_pos hDpos hβ
  have hTz : ∀ c, (Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _)
      (compoundMonoidHom k (hzu.unit : Matrix (Fin r) (Fin r) K))).charpoly.IsRoot c →
        ‖ι c‖ ≤ D * β := by
    intro c hc
    rw [Matrix.charpoly_reindex, IsUnit.unit_spec] at hc
    have hmem : c ∈ (compoundMonoidHom k (exp B)).charpoly.roots :=
      (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr hc
    have hcp := charpoly_compoundMonoidHom_map k (RingHom.id K) (exp B)
    rw [Polynomial.map_id, Polynomial.map_id] at hcp
    rw [hcp, show (((exp B).charpoly.roots.powersetCard k).map fun s =>
        Polynomial.X - Polynomial.C s.prod) = (((exp B).charpoly.roots.powersetCard k).map
          Multiset.prod).map (fun a => Polynomial.X - Polynomial.C a) by
        rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C] at hmem
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hmem
    rw [Multiset.mem_powersetCard] at hs
    rw [norm_map_multiset_prod]
    refine multiset_prod_le_mul_of_card_eq_succ hβ.le hM1 hM2 ?_ ?_
    · rw [← Multiset.map_add, ← hroots]
      exact Multiset.map_le_map hs.1
    · rw [Multiset.card_map, Multiset.card_map, hs.2, hcardp]
  have hcoinv : ∀ i : ℕ, 0 < i → ∀ ζ : ℂ, ((LinearMap.charpoly (coinvariantsFrobenius H
      (tensorPowerRepresentation (exteriorPowerRepresentation k ρ) (2 * i)) φ)).map
        (ι.comp (algebraMap F K))).IsRoot ζ →
      ‖ζ‖ ≤ q ^ ((i : ℝ) * (2 * Real.logb q (D * β) / e)) := by
    intro i _ ζ hζ
    have h4 := norm_pow_le_of_isRoot_coinvariantsFrobenius_linear ι H φ ρ P₀ d σ' hup hσ' U.index
      hGH hG hu hA hAn hBn hBG hAB hsum (z := hzu.unit) hzu.unit_spec k (2 * i) hT.le hTz ζ hζ
    have h5 := (pow_le_pow_iff_le_rpow_logb hq hT (norm_nonneg ζ) he (2 * i)).mp h4
    convert h5 using 2
    push_cast
    ring
  have hrank : ∀ (y : Y) (α : ℂ), ((exteriorPowerRepresentation k ρ (Fr y) :
      Matrix (Fin (Fintype.card (Set.powersetCard (Fin r) k)))
        (Fin (Fintype.card (Set.powersetCard (Fin r) k))) F).charpoly.map
          (ι.comp (algebraMap F K))).IsRoot α →
        ‖α‖ ^ e ≤ (D * β) ^ deg y := by
    intro y α hα
    have hτc := continuous_exteriorPowerRepresentation k hρ
    have h := norm_le_of_satisfiesFrobeniusTraceFormula hq.le (ι.comp (algebraMap F K)) H φ
      Fr deg hfin (exteriorPowerRepresentation k ρ)
      (fun y m => exteriorPowerRepresentation_charpoly_real k _ ρ (Fr y) (hreal y) m)
      (2 * Real.logb q (D * β) / e)
      (fun i _ => htf _ _ (continuous_tensorPowerRepresentation hτc (2 * i))) hcoinv y (hdeg y)
      α hα
    refine (pow_le_pow_iff_le_rpow_logb hq hT (norm_nonneg α) he (deg y)).mpr ?_
    convert h using 2
    ring
  have hdet : ∀ (Q : ℤ → Prop) [DecidablePred Q] (y : Y),
      ‖ι ((σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlockProp fun i => Q (d i)).det‖ ^ e =
        ‖ι ((exp B).toSquareBlockProp fun i => Q (d i)).det‖ ^ deg y := by
    intro Q _ y
    obtain ⟨hzW, hdetW⟩ := norm_det_pow_eq_of_stable ι σ' hσc H φ hH U.index hGH hG hu hA hAn
      hBn hBG hAB hsum (W := coordSubspace (K := K) fun i => Q (d i)) (fun g => hstab Q g)
      (hFr y)
    simpa only [stabRestrict, det_restrict_coordSubspace] using hdetW
  have hle : ∀ (y : Y) (μ : K), ((σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlockProp
      fun i => d i = t).charpoly.IsRoot μ → ‖ι μ‖ ^ e ≤ β ^ deg y := by
    intro y μ hμ
    obtain ⟨v, hv0, hvt, hgv⟩ := exists_mulVec_eq_of_isRoot_toSquareBlockProp
      (p := fun i => d i = t) (fun i j hj hi => hσbd (Fr y) i j fun e => hi (e ▸ hj)) hμ
    have hvW : v ∉ W := by
      intro hvW
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
      have hdi : d i = t := by
        by_contra h
        exact hi (hvt i h)
      have hpi : p i := by
        by_contra h
        exact hi (hvW i h)
      change β < rr (d i) at hpi
      rw [hdi] at hpi
      exact lt_irrefl _ hpi
    set f := Matrix.toLin' (σ' (Fr y) : Matrix (Fin r) (Fin r) K) with hf_def
    have hWf : ∀ v ∈ W, f v ∈ W := fun v hv => by
      rw [Matrix.toLin'_apply]
      exact hstab (fun s => β < rr s) (Fr y) v hv
    have hE := hasEigenvalue_exteriorPower_map_mul_det f W hWf hvW
      (by rw [Matrix.toLin'_apply]; exact hgv)
    have hfr : Module.finrank K W = N' := by
      rw [LinearEquiv.finrank_eq (coordSubspaceEquiv p), Module.finrank_fintype_fun_eq_card]
    rw [hfr, Module.End.hasEigenvalue_iff_isRoot_charpoly] at hE
    have hcp := charpoly_exteriorPower_map_map (RingHom.id K) f k
    rw [Polynomial.map_id, Polynomial.map_id, hf_def, Matrix.charpoly_toLin'] at hcp
    rw [hcp] at hE
    have hρc : (σ' (Fr y) : Matrix (Fin r) (Fin r) K).charpoly =
        (ρ (Fr y) : Matrix (Fin r) (Fin r) F).charpoly.map (algebraMap F K) := by
      rw [hσ' (Fr y), charpoly_gradedDiag (hup (Fr y)), Matrix.coe_units_inv,
        Matrix.charpoly_units_conj', Matrix.charpoly_map]
    rw [hρc, ← charpoly_exteriorPowerRepresentation_map k (algebraMap F K) ρ (Fr y)] at hE
    have hα := hrank y (ι (μ * LinearMap.det (f.restrict hWf)))
      (by rw [← Polynomial.map_map]; exact Polynomial.IsRoot.map hE)
    have hdetW : ‖ι (LinearMap.det (f.restrict hWf))‖ ^ e = D ^ deg y := by
      rw [← hD, det_restrict_coordSubspace hWf]
      exact hdet (fun s => β < rr s) y
    rw [map_mul, norm_mul, mul_pow, hdetW, mul_pow, mul_comm (D ^ deg y)] at hα
    exact le_of_mul_le_mul_right hα (pow_pos hDpos _)
  refine ⟨β ^ ((e : ℝ)⁻¹), Real.rpow_pos_of_pos hβ _, fun y c hc => ?_⟩
  set Mt := (σ' (Fr y) : Matrix (Fin r) (Fin r) K).toSquareBlock d t with hMt_def
  set R := (β ^ ((e : ℝ)⁻¹)) ^ deg y with hR_def
  have hR0 : 0 ≤ R := pow_nonneg (Real.rpow_nonneg hβ.le _) _
  have hRe : R ^ e = β ^ deg y := by
    rw [hR_def, ← pow_mul, mul_comm, pow_mul, Real.rpow_inv_natCast_pow hβ.le he.ne']
  have hroots' : (Mt.charpoly.map ι).roots = Mt.charpoly.roots.map ι :=
    ((Matrix.charpoly_monic _).roots_map_of_card_eq_natDegree ι
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hcm : c ∈ (Mt.charpoly.map ι).roots :=
    (Polynomial.mem_roots ((Matrix.charpoly_monic _).map ι).ne_zero).mpr hc
  refine norm_eq_of_forall_norm_le_of_norm_prod_eq (s := (Mt.charpoly.map ι).roots) (R := R) ?_ ?_
    c hcm
  · intro x hx
    rw [hroots'] at hx
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
    have h1 := hle y μ ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hμ)
    rw [← hRe] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 he.ne').mp h1
  · rw [hroots', ← map_multiset_prod, ← Matrix.det_eq_prod_roots_charpoly, Multiset.card_map,
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
    have hdetV : ‖ι Mt.det‖ ^ e = _ := hdet (· = t) y
    have hzt : ∀ x ∈ ((exp B).toSquareBlockProp fun i => d i = t).charpoly.roots,
        ‖ι x‖ = β := by
      intro x hx
      obtain ⟨i, hi, hn⟩ := hrootnorm (· = t) x hx
      have hi' : d i = t := hi
      rw [hn, hi']
    rw [Matrix.det_eq_prod_roots_charpoly ((exp B).toSquareBlockProp _),
      norm_map_multiset_prod, Multiset.map_congr rfl hzt, Multiset.map_const',
      Multiset.prod_replicate, IsAlgClosed.card_roots_eq_natDegree,
      Matrix.charpoly_natDegree_eq_dim] at hdetV
    rw [← pow_left_inj₀ (norm_nonneg _) (pow_nonneg hR0 _) he.ne', hdetV, ← pow_mul R,
      mul_comm (Fintype.card _) e, pow_mul, hRe, ← pow_mul, mul_comm]
    rw [pow_mul]

include ℓ in
/-- **The constituents of an `ι`-real representation are `ι`-pure** (Weil II 1.5.1; Kedlaya,
Theorem 6.5.2), for a block triangular form: if `P₀⁻¹ ρ P₀` is block upper triangular along `d`
over `K` with irreducible diagonal blocks (a subspace of a block stable under the block diagonal
parts is zero or the block), then on every block `t` there is `β > 0` with every root of the
characteristic polynomial of the block `t` of `P₀⁻¹ ρ(F_y) P₀` of absolute value `β ^ deg y`
along `ι`.  The hypotheses on `Γ`, `H`, `φ`, `Fr`, `deg`, `ρ` are those of
`Stacks.EtaleCohomology.exists_norm_eq_pow_of_isRoot_toSquareBlock_linear`, and `F → K` is
continuous. For `F = ℚ_ℓ` this is `Stacks.EtaleCohomology.exists_norm_eq_pow_of_isGradedUpper`. -/
public theorem exists_norm_eq_pow_of_isGradedUpper_linear (ι : K →+* ℂ) (H : Subgroup Γ)
    [H.Normal] (φ : Γ) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hD1 : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) → ψ = 0)
    {Y : Type*} (Fr : Y → Γ) (deg : Y → ℕ) (hFr : ∀ y, (φ ^ deg y)⁻¹ * Fr y ∈ H)
    (hdeg : ∀ y, 0 < deg y) (hfin : ∀ m : ℕ, 0 < m → {y : Y | deg y ∣ m}.Finite)
    {q : ℝ} (hq : 1 < q)
    (htf : ∀ (m : ℕ) (τ : Γ →* GL (Fin m) F), Continuous τ →
      SatisfiesFrobeniusTraceFormula q (ι.comp (algebraMap F K)) H φ Fr deg τ)
    (ρ : Γ →* GL (Fin r) F) (hρ : Continuous ρ) (hFK : Continuous (algebraMap F K))
    (hreal : ∀ (y : Y) (m : ℕ), (ι.comp (algebraMap F K))
      ((ρ (Fr y) : Matrix (Fin r) (Fin r) F).charpoly.coeff m) ∈ Set.range ((↑) : ℝ → ℂ))
    (P₀ : (Matrix (Fin r) (Fin r) K)ˣ) (d : Fin r → ℤ)
    (hup : ∀ g, IsGradedUpper d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
      (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
        (P₀ : Matrix (Fin r) (Fin r) K)))
    (hirr : ∀ (t : ℤ) (W' : Submodule K (Fin r → K)),
      W' ≤ coordSubspace (K := K) (fun i => d i = t) → W' ≠ ⊥ →
      (∀ g, ∀ v ∈ W', gradedDiag d (((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) :
        Matrix (Fin r) (Fin r) K) * (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
          (P₀ : Matrix (Fin r) (Fin r) K)) *ᵥ v ∈ W') →
        W' = coordSubspace (K := K) (fun i => d i = t))
    (t : ℤ) :
    ∃ β : ℝ, 0 < β ∧ ∀ (y : Y) (c : ℂ),
      (((((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) *
        (ρ (Fr y) : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
          (P₀ : Matrix (Fin r) (Fin r) K)).toSquareBlock d t).charpoly.map ι).IsRoot c →
        ‖c‖ = β ^ deg y := by
  classical
  set P1 : Matrix (Fin r) (Fin r) K := ((P₀⁻¹ : (Matrix (Fin r) (Fin r) K)ˣ) :
    Matrix (Fin r) (Fin r) K) with hP1
  set P0 : Matrix (Fin r) (Fin r) K := (P₀ : Matrix (Fin r) (Fin r) K) with hP0
  set T : Γ → Matrix (Fin r) (Fin r) K := fun g =>
    P1 * (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) * P0 with hT_def
  have hρK : ∀ g h : Γ, (ρ (g * h) : Matrix (Fin r) (Fin r) F).map (algebraMap F K) =
      (ρ g : Matrix (Fin r) (Fin r) F).map (algebraMap F K) *
        (ρ h : Matrix (Fin r) (Fin r) F).map (algebraMap F K) := by
    intro g h
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have hTmul : ∀ g h, T (g * h) = T g * T h := by
    intro g h
    simp only [hT_def, hρK, mul_assoc]
    rw [hP1, hP0, Units.mul_inv_cancel_left]
  have hT1 : T 1 = 1 := by
    simp only [hT_def, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one,
      hP1, hP0, Units.inv_mul]
  let σ' : Γ →* (Matrix (Fin r) (Fin r) K)ˣ :=
    { toFun := fun g => ⟨gradedDiag d (T g), gradedDiag d (T g⁻¹), by
          rw [← gradedDiag_mul (hup g) (hup g⁻¹), ← hTmul, mul_inv_cancel, hT1, gradedDiag_one],
        by rw [← gradedDiag_mul (hup g⁻¹) (hup g), ← hTmul, inv_mul_cancel, hT1, gradedDiag_one]⟩
      map_one' := Units.ext (by simp only [hT1, gradedDiag_one, Units.val_one])
      map_mul' := fun g h => Units.ext (by
        simp only [Units.val_mul]
        rw [hTmul, gradedDiag_mul (hup g) (hup h)]) }
  have hσv : ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) = gradedDiag d (T g) := fun g => rfl
  have hgd : Continuous (gradedDiag d : Matrix (Fin r) (Fin r) K → Matrix (Fin r) (Fin r) K) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun T : Matrix (Fin r) (Fin r) K => if d i = d j then T i j else 0
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const
  have hσc : Continuous fun g => (σ' g : Matrix (Fin r) (Fin r) K) := by
    refine hgd.comp ?_
    exact (continuous_const.matrix_mul (((Units.continuous_val.comp hρ).matrix_map
      hFK))).matrix_mul continuous_const
  have hstab : ∀ (Q : ℤ → Prop) [DecidablePred Q] (g : Γ), (σ' g : Matrix (Fin r) (Fin r) K) ∈
      stabilizerSubalgebra (coordSubspace (K := K) fun i => Q (d i)) := fun Q _ g =>
    mem_stabilizerSubalgebra_coordSubspace_of_blockDiag (fun i j h => by
      rw [hσv]
      exact if_neg h) Q
  set S : Set (Module.End K (Fin r → K)) :=
    Set.range fun g => Matrix.toLin' (σ' g : Matrix (Fin r) (Fin r) K) with hS_def
  have hSiff : ∀ X : Submodule K (Fin r → K), IsStableUnder S X ↔
      ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra X := fun _ =>
    ⟨fun h g => le_comap_toLin'_iff.mp (h _ ⟨g, rfl⟩), by
      rintro h _ ⟨g, rfl⟩
      exact le_comap_toLin'_iff.mpr (h g)⟩
  have htop : sSup {X | IsIrreducibleUnder S X} = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    rw [pi_eq_sum_univ v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hmem : (fun j => if i = j then (1 : K) else 0) ∈
        coordSubspace (K := K) (fun j => d j = d i) := by
      intro j hj
      have : i ≠ j := fun e => hj (by rw [e])
      simp [this]
    refine Submodule.mem_sSup_of_mem ?_ hmem
    refine ⟨fun h => ?_, (hSiff _).mpr (hstab (· = d i)), fun W' hle hW' => ?_⟩
    · have := (Submodule.mem_bot K).mp (h ▸ hmem)
      simpa using congrFun this i
    · by_cases h : W' = ⊥
      · exact Or.inl h
      · exact Or.inr (hirr (d i) W' hle h fun g v hv => (hSiff W').mp hW' g v hv)
  have hss : ∀ W : Submodule K (Fin r → K),
      (∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (Fin r → K), IsCompl W W' ∧
        ∀ g, (σ' g : Matrix (Fin r) (Fin r) K) ∈ stabilizerSubalgebra W' := by
    intro W hW
    obtain ⟨W', hc, hW'⟩ := exists_isCompl_of_sSup_eq_top htop ((hSiff W).mpr hW)
    exact ⟨W', hc, (hSiff W').mp hW'⟩
  obtain ⟨β, hβ, h⟩ := exists_norm_eq_pow_of_isRoot_toSquareBlock_linear (ℓ := ℓ) ι H φ hcomm hD1
    Fr deg hFr hdeg hfin hq htf ρ hρ hreal P₀ d σ' hup hσv hσc hss
    (fun t W' hle hne hW' => hirr t W' hle hne fun g v hv => hW' g v hv) t
  refine ⟨β, hβ, fun y c hc => h y c ?_⟩
  rwa [hσv, toSquareBlock_gradedDiag]

end Purity

end Stacks.EtaleCohomology

end
