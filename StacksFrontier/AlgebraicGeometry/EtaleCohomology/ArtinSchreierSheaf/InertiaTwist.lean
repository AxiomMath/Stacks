module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.GaloisCharacter
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Sheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CurvePointInertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreierInertia

/-!
# Twists by Artin–Schreier sheaves of large pole order at a missing point

Let `Spec R` be an irreducible `k`-scheme (`k` finite with `q` elements), `τ` a continuous
representation of `π₁(Spec R, η̄)` on `E ^ m`, `E` a finite extension of a topological field `F`
(e.g. `ℚ_ℓ`) with continuity read through restriction of scalars, and `A` a discrete valuation
ring with perfect residue field and fraction field the function field `K` of `Spec R` (a missing
point of `Spec R`, e.g. `∞` on an open of the affine line). There is `N` such that for every
`g ∈ R` which is `π ^ (-n) · u` in `K` with `n > N` prime to `p` and `u` a unit of `A`, the
representation `τ ⊗ L_ψ(g)` of the inertia group at the missing point has no invariants and no
coinvariants: one element of inertia acts by `M` with `M - 1` invertible.

## Main results

* `Stacks.EtaleCohomology.isUnit_of_isUnit_restrictScalarsMatrix`: a square matrix whose
  restriction of scalars is invertible is invertible.
* `Stacks.ArtinSchreier.exists_forall_invariants_eq_bot_and_subsingleton_coinvariants`: for pole
  order `n > N` prime to `p`, the twist `τ ⊗ L_ψ(g)` restricted to inertia at the missing point
  has no invariants and no coinvariants.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Stacks.FundamentalGroup

universe u

namespace Stacks.EtaleCohomology

section RestrictScalars

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- Restriction of scalars of matrices along a basis of `E` over `F` commutes with subtraction. -/
theorem restrictScalarsMatrix_sub {m n : ℕ} (M N : Matrix (Fin m) (Fin n) E) :
    restrictScalarsMatrix b (M - N) = restrictScalarsMatrix b M - restrictScalarsMatrix b N := by
  ext p q
  simp [restrictScalarsMatrix, map_sub]

/-- A square matrix over `E` whose restriction of scalars to `F` is invertible is invertible. -/
theorem isUnit_of_isUnit_restrictScalarsMatrix {m : ℕ} {M : Matrix (Fin m) (Fin m) E}
    (h : IsUnit (restrictScalarsMatrix b M)) : IsUnit M := by
  classical
  by_contra hM
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hM
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  let Z : Matrix (Fin m) (Fin 1) E := Matrix.of fun i _ => v i
  have hZ : M * Z = 0 := by
    ext i j
    simpa [Z, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hv i
  have hRZ : restrictScalarsMatrix b Z = 0 := by
    have h0 : restrictScalarsMatrix b M * restrictScalarsMatrix b Z = 0 := by
      rw [← restrictScalarsMatrix_mul, hZ]
      ext p q
      simp [restrictScalarsMatrix]
    obtain ⟨u, hu⟩ := h
    have := congrArg (fun X => ((u⁻¹ : (Matrix (Fin (m * d)) (Fin (m * d)) F)ˣ) :
      Matrix (Fin (m * d)) (Fin (m * d)) F) * X) h0
    simp only [Matrix.mul_zero, ← Matrix.mul_assoc] at this
    rwa [← hu, Units.inv_mul, Matrix.one_mul] at this
  apply hv0
  funext i
  have hi : Algebra.leftMulMatrix b (v i) = 0 := by
    ext l l'
    have := congrFun (congrFun hRZ (finProdFinEquiv (i, l))) (finProdFinEquiv (0, l'))
    rw [restrictScalarsMatrix_apply] at this
    simpa [Z] using this
  exact (Algebra.leftMulMatrix_injective b) (hi.trans (map_zero _).symm)

end RestrictScalars

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

section Inertia

variable (k : Type u) [Field k] [Fintype k] (R : Type u) [CommRing R] [Algebra k R]
  [ConnectedSpace (Spec (.of R))] [IrreducibleSpace (Spec (.of R))]
  (L Ω : Type u) [Field L] [Field Ω]
  [Algebra ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) L]
  [IsSepClosure ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) L]
  [Algebra L Ω] [Algebra ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω]
  [IsScalarTower ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) L Ω]
  [IsAlgClosed Ω]
  [Algebra.IsAlgebraic ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω]
  (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra A ((Spec (.of R)).residueField (genericPoint (Spec (.of R))))]
  [IsFractionRing A ((Spec (.of R)).residueField (genericPoint (Spec (.of R))))] [Algebra A L]
  [IsScalarTower A ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) L]
  (P : Ideal (integralClosure A L)) [P.IsMaximal] [PerfectField (IsLocalRing.ResidueField A)]
  (p : ℕ) [Fact p.Prime] [CharP ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) p]
  [Algebra k A] [Algebra k ((Spec (.of R)).residueField (genericPoint (Spec (.of R))))]
  [IsScalarTower k A ((Spec (.of R)).residueField (genericPoint (Spec (.of R))))]

/-- **The local terms at a missing point of a twist by an Artin–Schreier sheaf of large pole
order vanish.** Let `τ` be a representation of `π₁(Spec R, η̄)` on `E ^ m`, continuous through the
restriction of scalars to a topological field `F`, and `ψ` a nontrivial additive character of
`k`. There is `N` such that for every `g ∈ R` which is `π ^ (-n) · u` in the function field, with
`u` a unit of the discrete valuation ring `A` of the missing point, `n > N` and `p ∤ n`, the
representation `τ ⊗ L_ψ(g)` (`σ ↦ ψ(-χ_g(σ)) τ(σ)`) of the inertia group at the missing point has
no invariants and no coinvariants. The hypotheses on `p₀` say that the geometric generic point
sends `g` to `π ^ (-n) · u` and `k ⊆ R` to `k ⊆ K`.

An element `σ` of inertia acts by `M = ψ(-c) τ(σ)` with `M - 1` invertible
(`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_isUnit_mul_sub_one` applied to the
restriction of scalars, the Artin–Schreier character on inertia being `σ ↦ σ t - t` by
`Stacks.ArtinSchreier.exists_algebraMap_eq_fiberRoot_galoisToFundamentalGroup`); such an `M`
fixes no nonzero vector, and every vector is `M v - v`. -/
theorem exists_forall_invariants_eq_bot_and_subsingleton_coinvariants {π : A}
    (hπ : Irreducible π) {F E : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [T1Space F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) {m : ℕ}
    (τ : EtaleFundamentalGroup (Spec (.of R)) ((algebraicClosureGeometricPoint
      ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω).map
        ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R))))) →* GL (Fin m) E)
    (hτ : Continuous (restrictScalarsRep b τ)) (ψ : AddChar k E) (hψ : ψ ≠ 1) :
    ∃ N : ℕ, ∀ (n : ℕ) (u : A), N < n → ¬ p ∣ n → IsUnit u → ∀ (g : R)
      (p₀ : (finiteEtaleFiberFunctor ((algebraicClosureGeometricPoint
        ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω).map
          ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))))).obj
            (cover k R g)),
      (fiberRingHom p₀).hom (algebraMap R (Ring k g) g) =
        algebraMap ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω
          ((algebraMap A _ π)⁻¹ ^ n * algebraMap A _ u) →
      (∀ c : k, (fiberRingHom p₀).hom (algebraMap k (Ring k g) c) =
        algebraMap ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω
          (algebraMap k _ c)) →
      Representation.invariants ((matrixRepresentation
          (characterTwist τ (artinSchreierCharacter k R g ψ _ p₀))).comp
            (curvePointInertia (Spec (.of R)) L Ω A P).subtype) = ⊥ ∧
        Subsingleton (Representation.Coinvariants ((matrixRepresentation (characterTwist τ
          (artinSchreierCharacter k R g ψ _ p₀))).comp
            (curvePointInertia (Spec (.of R)) L Ω A P).subtype)) := by
  classical
  let K := (Spec (.of R)).residueField (genericPoint (Spec (.of R)))
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let φ := galoisToFundamentalGroup (Spec (.of R)) L Ω
  let ρ₀ : Gal(L/K) →* GL (Fin (m * d)) F := restrictScalarsRep b (τ.comp φ.toMonoidHom)
  let T : k → Matrix (Fin (m * d)) (Fin (m * d)) F :=
    fun c => restrictScalarsMatrix b (Matrix.scalar (Fin m) (ψ (-c)))
  obtain ⟨c₁, hc₁⟩ := AddChar.ne_one_iff.1 hψ
  have hc₀ : IsUnit (T (-c₁) - 1) := by
    rw [show T (-c₁) - 1 = restrictScalarsMatrix b (Matrix.scalar (Fin m) (ψ c₁ - 1)) by
      simp only [T, neg_neg, map_sub, map_one, restrictScalarsMatrix_sub,
        restrictScalarsMatrix_one]]
    exact ((Ne.isUnit (sub_ne_zero.2 hc₁)).map (Matrix.scalar (Fin m))).map
      (restrictScalarsMonoidHom b m)
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.exists_forall_exists_mem_inertia_isUnit_mul_sub_one
    A K L p k P hπ ρ₀ (hτ.comp φ.continuous) T (-c₁) hc₀
  refine ⟨N, fun n u hn hpn hu g p₀ hg hk => ?_⟩
  obtain ⟨t, ht, hσt⟩ := exists_algebraMap_eq_fiberRoot_galoisToFundamentalGroup k R g L Ω p₀
  have hroot : t ^ Fintype.card k - t =
      algebraMap K L ((algebraMap A K π)⁻¹ ^ n * algebraMap A K u) := by
    apply (algebraMap L Ω).injective
    let r : Ω := fiberRoot p₀
    have e : r ^ Fintype.card k = r + _ := fiberRoot_pow_card p₀
    rw [map_sub, map_pow, show algebraMap L Ω t = r from ht, e,
      ← IsScalarTower.algebraMap_apply K L Ω]
    exact (add_sub_cancel_left _ _).trans hg
  obtain ⟨σ, hσI, hσ, hunit⟩ := hN n u hn hpn hu t hroot
  have ha : Multiplicative.toAdd ((torsorCover k R g).character _ p₀ (φ σ)) = -c₁ := by
    have h1 := hσt σ
    have h2 : ((fiberRingHom p₀).hom (algebraMap k (Ring k g)
        (Multiplicative.toAdd ((torsorCover k R g).character _ p₀ (φ σ)))) : Ω) =
          algebraMap K Ω (algebraMap k K
            (Multiplicative.toAdd ((torsorCover k R g).character _ p₀ (φ σ)))) := hk _
    rw [hσ, h2, ← IsScalarTower.algebraMap_apply K L Ω] at h1
    exact ((algebraMap k K).injective ((algebraMap K Ω).injective h1)).symm
  let χ := artinSchreierCharacter k R g ψ _ p₀
  have hχ : (χ (φ σ) : E) = ψ c₁ := by rw [artinSchreierCharacter_apply, ha, neg_neg]
  let M : Matrix (Fin m) (Fin m) E := (characterTwist τ χ (φ σ)).val
  have hMdef : M = ψ c₁ • (τ (φ σ)).val := hχ ▸ characterTwist_val τ χ (φ σ)
  have hT : restrictScalarsMatrix b (M - 1) = T (-c₁) * (ρ₀ σ : Matrix _ _ F) - 1 := by
    rw [hMdef, restrictScalarsMatrix_sub, restrictScalarsMatrix_one, Matrix.smul_eq_diagonal_mul,
      restrictScalarsMatrix_mul]
    simp only [T, neg_neg, ρ₀, restrictScalarsRep_val, MonoidHom.comp_apply]
    rfl
  have hMunit : IsUnit (M - 1) := isUnit_of_isUnit_restrictScalarsMatrix b (by rwa [hT])
  let h : curvePointInertia (Spec (.of R)) L Ω A P := ⟨φ σ, Subgroup.mem_map_of_mem _ hσI⟩
  have hρh : ∀ v, ((matrixRepresentation (characterTwist τ χ)).comp
      (curvePointInertia (Spec (.of R)) L Ω A P).subtype) h v = M.mulVec v :=
    fun v => matrixRepresentation_apply _ _ v
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 hMunit
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.2 hMunit
  constructor
  · rw [eq_bot_iff]
    intro v hv
    rw [Representation.mem_invariants] at hv
    rw [Submodule.mem_bot]
    apply hinj
    rw [Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.one_mulVec, ← hρh, hv h, sub_self]
  · have h0 : ∀ w, Representation.Coinvariants.mk _ w = (0 : Representation.Coinvariants
        ((matrixRepresentation (characterTwist τ χ)).comp
          (curvePointInertia (Spec (.of R)) L Ω A P).subtype)) := by
      intro w
      rw [Representation.Coinvariants.mk_eq_zero]
      obtain ⟨x, hx⟩ := hsurj w
      refine Representation.Coinvariants.mem_ker_of_eq h x w ?_
      rw [hρh]
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at hx
    constructor
    intro x y
    obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
    rw [h0 x, h0 y]

end Inertia

end Stacks.ArtinSchreier
