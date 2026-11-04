module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyGroupTheory
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.LAdicTameInertia

/-!
# Grothendieck's local monodromy theorem for a field with finite residue field

Let `A` be a discrete valuation ring with finite residue field of characteristic `p` and
cardinality `q`, `L` a separable closure of its fraction field `K`, `P` a maximal ideal of the
integral closure of `A` in `L`, `I` its inertia group, and `ρ : Gal(L/K) → GL_r(ℤ_ℓ)` a continuous
representation, `ℓ ≠ p`.  Combining the `ℓ`-adic tame character
(`Stacks.FundamentalGroup.exists_ladicTameCharacter`) with the group-theoretic half of
Grothendieck's argument (`Stacks.EtaleCohomology.exists_monodromy_logarithm_of_tame`,
`Stacks.EtaleCohomology.mulVec_eq_of_tame`): there is `T ∈ I` in the open subgroup
`J = I ∩ ρ⁻¹(1 + ℓ M_r(ℤ_ℓ))` such that

* the `J`-invariant integral vectors are those fixed by `ρ T`;
* for every arithmetic Frobenius `Fr`, a power `ρ(T) ^ m`, `m > 0`, is unipotent with logarithm
  `N` satisfying `N F = q F N` for `F = ρ(Fr⁻¹)` the geometric Frobenius, and
  `ker N = ker (ρ(T) ^ m - 1)`.

## Main results

* `Stacks.EtaleCohomology.exists_monodromy_logarithm_of_inertia`.
* `Stacks.EtaleCohomology.isClosed_inertia`: inertia groups are closed in the Krull topology.

## References

* A. Grothendieck, appendix to J.-P. Serre and J. Tate, *Good reduction of abelian varieties*,
  Ann. of Math. 88 (1968).
* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7, 1.8.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open scoped Pointwise
open Matrix

namespace Stacks.EtaleCohomology

/-- The inertia group of a maximal ideal of the integral closure in an algebraic Galois extension
is closed in the Krull topology. -/
public theorem isClosed_inertia
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [Normal K L]
    [Algebra A L] [IsScalarTower A K L] (P : Ideal (integralClosure A L)) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    IsClosed (P.inertia Gal(L/K) : Set Gal(L/K)) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  have hI : (P.inertia Gal(L/K) : Set Gal(L/K)) = ⋂ b : integralClosure A L,
      ⋃ c ∈ {c : integralClosure A L | c - b ∈ P},
        {σ : Gal(L/K) | σ (b : L) = (c : L)} := by
    ext σ
    simp only [SetLike.mem_coe, Ideal.mem_inertia, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_setOf_eq, exists_prop]
    refine forall_congr' fun b => ⟨fun h => ⟨σ • b, h, ?_⟩, fun ⟨c, hc, hσc⟩ => ?_⟩
    · exact (algebraMap_galRestrict_apply A σ b).symm
    · have : σ • b = c := Subtype.ext ((algebraMap_galRestrict_apply A σ b).trans hσc)
      rwa [this]
  have hclopen : ∀ (x y : L), IsClopen {σ : Gal(L/K) | σ x = y} := fun x y =>
    ⟨by
      have : {σ : Gal(L/K) | σ x = y}ᶜ = ⋃ z ∈ {z : L | z ≠ y}, {σ : Gal(L/K) | σ x = z} := by
        ext σ; simp
      rw [← isOpen_compl_iff, this]
      exact isOpen_biUnion fun z _ => isOpen_krullTopology_apply_eq' K x z,
     isOpen_krullTopology_apply_eq' K x y⟩
  rw [hI]
  refine isClosed_iInter fun b => ?_
  have hfin : (Set.range fun σ : Gal(L/K) => σ (b : L)).Finite := by
    refine ((minpoly K (b : L)).rootSet L).toFinite.subset ?_
    rintro _ ⟨σ, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral (b : L)), ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have : (⋃ c ∈ {c : integralClosure A L | c - b ∈ P}, {σ : Gal(L/K) | σ (b : L) = (c : L)}) =
      ⋃ z ∈ (Set.range fun σ : Gal(L/K) => σ (b : L)) ∩
        {z : L | ∃ c : integralClosure A L, c - b ∈ P ∧ (c : L) = z},
        {σ : Gal(L/K) | σ (b : L) = z} := by
    ext σ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Set.mem_inter_iff,
      Set.mem_range]
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨_, ⟨⟨σ, h⟩, c, hc, rfl⟩, h⟩
    · rintro ⟨z, ⟨-, c, hc, rfl⟩, h⟩
      exact ⟨c, hc, h⟩
  rw [this]
  exact (hfin.subset Set.inter_subset_left).isClosed_biUnion fun z _ => (hclopen _ _).isClosed

/-- **Grothendieck's local monodromy theorem** (Weil II 1.7.1, 1.8) for a discrete valuation ring
`A` with finite residue field of characteristic `p` and cardinality `q`, a separable closure `L`
of its fraction field `K`, a maximal ideal `P` of the integral closure of `A` in `L` with inertia
group `I` and decomposition group `D`, and a continuous `ρ : Gal(L/K) → GL_r(ℤ_ℓ)`, `ℓ ≠ p`.
There is `T ∈ I` with `ρ T ≡ 1 (mod ℓ)` such that every integral vector fixed by `ρ T` is fixed by
`ρ σ` for every `σ ∈ I` with `ρ σ ≡ 1 (mod ℓ)`, and for every arithmetic Frobenius `Fr ∈ D`
(acting on the residue field by `x ↦ x ^ q`), on `ℚ_ℓ^r` some power `ρ(T) ^ m`, `m > 0`, is
unipotent with nilpotent logarithm `N`, `N F = q F N` for the geometric Frobenius `F = ρ(Fr⁻¹)`,
and `ker N` the vectors fixed by `ρ(T) ^ m`. -/
public theorem exists_monodromy_logarithm_of_inertia
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [Finite (IsLocalRing.ResidueField A)] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A)) {r : ℕ}
    (ρ : Gal(L/K) →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    let q := Nat.card (IsLocalRing.ResidueField A)
    ∃ T ∈ P.inertia Gal(L/K), ρ T ∈ congruenceSubgroup ℓ r 1 ∧
      (∀ σ ∈ P.inertia Gal(L/K), ρ σ ∈ congruenceSubgroup ℓ r 1 →
        ∀ v : Fin r → ℤ_[ℓ],
          ((ρ T : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v →
          ((ρ σ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) ∧
      ∀ Fr ∈ MulAction.stabilizer Gal(L/K) P,
        (∀ b : integralClosure A L, Fr • b - b ^ q ∈ P) →
        let φ : Matrix (Fin r) (Fin r) ℤ_[ℓ] →ₐ[ℤ_[ℓ]] Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]) :=
          (Matrix.toLinAlgEquiv' (R := ℚ_[ℓ]) (n := Fin r)).toAlgHom.restrictScalars ℤ_[ℓ] |>.comp
            (AlgHom.mapMatrix (Algebra.ofId ℤ_[ℓ] ℚ_[ℓ]))
        ∃ m : ℕ, 0 < m ∧ ∃ N : Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]), IsNilpotent N ∧
          N * φ (ρ Fr⁻¹ : GL (Fin r) ℤ_[ℓ]) =
            (q : ℚ_[ℓ]) • (φ (ρ Fr⁻¹ : GL (Fin r) ℤ_[ℓ]) * N) ∧
          ∀ v, N v = 0 ↔ (φ (ρ T : GL (Fin r) ℤ_[ℓ]) ^ m) v = v := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro q
  obtain ⟨t, htc, htker, htFr, -⟩ := Stacks.FundamentalGroup.exists_ladicTameCharacter A K L P ℓ hℓ
  have hτ : ∀ Fr ∈ MulAction.stabilizer Gal(L/K) P,
      (∀ b : integralClosure A L, Fr • b - b ^ q ∈ P) → ∀ σ ∈ P.inertia Gal(L/K),
      ∀ U : OpenSubgroup Gal(L/K), ∃ m : ℕ, ℓ.Coprime m ∧ (Fr * σ * Fr⁻¹ * (σ ^ q)⁻¹) ^ m ∈ U := by
    intro Fr hFrD hFr σ hσI U
    obtain ⟨τ, hτ, hτ1, -⟩ := htFr Fr hFrD hFr ⟨σ, hσI⟩
    obtain ⟨m, hm, hmU⟩ := htker τ hτ1 U
    exact ⟨m, hm, by rwa [← hτ]⟩
  let J : Subgroup Gal(L/K) := P.inertia Gal(L/K) ⊓ (congruenceSubgroup ℓ r 1).comap ρ
  have hJ : IsClosed (J : Set Gal(L/K)) :=
    (isClosed_inertia A K L P).inter
      (Subgroup.isClosed_of_isOpen _ ((isOpen_congruenceSubgroup 1).preimage hρ))
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJ.isCompact
  let t' : J →* Multiplicative ℤ_[ℓ] := t.comp (Subgroup.inclusion inf_le_left)
  have ht' : Continuous t' :=
    htc.comp (continuous_subtype_val.subtype_mk fun x => (inf_le_left : J ≤ _) x.2)
  have hker : ∀ τ : J, t' τ = 1 → ρ τ = 1 := fun τ h =>
    map_eq_one_of_forall_exists_coprime_pow_mem hρ τ.2.2 (htker _ h)
  obtain ⟨T, hgen⟩ := Stacks.FundamentalGroup.exists_forall_exists_eq_mul_of_compactSpace t' ht'
  refine ⟨T, T.2.1, T.2.2, fun σ hσI hσ v hv =>
    mulVec_eq_of_tame hρ t' ht' hker T hgen hv ⟨σ, hσI, hσ⟩, fun Fr hFrD hFr => ?_⟩
  have hq : 2 ≤ q := Finite.one_lt_card
  exact exists_monodromy_logarithm_of_tame hρ hq T.2.2 (hτ Fr hFrD hFr T T.2.1)

end Stacks.EtaleCohomology
