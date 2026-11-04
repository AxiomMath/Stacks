module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.LAdicTameInertia
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyInertia

/-!
# Inertia and decomposition groups of a missing point of a curve in its fundamental group

Let `V` be an irreducible scheme with function field `K = κ(η)`, `L` a separable closure of `K`
inside an algebraically closed field `Ω`, and `φ : Gal(L/K) → π₁(V, η̄)` the canonical continuous
homomorphism (`AlgebraicGeometry.galoisToFundamentalGroup`). A discrete valuation ring `A` with
fraction field `K` (for a smooth curve `V ⊆ X` and a closed point `y ∈ X ∖ V`, the local ring
`𝒪_{X,y}`) and a maximal ideal `P` of the integral closure of `A` in `L` (a place of `L` over `y`)
give the inertia group `I_P` and the decomposition group `D_P` inside `Gal(L/K)`; their images
under `φ` are the **inertia group** and the **decomposition group** of `V` at the missing point,
`Stacks.FundamentalGroup.curvePointInertia` and `Stacks.FundamentalGroup.curvePointDecomposition`.

Everything about the local field is stated on `I_P ⊆ D_P ⊆ Gal(L/K)` itself, so the local results
of this directory apply verbatim: the `ℓ`-adic tame character
(`Stacks.FundamentalGroup.exists_ladicTameCharacter`) and Grothendieck's local monodromy theorem
(`Stacks.EtaleCohomology.exists_monodromy_logarithm_of_inertia`) for a continuous representation
of `π₁(V, η̄)`, restricted along `φ`.

## Main definitions

* `Stacks.FundamentalGroup.curvePointInertia` — `φ(I_P) ⊆ π₁(V, η̄)`.
* `Stacks.FundamentalGroup.curvePointDecomposition` — `φ(D_P) ⊆ π₁(V, η̄)`.

## Main results

* `Stacks.FundamentalGroup.curvePointInertia_le_curvePointDecomposition` — the inertia group lies
  in the decomposition group.
* `Stacks.FundamentalGroup.isCompact_curvePointInertia` — the inertia group is compact.
* `Stacks.FundamentalGroup.exists_monodromy_logarithm_of_curvePointInertia` — Grothendieck's local
  monodromy theorem for a continuous `ρ : π₁(V, η̄) → GL_r(ℤ_ℓ)` at the missing point.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7, 1.8.
* [Stacks Project, Tag 0BQH](https://stacks.math.columbia.edu/tag/0BQH)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped Pointwise

universe u

namespace Stacks.FundamentalGroup

variable (V : Scheme.{u}) [IrreducibleSpace V] (L Ω : Type u) [Field L] [Field Ω]
  [Algebra (V.residueField (genericPoint V)) L] [IsSepClosure (V.residueField (genericPoint V)) L]
  [Algebra L Ω] [Algebra (V.residueField (genericPoint V)) Ω]
  [IsScalarTower (V.residueField (genericPoint V)) L Ω] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic (V.residueField (genericPoint V)) Ω]
  (A : Type u) [CommRing A] [IsDomain A] [Algebra A (V.residueField (genericPoint V))]
  [IsFractionRing A (V.residueField (genericPoint V))] [Algebra A L]
  [IsScalarTower A (V.residueField (genericPoint V)) L] (P : Ideal (integralClosure A L))

/-- The **inertia group of `V` at a missing point**: the image in `π₁(V, η̄)` of the inertia group
`I_P ⊆ Gal(L/K)` of a place `P` of `L` over the discrete valuation ring `A` of the point, under the
canonical homomorphism `Gal(L/K) → π₁(V, η̄)`. -/
def curvePointInertia :
    Subgroup (EtaleFundamentalGroup V ((algebraicClosureGeometricPoint
      (V.residueField (genericPoint V)) Ω).map (V.fromSpecResidueField (genericPoint V)))) :=
  letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
    (integralClosure A L)
  (P.inertia Gal(L / V.residueField (genericPoint V))).map
    (galoisToFundamentalGroup V L Ω).toMonoidHom

/-- The **decomposition group of `V` at a missing point**: the image in `π₁(V, η̄)` of the
decomposition group `D_P ⊆ Gal(L/K)` (the stabilizer of the place `P`) under the canonical
homomorphism `Gal(L/K) → π₁(V, η̄)`. -/
def curvePointDecomposition :
    Subgroup (EtaleFundamentalGroup V ((algebraicClosureGeometricPoint
      (V.residueField (genericPoint V)) Ω).map (V.fromSpecResidueField (genericPoint V)))) :=
  letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
    (integralClosure A L)
  (MulAction.stabilizer Gal(L / V.residueField (genericPoint V)) P).map
    (galoisToFundamentalGroup V L Ω).toMonoidHom

/-- An element of `π₁(V, η̄)` lies in the inertia group at a missing point if and only if it is
the image of an element of the inertia group `I_P ⊆ Gal(L/K)`. -/
theorem mem_curvePointInertia_iff (g : EtaleFundamentalGroup V ((algebraicClosureGeometricPoint
      (V.residueField (genericPoint V)) Ω).map (V.fromSpecResidueField (genericPoint V)))) :
    letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
      (integralClosure A L)
    g ∈ curvePointInertia V L Ω A P ↔
      ∃ σ ∈ P.inertia Gal(L / V.residueField (genericPoint V)),
        galoisToFundamentalGroup V L Ω σ = g :=
  Subgroup.mem_map

/-- An element of `π₁(V, η̄)` lies in the decomposition group at a missing point if and only if
it is the image of an element of the stabilizer `D_P ⊆ Gal(L/K)` of the place `P`. -/
theorem mem_curvePointDecomposition_iff (g : EtaleFundamentalGroup V
      ((algebraicClosureGeometricPoint (V.residueField (genericPoint V)) Ω).map
        (V.fromSpecResidueField (genericPoint V)))) :
    letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
      (integralClosure A L)
    g ∈ curvePointDecomposition V L Ω A P ↔
      ∃ σ ∈ MulAction.stabilizer Gal(L / V.residueField (genericPoint V)) P,
        galoisToFundamentalGroup V L Ω σ = g :=
  Subgroup.mem_map

/-- The inertia group at a missing point lies in its decomposition group. -/
theorem curvePointInertia_le_curvePointDecomposition :
    curvePointInertia V L Ω A P ≤ curvePointDecomposition V L Ω A P := by
  let := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
    (integralClosure A L)
  exact Subgroup.map_mono fun σ hσ => (Ideal.inertia_le_stabilizer P) hσ

/-- The inertia group at a missing point is compact. -/
theorem isCompact_curvePointInertia [IsDiscreteValuationRing A] :
    IsCompact (curvePointInertia V L Ω A P : Set (EtaleFundamentalGroup V
      ((algebraicClosureGeometricPoint (V.residueField (genericPoint V)) Ω).map
        (V.fromSpecResidueField (genericPoint V))))) := by
  let := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
    (integralClosure A L)
  exact (Stacks.EtaleCohomology.isClosed_inertia A (V.residueField (genericPoint V)) L
    P).isCompact.image (galoisToFundamentalGroup V L Ω).continuous

/-- **Grothendieck's local monodromy theorem at a missing point** (Weil II 1.7.1, 1.8): for a
discrete valuation ring `A` with fraction field `K` and finite residue field of cardinality `q`,
a place `P` of `L` over it and a continuous `ρ : π₁(V, η̄) → GL_r(ℤ_ℓ)`, `ℓ` different from the
residue characteristic, the conclusion of
`Stacks.EtaleCohomology.exists_monodromy_logarithm_of_inertia` holds for `ρ ∘ φ`. -/
theorem exists_monodromy_logarithm_of_curvePointInertia [IsDiscreteValuationRing A] [P.IsMaximal]
    [Finite (IsLocalRing.ResidueField A)] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A)) {r : ℕ}
    (ρ : EtaleFundamentalGroup V ((algebraicClosureGeometricPoint
      (V.residueField (genericPoint V)) Ω).map (V.fromSpecResidueField (genericPoint V))) →*
        GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) :
    letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
      (integralClosure A L)
    let ρ' := ρ.comp (galoisToFundamentalGroup V L Ω).toMonoidHom
    let q := Nat.card (IsLocalRing.ResidueField A)
    ∃ T ∈ P.inertia Gal(L / V.residueField (genericPoint V)),
      ρ' T ∈ Stacks.EtaleCohomology.congruenceSubgroup ℓ r 1 ∧
      (∀ σ ∈ P.inertia Gal(L / V.residueField (genericPoint V)),
        ρ' σ ∈ Stacks.EtaleCohomology.congruenceSubgroup ℓ r 1 →
        ∀ v : Fin r → ℤ_[ℓ],
          ((ρ' T : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]).mulVec v = v →
          ((ρ' σ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]).mulVec v = v) ∧
      ∀ Fr ∈ MulAction.stabilizer Gal(L / V.residueField (genericPoint V)) P,
        (∀ b : integralClosure A L, Fr • b - b ^ q ∈ P) →
        let φ : Matrix (Fin r) (Fin r) ℤ_[ℓ] →ₐ[ℤ_[ℓ]] Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]) :=
          (Matrix.toLinAlgEquiv' (R := ℚ_[ℓ]) (n := Fin r)).toAlgHom.restrictScalars ℤ_[ℓ] |>.comp
            (AlgHom.mapMatrix (Algebra.ofId ℤ_[ℓ] ℚ_[ℓ]))
        ∃ m : ℕ, 0 < m ∧ ∃ N : Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]), IsNilpotent N ∧
          N * φ (ρ' Fr⁻¹ : GL (Fin r) ℤ_[ℓ]) =
            (q : ℚ_[ℓ]) • (φ (ρ' Fr⁻¹ : GL (Fin r) ℤ_[ℓ]) * N) ∧
          ∀ v, N v = 0 ↔ (φ (ρ' T : GL (Fin r) ℤ_[ℓ]) ^ m) v = v :=
  Stacks.EtaleCohomology.exists_monodromy_logarithm_of_inertia A (V.residueField (genericPoint V)) L
    P hℓ _ (hρ.comp (galoisToFundamentalGroup V L Ω).continuous)

end Stacks.FundamentalGroup

end
