module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeterminantalWeightsFrobenius
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorWeightBoundOpen
public import StacksFrontier.NumberTheory.Padics.LAdicInvariantCharacters

/-!
# Determinantal weights on curves over finite fields

Weil II 1.3 (Kedlaya, *Fourier transforms and p-adic Weil II*, Proposition 6.1.6): on a smooth
curve `X` over a finite field, every irreducible continuous ℓ-adic representation `ρ` of
`π₁(X, x̄)` has a determinantal weight: there are `c > 0` and `r` with
`|ι det ρ(F_y)| ^ c = r ^ (deg y · dim ρ)` at every closed point `y`.

## Main results

* `AlgebraicGeometry.forall_eq_zero_of_isCurve`: on a smooth curve, every Frobenius-invariant
  continuous additive character of an open subgroup of the geometric fundamental group vanishes
  (Weil II 1.3.4).
* `AlgebraicGeometry.exists_geometricFrobeniusFamily_determinantal_weight_of_isCurve`: an
  irreducible continuous ℓ-adic representation of `π₁(X, x̄)` has a determinantal weight.
* `AlgebraicGeometry.exists_geometricFrobeniusFamily_determinantal_weights_of_isCurve`: for a
  semisimple representation, one exponent serves every irreducible constituent.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.3)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.LAdic

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p]
  (hq : Fintype.card k = p ^ n) {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
  [Smooth f] [IsCurve k f] (x : GeometricPoint X)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
  {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] [IsAlgClosed K]
  {m : Type*} [Fintype m] [DecidableEq m]

omit [CharZero K] [CompleteSpace K] [IsAlgClosed K] in
include hℓp in
/-- **Weil II 1.3.4 on a smooth curve**: every continuous additive character of an open subgroup
`H ∩ U` of the geometric fundamental group with values in `K`, invariant under conjugation by
`φ ^ [π₁ : U]`, vanishes. -/
theorem forall_eq_zero_of_isCurve (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hq (x.map f))⁻¹) :
    ∀ U : Subgroup (EtaleFundamentalGroup X x), U.Normal →
      IsOpen (U : Set (EtaleFundamentalGroup X x)) →
      ∀ ψ : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U) → K,
        (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U),
          (b : EtaleFundamentalGroup X x) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) →
        ψ = 0 :=
  Stacks.LAdic.forall_eq_zero_of_forall_encard_invariant_zmod_le (ℓ := ℓ) _
    (isClosed_ker_etaleFundamentalGroupMap f x) φ
    (exists_forall_encard_invariant_zmod_le p n hq f x φ hφ (Fact.out : ℓ.Prime) hℓp)

include hℓp in
/-- **Determinantal weight of an irreducible ℓ-adic representation of a curve** (Weil II 1.3):
for a smooth curve `X` over a finite field, a lift `φ` of the geometric Frobenius and an
irreducible continuous `ρ : π₁(X, x̄) → GL_m(K)`, there are `c > 0` and `r` with
`‖ι det ρ(F_y)‖ ^ c = r ^ (deg y · m)` at every closed point `y`. -/
theorem exists_geometricFrobeniusFamily_determinantal_weight_of_isCurve (ι : K →+* ℂ)
    (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hq (x.map f))⁻¹)
    (ρ : EtaleFundamentalGroup X x →* (Matrix m m K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix m m K))
    (hirr : ∀ W : Submodule K (m → K), (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∃ r : ℝ, ∀ y : closedPoints X,
      ‖ι (ρ (Stacks.EtaleCohomology.geometricFrobeniusFamily f x y) : Matrix m m K).det‖ ^ c =
        r ^ (Stacks.EtaleCohomology.residueDegree f y.1 * Fintype.card m) :=
  exists_geometricFrobeniusFamily_determinantal_weight_of_irreducible p n hq f x ℓ ι φ hφ ρ hρ
    (forall_eq_zero_of_isCurve p n hq f x ℓ hℓp φ hφ) hirr

include hℓp in
/-- **Determinantal weights of a semisimple ℓ-adic representation of a curve** (Weil II 1.3):
one exponent `c > 0` serves every irreducible constituent `W`, each with its own `r`. -/
theorem exists_geometricFrobeniusFamily_determinantal_weights_of_isCurve (ι : K →+* ℂ)
    (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hq (x.map f))⁻¹)
    (ρ : EtaleFundamentalGroup X x →* (Matrix m m K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix m m K))
    (hss : ∀ W : Submodule K (m → K), (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (m → K), IsCompl W W' ∧
        ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W') :
    ∃ c : ℕ, 0 < c ∧
      ∀ W : Submodule K (m → K), ∀ hW : (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W),
        (∀ W' ≤ W, W' ≠ ⊥ → (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W') →
          W' = W) →
        ∃ r : ℝ, ∀ y : closedPoints X,
          ‖ι (detCharacter ρ hW (Stacks.EtaleCohomology.geometricFrobeniusFamily f x y))‖ ^ c =
            r ^ (Stacks.EtaleCohomology.residueDegree f y.1 * Module.finrank K W) :=
  exists_geometricFrobeniusFamily_determinantal_weights p n hq f x ℓ ι φ hφ ρ hρ
    (forall_eq_zero_of_isCurve p n hq f x ℓ hℓp φ hφ) hss

end AlgebraicGeometry

end
