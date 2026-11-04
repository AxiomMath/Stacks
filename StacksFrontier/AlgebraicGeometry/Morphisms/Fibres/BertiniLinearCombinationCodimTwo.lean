module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Bertini
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniAlgebraicIndependence

/-!
# Geometric irreducibility of a general linear combination over a codimension-two intersection

Let `A` be a domain of finite type over a field `k` with fraction field `K`, let `n ≥ 2` and let
`g₁, …, gₙ ∈ A`. Let `Ω = K(x₁, …, xₙ)` be a purely transcendental extension of `K` in `n`
variables and put `ξ = ∑ gᵢxᵢ ∈ Ω`. If `K` is geometrically irreducible over `k` and the common
zero locus `V(g₁, g₂)` has an irreducible component of codimension two in `Spec A`, then `Ω` is
geometrically irreducible over the subfield `k(x₁, …, xₙ, ξ)`.

## Main results

* `Algebra.fg_top_intermediateField_of_finiteType`: the fraction field of an algebra of finite
  type over a field is a finitely generated field extension.
* `Algebra.algebraicIndependent_linearCombination_of_codimTwo`: the variables together with
  `ξ = ∑ gᵢxᵢ` are algebraically independent over `k`.
* `Algebra.isGeometricallyIrreducible_adjoin_linearCombination_of_codimTwo`: the geometric
  irreducibility assertion.

## References

* [Stacks Project, Tag 0G4D](https://stacks.math.columbia.edu/tag/0G4D)
* [Stacks Project, Tag 0G4E](https://stacks.math.columbia.edu/tag/0G4E)
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Jou, Theorem 6.3, part 4]
-/

@[expose] public section

universe u

namespace Algebra

/-- **The fraction field of an algebra of finite type is a finitely generated field extension.**
If `A` is a `k`-algebra of finite type with fraction field `K`, then `K` is generated over `k` by
finitely many elements as a field. -/
theorem fg_top_intermediateField_of_finiteType (k A K : Type u) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra k K] [IsScalarTower k A K] :
    (⊤ : IntermediateField k K).FG := by
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  refine IntermediateField.fg_def.mpr
    ⟨algebraMap A K '' (↑t : Set A), t.finite_toSet.image _, ?_⟩
  have hrange : (IsScalarTower.toAlgHom k A K).range =
      Algebra.adjoin k (algebraMap A K '' (↑t : Set A)) := by
    rw [show (algebraMap A K '' (↑t : Set A)) = (IsScalarTower.toAlgHom k A K) '' ↑t from rfl,
      Algebra.adjoin_image, ht, Algebra.map_top]
  exact (IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (g := IsScalarTower.toAlgHom k A K) (f := AlgHom.id k K) (by ext; simp) hrange).symm.trans
    (AlgHom.fieldRange_eq_top.mpr fun y ↦ ⟨y, rfl⟩)

section LinearCombination

variable (k A K Ω : Type u) [Field k] [CommRing A] [Algebra k A] [Field K] [Algebra A K]
  [Algebra k K] [IsScalarTower k A K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-- The `k`-algebra map `A[x₁, …, xₙ] → Ω` evaluating the variables at a family `x` of elements
of `Ω` and the constants along `A → K → Ω`. It is the base change `A[x₁, …, xₙ] → K[x₁, …, xₙ]`
followed by evaluation at `x`. -/
private noncomputable def mvPolynomialEval {n : ℕ} (x : Fin n → Ω) :
    MvPolynomial (Fin n) A →ₐ[k] Ω :=
  ((MvPolynomial.aeval x : MvPolynomial (Fin n) K →ₐ[K] Ω).restrictScalars k).comp
    (MvPolynomial.mapAlgHom (IsScalarTower.toAlgHom k A K))

/-- `mvPolynomialEval` is evaluation at `x` of the base change of a polynomial to `K`. -/
private theorem mvPolynomialEval_apply {n : ℕ} (x : Fin n → Ω) (p : MvPolynomial (Fin n) A) :
    mvPolynomialEval k A K Ω x p =
      MvPolynomial.aeval x (MvPolynomial.map (algebraMap A K) p) := rfl

/-- `mvPolynomialEval` is injective when `x` is algebraically independent over `K`. -/
private theorem mvPolynomialEval_injective [IsFractionRing A K] {n : ℕ} {x : Fin n → Ω}
    (hx : AlgebraicIndependent K x) :
    Function.Injective (mvPolynomialEval k A K Ω x) := by
  intro p q hpq
  rw [mvPolynomialEval_apply, mvPolynomialEval_apply] at hpq
  exact MvPolynomial.map_injective _ (IsFractionRing.injective A K) (hx hpq)

/-- **The variables and their linear combination are algebraically independent over the base
field.** Let `A` be a domain of finite type over `k`, `n ≥ 2` and `g : Fin n → A` such that
`V(g₁, g₂)` has an irreducible component of codimension two in `Spec A`. Then the `n + 1` elements
`x₁, …, xₙ` and `ξ = ∑ gᵢxᵢ` of `Ω` are algebraically independent over `k`. -/
@[stacks 0G4E "the variables and their linear combination, read in the ambient field"]
theorem algebraicIndependent_linearCombination_of_codimTwo
    [IsDomain A] [Algebra.FiniteType k A] [IsFractionRing A K]
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → Ω) (hx : AlgebraicIndependent K x) (g : Fin n → A)
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {g ⟨0, by omega⟩, g ⟨1, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    AlgebraicIndependent k
      (Sum.elim x fun _ : Unit => ∑ i, algebraMap K Ω (algebraMap A K (g i)) * x i) := by
  obtain ⟨c, hc⟩ := Algebra.exists_algebraicIndependent_linearCombinations k A hn g hcodim
  have he : Function.Injective
      (Sum.map (_root_.id : Fin n → Fin n) fun _ : Unit => (0 : Fin 2)) :=
    Function.Injective.sumMap Function.injective_id fun a b _ ↦ Subsingleton.elim a b
  convert (hc.map' (mvPolynomialEval_injective k A K Ω hx)).comp _ he using 1
  funext s
  rcases s with i | _ <;> simp [mvPolynomialEval_apply]

/-- **Geometric irreducibility of `K(x₁, …, xₙ)` over `k(x₁, …, xₙ, ∑ gᵢxᵢ)`.** Let `A` be a
domain of finite type over `k` with fraction field `K`, let `n ≥ 2` and let `g : Fin n → A` be
such that the common zero locus of `g₁` and `g₂` has an irreducible component of codimension two
in `Spec A`. Let `Ω` be generated over `K` by the algebraically independent family `x₁, …, xₙ`.
If `K` is geometrically irreducible over `k`, then `Ω` is geometrically irreducible over the
subfield of `Ω` generated over `k` by the variables and by `ξ = ∑ gᵢxᵢ`. -/
theorem isGeometricallyIrreducible_adjoin_linearCombination_of_codimTwo
    [IsDomain A] [Algebra.FiniteType k A] [IsFractionRing A K]
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → Ω)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hx : AlgebraicIndependent K x)
    (hK : Algebra.IsGeometricallyIrreducible k K) (g : Fin n → A)
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {g ⟨0, by omega⟩, g ⟨1, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    let ξ : Ω := ∑ i, algebraMap K Ω (algebraMap A K (g i)) * x i
    let F : IntermediateField k Ω :=
      IntermediateField.adjoin k (Set.range x ∪ {ξ})
    letI : Algebra F Ω := F.toSubalgebra.toAlgebra
    Algebra.IsGeometricallyIrreducible F Ω := by
  obtain ⟨c, hc⟩ := Algebra.exists_algebraicIndependent_linearCombinations k A hn g hcodim
  have he : Function.Injective
      (Sum.map (_root_.id : Fin n → Fin n) (fun b : Bool => if b then (1 : Fin 2) else 0)) :=
    Function.Injective.sumMap Function.injective_id (by decide)
  refine isGeometricallyIrreducible_adjoin_linearCombination k K Ω n (by omega) x
    (fun i ↦ algebraMap A K (g i)) hgen hx hK
    (fg_top_intermediateField_of_finiteType k A K) c ?_
  convert (hc.map' (mvPolynomialEval_injective k A K Ω hx)).comp _ he using 1
  funext s
  rcases s with i | _ | _ <;> simp [mvPolynomialEval_apply, IsScalarTower.algebraMap_apply k A K]

end LinearCombination

end Algebra

end
