module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CycleCoefficientSupport
public import StacksFrontier.AlgebraicGeometry.Chow.Sweep.FamilyFibreDifference
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints

/-!
# Rational equivalence of the two fibre cycles of a family over the projective line

Let `f : X ⟶ S` and let `Z ⊆ X ×_S 𝐏¹_S` be a closed subscheme, with zero and infinity fibres
`Z₀` and `Z_∞` read as closed subschemes of `X`. Stacks Tag 02S5 asserts that `[Z₀]_k` and
`[Z_∞]_k` are rationally equivalent as `k`-cycles on `X`, under a bound on the delta-dimension
of `Z` and of the two fibres and a condition on the associated points of `Z`.

This file derives that conclusion from two statements. One is Tag 02S4 part (3): the fibre
differences of a locally finite family of integral closed subschemes of relative dimension
`k + 1`, each contained in neither distinguished section, sum to a `k`-cycle rationally
equivalent to zero. The other is the decomposition of the fibre cycles of `Z` over such a family:
writing `[Z]_{k+1} = ∑ nᵢ [Wᵢ]` over the irreducible components of `Z` of delta-dimension
`k + 1`, one has `[Z₀]_k = ∑ nᵢ [(Wᵢ)₀]_k`, and likewise at infinity. The decomposition holds
when `Z` is itself integral of relative dimension `k + 1` and contained in neither distinguished
section, so Tag 02S5 for such a `Z` follows from Tag 02S4 part (3) alone.

## Main definitions

* `Stacks.Chow.FamilyFibreDifferencesRationallyEquivalentToZero` — Tag 02S4 part (3).
* `Stacks.Chow.FibreCycleComponentDecomposition` — the claim in the proof of Tag 02S5, for a
  single closed subscheme.
* `Stacks.Chow.FibreCycleComponentDecompositionRule` — the claim as an implication from the
  hypotheses of Tag 02S5.

## Main results

* `Stacks.Chow.fibreCycleComponentDecomposition_of_isIntegral` — the decomposition holds for an
  integral `Z` of relative dimension `k + 1` meeting neither section in its whole range.
* `Stacks.Chow.fibreCycleComponentDecomposition_of_apply_of_relativeDimension_eq` — the
  decomposition only has to be checked at points of relative dimension `k`.
* `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent_of_decomposition` — the two fibre
  cycles of `Z` are rationally equivalent, given Tag 02S4 part (3) and the decomposition.
* `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent_of_isIntegral` — Tag 02S5 for an
  integral `Z`, from Tag 02S4 part (3) alone.
* `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent_of_decompositionRule` — Tag 02S5
  with all four of its hypotheses, from Tag 02S4 part (3) and the decomposition rule.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-! ### The two inputs -/

/-- Stacks Tag 02S4 part (3): for a locally finite family of integral closed subschemes of
`X ×_S 𝐏¹_S`, each of relative dimension `k + 1` at its generic points and contained in neither
distinguished section, the coefficientwise difference of the cycles of the zero and infinity
fibres is a `k`-cycle rationally equivalent to zero. -/
def FamilyFibreDifferencesRationallyEquivalentToZero : Prop :=
  ∀ {J : Type u} (W : J → (projectiveLineProduct f).IdealSheafData),
    (∀ j, IsIntegral (W j).subscheme) →
    (∀ j, ∀ ξ : genericPoints (W j).subscheme,
      relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1) →
    (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f)) →
    (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) →
    LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))) →
    ∃ α : CycleGroup C f k, IsRationallyEquivalentToZero C f k α ∧
      ∀ x : X, α.1 x = familyFibreDifferenceCoefficient C f k W x

/-- The claim in the proof of Stacks Tag 02S5: the difference of the cycles of the two fibres of
`Z` is, coefficientwise, the difference of the cycles of the two fibres of a locally finite
family of integral closed subschemes of relative dimension `k + 1`, each contained in neither
distinguished section. -/
def FibreCycleComponentDecomposition (Z : (projectiveLineProduct f).IdealSheafData) : Prop :=
  ∃ (J : Type u) (W : J → (projectiveLineProduct f).IdealSheafData),
    (∀ j, IsIntegral (W j).subscheme) ∧
    (∀ j, ∀ ξ : genericPoints (W j).subscheme,
      relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1) ∧
    (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f)) ∧
    (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) ∧
    LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))) ∧
    ∀ x : X,
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1 x -
          (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1 x =
        familyFibreDifferenceCoefficient C f k W x

/-- The claim in the proof of Stacks Tag 02S5, as an implication from that tag's hypotheses: for
every closed subscheme of `X ×_S 𝐏¹_S` whose relative dimension is at most `k + 1`, whose two
fibres have delta-dimension at most `k`, and each of whose associated points either misses both
distinguished sections or has relative dimension below `k`, the fibre cycles decompose over a
family of integral closed subschemes. -/
def FibreCycleComponentDecompositionRule : Prop :=
  ∀ Z : (projectiveLineProduct f).IdealSheafData,
    (∀ ξ : Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ξ ≤ k + 1) →
    schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt) →
    schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt) →
    (∀ ξ : Z.subscheme, ξ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ξ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ξ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ξ < k)) →
    FibreCycleComponentDecomposition C f k Z

/-! ### The decomposition is not vacuous -/

/-- An integral closed subscheme of `X ×_S 𝐏¹_S` of relative dimension `k + 1` which is
contained in neither distinguished section decomposes over the one-member family. -/
theorem fibreCycleComponentDecomposition_of_isIntegral
    (Z : (projectiveLineProduct f).IdealSheafData) (hZ : IsIntegral Z.subscheme)
    (hDim : ∀ ξ : genericPoints Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ξ.1 = k + 1)
    (h₀ : ¬ Set.range Z.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range Z.subschemeι ⊆ Set.range (infinitySection f)) :
    FibreCycleComponentDecomposition C f k Z := by
  refine ⟨PUnit.{u + 1}, fun _ ↦ Z, fun _ ↦ hZ, fun _ ↦ hDim, fun _ ↦ h₀, fun _ ↦ hInf,
    fun x ↦ ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩, fun x ↦ ?_⟩
  rw [familyFibreDifferenceCoefficient, finsum_unique]

/-- The two fibre cycles of `Z` have the same coefficient at a point of relative dimension
different from `k`. -/
private theorem fibre_cycles_sub_apply_eq_zero_of_relativeDimension_ne
    (Z : (projectiveLineProduct f).IdealSheafData) {x : X}
    (hx : relativeDimension C.dimensionFunction f x ≠ k) :
    (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1 x -
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1 x = 0 := by
  rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f
      (zeroFiber f Z).subschemeι k hx,
    cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f
      (infinityFiber f Z).subschemeι k hx, sub_zero]

/-- The decomposition of the fibre cycles of `Z` over a family holds as soon as the
coefficientwise identity holds at every point of `X` of relative dimension `k`. -/
theorem fibreCycleComponentDecomposition_of_apply_of_relativeDimension_eq
    (Z : (projectiveLineProduct f).IdealSheafData)
    {J : Type u} (W : J → (projectiveLineProduct f).IdealSheafData)
    (hInt : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, ∀ ξ : genericPoints (W j).subscheme,
      relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1)
    (h₀ : ∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f))
    (hLoc : LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))))
    (hpt : ∀ x : X, relativeDimension C.dimensionFunction f x = k →
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1 x -
          (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1 x =
        familyFibreDifferenceCoefficient C f k W x) :
    FibreCycleComponentDecomposition C f k Z := by
  refine ⟨J, W, hInt, hDim, h₀, hInf, hLoc, fun x ↦ ?_⟩
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · exact hpt x hx
  · rw [fibre_cycles_sub_apply_eq_zero_of_relativeDimension_ne C f k Z hx,
      familyFibreDifferenceCoefficient]
    exact ((finsum_congr fun j ↦
      fibre_cycles_sub_apply_eq_zero_of_relativeDimension_ne C f k (W j) hx).trans
        (finsum_zero (M := ℤ) (α := J))).symm

/-! ### Tag 02S5 from its two inputs -/

/-- Given Stacks Tag 02S4 part (3) and the decomposition of the fibre cycles of `Z` over a family
of integral closed subschemes, the cycles of the zero and infinity fibres of `Z` are rationally
equivalent. -/
theorem cycleAssociatedToFibres_rationallyEquivalent_of_decomposition
    (Z : (projectiveLineProduct f).IdealSheafData)
    (h02S4 : FamilyFibreDifferencesRationallyEquivalentToZero C f k)
    (hdec : FibreCycleComponentDecomposition C f k Z) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k) := by
  obtain ⟨J, W, hInt, hDim, h₀, hInf, hLoc, hcoeff⟩ := hdec
  obtain ⟨α, hα, hαcoeff⟩ := h02S4 W hInt hDim h₀ hInf hLoc
  have heq : cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k -
      cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k = α :=
    Subtype.ext (DFunLike.ext _ _ fun x ↦ (hcoeff x).trans (hαcoeff x).symm)
  rwa [RationallyEquivalent, heq]

/-- Given Stacks Tag 02S4 part (3), for an integral closed subscheme `Z ⊆ X ×_S 𝐏¹_S` of
relative dimension `k + 1` contained in neither distinguished section, the cycles of its two fibres
are rationally equivalent. -/
theorem cycleAssociatedToFibres_rationallyEquivalent_of_isIntegral
    (Z : (projectiveLineProduct f).IdealSheafData) (hZ : IsIntegral Z.subscheme)
    (hDim : ∀ ξ : genericPoints Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ξ.1 = k + 1)
    (h₀ : ¬ Set.range Z.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range Z.subschemeι ⊆ Set.range (infinitySection f))
    (h02S4 : FamilyFibreDifferencesRationallyEquivalentToZero C f k) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k) :=
  cycleAssociatedToFibres_rationallyEquivalent_of_decomposition C f k Z h02S4
    (fibreCycleComponentDecomposition_of_isIntegral C f k Z hZ hDim h₀ hInf)

/-- Under the hypotheses of Stacks Tag 02S5 on `Z`, the cycles of the zero and infinity fibres of
`Z` are rationally equivalent, given
`Stacks.Chow.FamilyFibreDifferencesRationallyEquivalentToZero` and
`Stacks.Chow.FibreCycleComponentDecompositionRule`. -/
theorem cycleAssociatedToFibres_rationallyEquivalent_of_decompositionRule
    (Z : (projectiveLineProduct f).IdealSheafData)
    (hZ : ∀ ξ : Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ξ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ξ : Z.subscheme,
      ξ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ξ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ξ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ξ < k))
    (h02S4 : FamilyFibreDifferencesRationallyEquivalentToZero C f k)
    (hrule : FibreCycleComponentDecompositionRule C f k) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k) :=
  cycleAssociatedToFibres_rationallyEquivalent_of_decomposition C f k Z h02S4
    (hrule Z hZ h₀ hInf hAssociated)

end Stacks.Chow

end
