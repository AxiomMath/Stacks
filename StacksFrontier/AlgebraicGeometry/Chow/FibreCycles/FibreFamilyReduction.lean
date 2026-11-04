module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreComparison
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.LocallyFiniteImage
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity

/-!
# The family form of Stacks 02S4 part (3) from its one-member case

Stacks Tag 02S4 part (3) says that for a locally finite family of integral closed subschemes of
`X ×_S 𝐏¹_S`, each of relative dimension `k + 1` and contained in neither distinguished section,
the coefficientwise difference of the cycles of the zero and infinity fibres is a `k`-cycle
rationally equivalent to zero; it is stated here as
`Stacks.Chow.FamilyFibreDifferencesRationallyEquivalentToZero`.

This file shows that it follows from the statement for one subscheme refined by a carrier: the
difference of the two fibre cycles of a single integral `W` is rationally equivalent to zero
within the closure of the image of the support of `W` in `X`. The carriers of a locally finite
family form a locally finite family of subsets of `X` (Tag 02R2), and the coefficientwise sum of
the fibre differences of the family is a `k`-cycle.

## Main definitions

* `Stacks.Chow.fibreDifference` — the difference of the two fibre cycles of one subscheme, as a
  `k`-cycle.
* `Stacks.Chow.fibreCarrier` — its carrier, the closure of the image of the support in `X`.
* `Stacks.Chow.FibreCyclesRationallyEquivalentWithin` — Tag 02S4 part (2) refined by that
  carrier.

## Main results

* `Stacks.Chow.support_fibreDifference_subset` — the fibre difference is supported in the
  carrier.
* `Stacks.Chow.locallyFinite_fibreCarrier` — the carriers of a locally finite family are locally
  finite.
* `Stacks.Chow.exists_familyFibreDifferenceSum` — the family difference coefficient is the
  coefficient function of a `k`-cycle.
* `Stacks.Chow.familyFibreDifferencesRationallyEquivalentToZero_of_within` — the one-member
  statement implies Tag 02S4 part (3).
* `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent_of_within_of_decompositionRule` —
  Tag 02S5 follows from the one-member statement together with the decomposition rule.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02R2](https://stacks.math.columbia.edu/tag/02R2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-! ### One member of the family -/

/-- The difference of the cycles of the two fibres of a closed subscheme of `X ×_S 𝐏¹_S`, as a
`k`-cycle on `X`. -/
def fibreDifference (W : (projectiveLineProduct f).IdealSheafData) : CycleGroup C f k :=
  cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k -
    cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k

/-- The carrier of the fibre difference of `W`: the closure in `X` of the image of the support
of `W` under the projection `X ×_S 𝐏¹_S ⟶ X`. -/
def fibreCarrier (W : (projectiveLineProduct f).IdealSheafData) : Set X :=
  closure ((pullback.fst f (relativeProjectiveLine C.S ↘ C.S)).base ''
    (W.support : Set (projectiveLineProduct f)))

/-- The support of the fibre difference of `W` is contained in the carrier of `W`. -/
theorem support_fibreDifference_subset (W : (projectiveLineProduct f).IdealSheafData) :
    Function.support (fibreDifference C f k W).1 ⊆ fibreCarrier C f W := by
  intro x hx
  have hmem : x ∈ ((zeroFiber f W).support : Set X) ∪ ((infinityFiber f W).support : Set X) := by
    by_contra h
    rw [Set.mem_union, not_or] at h
    obtain ⟨h0, hinf⟩ := h
    rw [← Scheme.IdealSheafData.range_subschemeι] at h0 hinf
    refine hx ?_
    show (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k).1 x -
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k).1 x = 0
    rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f
        (zeroFiber f W).subschemeι k h0,
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f
        (infinityFiber f W).subschemeι k hinf, sub_zero]
  refine subset_closure ?_
  rcases hmem with h | h
  · rw [coe_support_zeroFiber] at h
    exact ⟨zeroSection f x, h, fst_constantSection_apply f _ x⟩
  · rw [coe_support_infinityFiber] at h
    exact ⟨infinitySection f x, h, fst_constantSection_apply f _ x⟩

omit [LocallyOfFiniteType f] in
/-- The carriers of a locally finite family of closed subschemes of `X ×_S 𝐏¹_S` form a locally
finite family of subsets of `X`. -/
theorem locallyFinite_fibreCarrier {J : Type u}
    (W : J → (projectiveLineProduct f).IdealSheafData)
    (hLoc : LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f)))) :
    LocallyFinite (fun j ↦ fibreCarrier C f (W j)) :=
  locallyFinite_closure_image_of_isSpectralMap
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S)).base
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S)).isSpectralMap _ hLoc

/-! ### The family sum is a cycle -/

/-- The family difference coefficient of a locally finite family of closed subschemes of
`X ×_S 𝐏¹_S` is the coefficient function of a `k`-cycle on `X`. -/
theorem exists_familyFibreDifferenceSum {J : Type u}
    (W : J → (projectiveLineProduct f).IdealSheafData)
    (hLoc : LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f)))) :
    ∃ α : CycleGroup C f k,
      ∀ x : X, α.1 x = familyFibreDifferenceCoefficient C f k W x := by
  have hloc := locallyFiniteSupport_finsum_of_locallyFinite
    (fun j ↦ fibreCarrier C f (W j)) (locallyFinite_fibreCarrier C f W hLoc)
    (fun j x ↦ (fibreDifference C f k (W j)).1 x)
    (fun j ↦ support_fibreDifference_subset C f k (W j))
    (fun j ↦ (fibreDifference C f k (W j)).1.locallyFiniteSupport)
  refine ⟨⟨⟨familyFibreDifferenceCoefficient C f k W, by simp, fun z _ ↦ hloc z⟩, ?_⟩,
    fun x ↦ rfl⟩
  intro Z hZ
  obtain ⟨j, hj⟩ : ∃ j, (fibreDifference C f k (W j)).1 Z.isIrreducible.genericPoint ≠ 0 := by
    by_contra! h
    exact hZ ((finsum_congr h).trans finsum_zero)
  exact (mem_cyclesOfDimension C f k _).1 (fibreDifference C f k (W j)).2 Z hj

/-! ### The one-member obligation -/

/-- For every integral closed subscheme `W ⊆ X ×_S 𝐏¹_S` of relative dimension `k + 1` contained
in neither distinguished section, the difference of the cycles of its two fibres is rationally
equivalent to zero within `Stacks.Chow.fibreCarrier`: Stacks Tag 02S4 part (2), refined by a
carrier. -/
def FibreCyclesRationallyEquivalentWithin : Prop :=
  ∀ W : (projectiveLineProduct f).IdealSheafData, IsIntegral W.subscheme →
    (∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1) →
    ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f) →
    ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f) →
    IsRationallyEquivalentToZeroWithin C f k (fibreDifference C f k W) (fibreCarrier C f W)

/-- `Stacks.Chow.FibreCyclesRationallyEquivalentWithin` implies
`Stacks.Chow.FamilyFibreDifferencesRationallyEquivalentToZero`. -/
theorem familyFibreDifferencesRationallyEquivalentToZero_of_within
    (h : FibreCyclesRationallyEquivalentWithin C f k) :
    FamilyFibreDifferencesRationallyEquivalentToZero C f k := by
  intro J W hInt hDim h₀ hInf hLoc
  obtain ⟨α, hα⟩ := exists_familyFibreDifferenceSum C f k W hLoc
  exact ⟨α, rationallyEquivalentToZero_finsum C f k (fun j ↦ fibreDifference C f k (W j))
    (fun j ↦ fibreCarrier C f (W j)) (locallyFinite_fibreCarrier C f W hLoc)
    (fun j ↦ h (W j) (hInt j) (hDim j) (h₀ j) (hInf j)) hα, hα⟩

/-- Under the hypotheses of Stacks Tag 02S5 on `Z`, the cycles of the zero and infinity fibres of
`Z` are rationally equivalent, given `Stacks.Chow.FibreCyclesRationallyEquivalentWithin` and
`Stacks.Chow.FibreCycleComponentDecompositionRule`. -/
theorem cycleAssociatedToFibres_rationallyEquivalent_of_within_of_decompositionRule
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
    (hwithin : FibreCyclesRationallyEquivalentWithin C f k)
    (hrule : FibreCycleComponentDecompositionRule C f k) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k) :=
  cycleAssociatedToFibres_rationallyEquivalent_of_decompositionRule C f k Z hZ h₀ hInf
    hAssociated (familyFibreDifferencesRationallyEquivalentToZero_of_within C f k hwithin) hrule

end Stacks.Chow

end
