module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import
  StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications

/-!
# Stacks 02S5 with a carrier

`Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent` is **Stacks 02S5**: for a closed
subscheme `Z ⊆ X ×_S 𝐏¹_S` of relative dimension at most `k + 1` whose two fibres have
delta-dimension at most `k` and whose associated points are in general position with respect to
the two distinguished sections, the cycles `[Z₀]_k` and `[Z_∞]_k` are rationally equivalent.

That statement cannot be summed over a locally finite family of such `Z`: rational equivalence
to zero in the sense of Stacks 02RW carries no information about *where* the witnessing family
of integral closed subschemes lives, and local finiteness of a union of witnessing families
needs it. This file upgrades the conclusion to
`Stacks.Chow.IsRationallyEquivalentToZeroWithin` at the carrier
`Stacks.Chow.fibreCarrier` — the closure of the image of the support of `Z` in `X` — which is
exactly the refinement `Stacks.Chow.rationallyEquivalentToZeroWithin_finsum` consumes.

## Main results

* `Stacks.Chow.fibreDifference_isRationallyEquivalentToZeroWithin` — Stacks 02S5 refined by its
  carrier.
* `Stacks.Chow.fibreDifference_apply_eq_finsum_componentFamily` — the fibre difference of `Z` is
  the locally finite sum of the fibre differences of the components of `Z` of relative dimension
  `k + 1`, repeated with multiplicity.

## Implementation notes

The proof runs the decomposition of the fibre cycles of `Z` over
`Stacks.Chow.componentFamily`, the family of irreducible components of `Z` of relative dimension
`k + 1` repeated with multiplicity, rather than through the existential
`Stacks.Chow.FibreCycleComponentDecompositionRule`: the family has to be *named* to know that
its members live inside `Z`, which is what bounds their carriers by the carrier of `Z`. The two
coefficient identities
`Stacks.Chow.cycleAssociatedToZeroFiber_apply_eq_finsum_componentFamily` and
`Stacks.Chow.cycleAssociatedToInfinityFiber_apply_eq_finsum_componentFamily` hold at the
points of relative dimension `k`; at every other point both sides vanish term by term, since the
cycle of a closed subscheme in degree `k` has no coefficient there.

Each member is integral, so Stacks 02S4 part (2) applies to it in the carrier-refined form
`Stacks.Chow.fibreCyclesRationallyEquivalentWithin`, and the carriers of the members are
contained in the carrier of `Z` because their supports are.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- The fibre difference of a closed subscheme of `X ×_S 𝐏¹_S` vanishes at every point of `X`
whose relative dimension is not `k`: both fibre cycles are `k`-cycles. -/
theorem fibreDifference_apply_eq_zero_of_relativeDimension_ne
    (W : (projectiveLineProduct f).IdealSheafData) {x : X}
    (hx : relativeDimension C.dimensionFunction f x ≠ k) :
    (fibreDifference C f k W).1 x = 0 := by
  change (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k).1 x -
    (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k).1 x = 0
  rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f
      (zeroFiber f W).subschemeι k hx,
    cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f
      (infinityFiber f W).subschemeι k hx, sub_zero]

variable (Z : (projectiveLineProduct f).IdealSheafData)

omit [LocallyOfFiniteType f] in
/-- The support of a member of the family of components of `Z` is contained in the support
of `Z`. -/
theorem coe_support_componentFamily_subset (j : componentIndex C f k Z) :
    ((componentFamily C f k Z j).support : Set (projectiveLineProduct f)) ⊆
      (Z.support : Set (projectiveLineProduct f)) := by
  have hmem : Z.subschemeι j.1.1.1 ∈ (Z.support : Set (projectiveLineProduct f)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨j.1.1.1, rfl⟩
  rw [coe_support_componentFamily]
  exact Z.support.2.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)

omit [LocallyOfFiniteType f] in
/-- The carrier of a member of the family of components of `Z` is contained in the carrier
of `Z`. -/
theorem fibreCarrier_componentFamily_subset (j : componentIndex C f k Z) :
    fibreCarrier C f (componentFamily C f k Z j) ⊆ fibreCarrier C f Z :=
  closure_mono (Set.image_mono (coe_support_componentFamily_subset C f k Z j))

/-- The fibre difference of `Z` is the locally finite sum of the fibre differences of the family
of components of `Z`. -/
theorem fibreDifference_apply_eq_finsum_componentFamily
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    (x : X) :
    (fibreDifference C f k Z).1 x =
      ∑ᶠ j : componentIndex C f k Z, (fibreDifference C f k (componentFamily C f k Z j)).1 x := by
  by_cases hx : relativeDimension C.dimensionFunction f x = k
  · change (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1 x -
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1 x = _
    rw [cycleAssociatedToZeroFiber_apply_eq_finsum_componentFamily C f k Z hZ h₀ hAssociated hx,
      cycleAssociatedToInfinityFiber_apply_eq_finsum_componentFamily C f k Z hZ hInf
        hAssociated hx]
    exact (finsum_sub_distrib
      (hasFiniteSupport_cycleAssociatedToZeroFiber_componentFamily C f k Z x)
      (hasFiniteSupport_cycleAssociatedToInfinityFiber_componentFamily C f k Z x)).symm
  · rw [fibreDifference_apply_eq_zero_of_relativeDimension_ne C f k Z hx,
      show (fun j : componentIndex C f k Z ↦
            (fibreDifference C f k (componentFamily C f k Z j)).1 x) = fun _ ↦ (0 : ℤ) from
        funext fun j ↦ fibreDifference_apply_eq_zero_of_relativeDimension_ne C f k _ hx]
    exact (finsum_zero (M := ℤ) (α := componentIndex C f k Z)).symm

/-- **Stacks 02S5, refined by its carrier.** Under the four hypotheses of Stacks 02S5, the
difference of the cycles of the two fibres of `Z` is rationally equivalent to zero *within* the
carrier of `Z`, the closure in `X` of the image of the support of `Z`.

Forgetting the carrier gives back `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent`; the
carrier is what makes the statement summable over a locally finite family of such `Z`. -/
theorem fibreDifference_isRationallyEquivalentToZeroWithin
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k)) :
    IsRationallyEquivalentToZeroWithin C f k (fibreDifference C f k Z) (fibreCarrier C f Z) :=
  (rationallyEquivalentToZeroWithin_finsum C f k
    (fun j ↦ fibreDifference C f k (componentFamily C f k Z j))
    (fun j ↦ fibreCarrier C f (componentFamily C f k Z j))
    (locallyFinite_fibreCarrier C f (componentFamily C f k Z)
      (locallyFinite_support_componentFamily C f k Z))
    (fun j ↦ fibreCyclesRationallyEquivalentWithin C f k (componentFamily C f k Z j)
      (isIntegral_componentFamily C f k Z j) (relativeDimension_componentFamily C f k Z j)
      (not_range_componentFamily_subset_range_zeroSection C f k Z h₀ j)
      (not_range_componentFamily_subset_range_infinitySection C f k Z hInf j))
    (fibreDifference_apply_eq_finsum_componentFamily C f k Z hZ h₀ hInf
      hAssociated)).mono
    (Set.iUnion_subset (fibreCarrier_componentFamily_subset C f k Z))

end Stacks.Chow

end
