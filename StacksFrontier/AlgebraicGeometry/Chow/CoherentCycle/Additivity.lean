module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity

/-!
# Additivity of the cycle of a coherent sheaf

Let `0 → F → G → H → 0` be a short exact sequence of coherent sheaves on a scheme `X` locally of
finite type over the base scheme of chapter 42 of the Stacks Project, and suppose all three
supports have delta-dimension at most `k`. Then `[G]_k = [F]_k + [H]_k`.

The stalk functor is exact, so at each point the three stalks form a short exact sequence of
modules over the local ring; the length of the middle term is the sum of the lengths of the
outer two, and at a point of delta-dimension `k` those outer lengths are finite, so the
multiplicities add as integers.

## Main results

* `Stacks.Chow.cycleAssociatedToCoherentSheaf_add` — Stacks 02QZ.

## Implementation notes

The short exact sequence of stalk modules is
`Stacks.SheafOfModules.FlatShortExact.stalkShortExact`, whose module structure on the stalk is
Mathlib's and therefore the one `Stacks.Chow.sheafMultiplicity` is computed with. Additivity of
length is `Module.length_eq_add_of_exact`, valued in `ℕ∞`; `ENat.toNat` is additive only on
finite values, which is what the delta-dimension bound supplies at the relevant points.

## References

* [Stacks Project, Tag 00IV](https://stacks.math.columbia.edu/tag/00IV)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 02QZ](https://stacks.math.columbia.edu/tag/02QZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **Stacks 02QZ.** The cycle of a coherent sheaf is additive along a short exact sequence of
coherent sheaves whose supports all have delta-dimension at most `k`. -/
@[stacks 02QZ]
theorem cycleAssociatedToCoherentSheaf_add (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (E : ShortComplex X.Modules) (hE : E.ShortExact)
    [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent] (k : ℤ)
    (hk₁ : schemeDeltaDimension C ((reducedSupport E.X₁).subschemeι ≫ f) ≤ (k : EInt))
    (hk₂ : schemeDeltaDimension C ((reducedSupport E.X₂).subschemeι ≫ f) ≤ (k : EInt))
    (hk₃ : schemeDeltaDimension C ((reducedSupport E.X₃).subschemeι ≫ f) ≤ (k : EInt)) :
    cycleAssociatedToCoherentSheaf C f E.X₂ k hk₂ =
      cycleAssociatedToCoherentSheaf C f E.X₁ k hk₁ +
        cycleAssociatedToCoherentSheaf C f E.X₃ k hk₃ := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (cycleAssociatedToCoherentSheaf C f E.X₂ k hk₂).1 x =
    (cycleAssociatedToCoherentSheaf C f E.X₁ k hk₁).1 x +
      (cycleAssociatedToCoherentSheaf C f E.X₃ k hk₃).1 x
  by_cases hδ : relativeDimension C.dimensionFunction f x = k
  · simp only [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq _ _ _ _ _ hδ]
    obtain ⟨α, β, hinj, hex, hsurj⟩ :
        ∃ (α : E.X₁.presheaf.stalk x →ₗ[X.presheaf.stalk x] E.X₂.presheaf.stalk x)
          (β : E.X₂.presheaf.stalk x →ₗ[X.presheaf.stalk x] E.X₃.presheaf.stalk x),
          Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β :=
      SheafOfModules.FlatShortExact.stalkShortExact E hE x
    have hlen := Module.length_eq_add_of_exact α β hinj hsurj hex
    have htop₁ := Module.length_ne_top_iff.mpr
      (isFiniteLength_stalk_of_relativeDimension_eq C f E.X₁ hk₁ hδ)
    have htop₃ := Module.length_ne_top_iff.mpr
      (isFiniteLength_stalk_of_relativeDimension_eq C f E.X₃ hk₃ hδ)
    simp only [sheafMultiplicity]
    rw [hlen, ENat.toNat_add htop₁ htop₃]
    push_cast
    rfl
  · simp only [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne _ _ _ _ _ hδ, add_zero]

end Stacks.Chow
