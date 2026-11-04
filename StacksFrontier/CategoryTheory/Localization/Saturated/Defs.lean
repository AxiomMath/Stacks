module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksCore.Tactic.StacksAttribute

/-!
# Saturated multiplicative systems

Let `C` be a category. A *multiplicative system* `S` of morphisms of `C` is one satisfying
MS1 (identities, closure under composition), MS2 (the two Ore conditions) and MS3 (the two
cancellation conditions); it is **saturated** when it satisfies in addition

* MS4: for three composable morphisms `f`, `g`, `h`, if `f ≫ g ∈ S` and `g ≫ h ∈ S` then
  `g ∈ S`.

Composition is written diagrammatically, so `fg ∈ S` is `W (f ≫ g)`.

In Mathlib a multiplicative system is a `W : MorphismProperty C` satisfying **both**
`W.HasLeftCalculusOfFractions` and `W.HasRightCalculusOfFractions`: each of those classes
extends `W.IsMultiplicative` (MS1) and adds one Ore condition together with one
cancellation condition, so the two of them together are exactly MS1 + MS2 + MS3. In
particular `W.IsMultiplicative` alone is *not* a multiplicative system — it is only MS1 —
which is why `IsSaturated` below bundles the two calculi rather than `IsMultiplicative`.

The weaker conjunction "MS1 and MS4" is `MorphismProperty.IsSaturatedMultiplicative`.

## Main definitions

* `CategoryTheory.MorphismProperty.IsSaturated`: saturated multiplicative systems.

## References

* [Stacks, Tag 05Q8](https://stacks.math.columbia.edu/tag/05Q8)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C]

/-- `W` is a *saturated multiplicative system* when it is a multiplicative system — MS1 together
with the two Ore conditions MS2 and the two cancellation conditions MS3, i.e. both a left and a
right calculus of fractions — and satisfies MS4: for composable `f : X ⟶ Y`, `g : Y ⟶ Z`,
`h : Z ⟶ T`, if `W (f ≫ g)` and `W (g ≫ h)` then `W g`. -/
@[stacks_fixed 05Q8]
structure IsSaturated (W : MorphismProperty C) : Prop where
  /-- MS1 together with the left halves of MS2 and MS3. -/
  hasLeftCalculusOfFractions : W.HasLeftCalculusOfFractions
  /-- MS1 together with the right halves of MS2 and MS3. -/
  hasRightCalculusOfFractions : W.HasRightCalculusOfFractions
  /-- MS4: a morphism is in `W` as soon as it becomes so after composing on either side. -/
  mem_of_comp_mem_comp : ∀ {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    W (f ≫ g) → W (g ≫ h) → W g

/-- A saturated multiplicative system is multiplicative (MS1). -/
lemma IsSaturated.isMultiplicative {W : MorphismProperty C} (hW : IsSaturated W) :
    W.IsMultiplicative :=
  hW.hasLeftCalculusOfFractions.toIsMultiplicative

end CategoryTheory.MorphismProperty
