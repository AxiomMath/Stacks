module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceUniversal

/-!
# Factoring through the zero section of a line bundle

Let `D` be a line-bundle situation, `p : Tot(L) ⟶ X` the total space of `L` and `o : X ⟶ Tot(L)`
its zero section. The functor of points of the total space,
`Stacks.LineBundle.Situation.totalSpaceHomEquiv`, writes a morphism `f : Y ⟶ Tot(L)` as a pair
consisting of a morphism `g : Y ⟶ X` and a morphism of `𝒪_X`-modules `L ⟶ g_* 𝒪_Y`. This file
records that

**`f` factors through the zero section exactly when the second component of that pair
vanishes.**

In other words the zero section is the subfunctor of points whose linear functional is zero,
which is what makes the zero section the zero of the fibrewise group structure.

## Main results

* `Stacks.LineBundle.Situation.totalSpaceHomEquiv_comp_zeroSection`: the pair attached to
  `g ≫ o` is `(g, 0)`.
* `Stacks.LineBundle.Situation.factorsThrough_zeroSection_iff`: **a morphism into the total
  space factors through the zero section if and only if the module component of its pair is
  zero**, and the factorization is then through `f ≫ p`.

## Implementation notes

Both statements are the naturality of the functor of points
(`Stacks.LineBundle.Situation.totalSpaceHomEquiv_comp`) together with its value at the zero
section (`Stacks.LineBundle.Situation.totalSpaceHomEquiv_zeroSection`); nothing about the
symmetric algebra is used here.

The pair is a dependent sum, so moving `g ≫ 𝟙_X` to `g` in its first component is not a
rewrite: the type of the second component changes with it. `sigmaMkZero_congr` performs that
move for the pairs whose second component is zero, which are the only ones appearing, by
substituting the equality of first components.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- Two pairs with zero module component and equal morphisms to the base are equal. The
substitution is needed because the type of the module component depends on that morphism. -/
private theorem sigmaMkZero_congr {Y : Scheme.{u}} {a a' : Y ⟶ D.X} (haa : a = a') :
    (⟨a, 0⟩ : Σ g : Y ⟶ D.X, (D.L ⟶ (Scheme.Modules.pushforward g).obj
        (SheafOfModules.unit Y.ringCatSheaf))) = ⟨a', 0⟩ := by
  subst haa
  rfl

/-- **The pair attached to a morphism that factors through the zero section has zero module
component**, the morphism to the base being the factor. -/
theorem Situation.totalSpaceHomEquiv_comp_zeroSection {Y : Scheme.{u}} (g : Y ⟶ D.X) :
    D.totalSpaceHomEquiv Y (g ≫ D.zeroSection) = ⟨g, 0⟩ := by
  refine (D.totalSpaceHomEquiv_comp g D.zeroSection).trans ?_
  rw [D.totalSpaceHomEquiv_zeroSection]
  refine Eq.trans ?_ (sigmaMkZero_congr D (Category.comp_id g))
  exact congrArg (Sigma.mk (g ≫ 𝟙 D.X)) Limits.zero_comp

/-- **A morphism into the total space of a line bundle factors through the zero section exactly
when the module component of its pair under the functor of points vanishes.** The factor is
then the morphism to the base attached to it, that is, its composite with the projection. -/
theorem Situation.factorsThrough_zeroSection_iff {Y : Scheme.{u}} (f : Y ⟶ D.totalSpace) :
    (∃ g : Y ⟶ D.X, g ≫ D.zeroSection = f) ↔ (D.totalSpaceHomEquiv Y f).2 = 0 := by
  refine ⟨fun ⟨g, hg⟩ => ?_, fun hz => ?_⟩
  · rw [← hg, D.totalSpaceHomEquiv_comp_zeroSection]
  · refine ⟨(D.totalSpaceHomEquiv Y f).1, (D.totalSpaceHomEquiv Y).injective ?_⟩
    rw [D.totalSpaceHomEquiv_comp_zeroSection, ← hz]

end Stacks.LineBundle

end
