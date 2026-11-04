module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Flat modules on flat thickenings of ringed spaces (Stacks 08VS)

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces. Tag 08VS fixes a commutative
diagram

    (X'₁, 𝒪'₁) ⟶ (X'₂, 𝒪'₂) ⟶ (X'₃, 𝒪'₃)
       ↓ f'₁         ↓ f'₂        ↓ f'₃
    (S'₁, 𝒪_{S'₁}) ⟶ (S'₂, 𝒪_{S'₂}) ⟶ (S'₃, 𝒪_{S'₃})

in which both rows are short exact sequences of first order thickenings (of `X` and of `S`
respectively), each `f'ᵢ` restricts to `f`, each pair `(f, f'ᵢ)` is a strict morphism of
thickenings, and each `f'ᵢ` is flat; together with an `𝒪'₂`-module `ℱ'₂` flat over `S'₂`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.FlatShortExactThickeningDiagram`: the whole situation.
* `FlatShortExactThickeningDiagram.restriction`: the module `ℱ = ℱ'₂|_X`.

## References

* [Stacks Project, Tag 08VS](https://stacks.math.columbia.edu/tag/08VS)
* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- Two short exact sequences of first order thickenings, one over the other, with strict and flat
vertical arrows, together with a module on the middle upper space which is flat over the middle
lower space. -/
@[stacks 08VS "the situation"]
structure FlatShortExactThickeningDiagram where
  /-- The upper row: a sequence of first order thickenings of `X`. -/
  upper : FirstOrderThickeningSequence.{u}
  /-- The lower row: a sequence of first order thickenings of `S`. -/
  lower : FirstOrderThickeningSequence.{u}
  /-- The upper row is short exact. -/
  upper_exact : IsShortExact upper
  /-- The lower row is short exact. -/
  lower_exact : IsShortExact lower
  /-- The morphism `f : X ⟶ S`. -/
  f : upper.X ⟶ lower.X
  /-- The first vertical morphism. -/
  f₁ : upper.X₁ ⟶ lower.X₁
  /-- The second vertical morphism. -/
  f₂ : upper.X₂ ⟶ lower.X₂
  /-- The third vertical morphism. -/
  f₃ : upper.X₃ ⟶ lower.X₃
  /-- The first vertical morphism restricts to `f`. -/
  restrict₁ : upper.i₁ ≫ f₁ = f ≫ lower.i₁
  /-- The second vertical morphism restricts to `f`. -/
  restrict₂ : upper.i₂ ≫ f₂ = f ≫ lower.i₂
  /-- The third vertical morphism restricts to `f`. -/
  restrict₃ : upper.i₃ ≫ f₃ = f ≫ lower.i₃
  /-- The left square of the diagram commutes. -/
  comm₁₂ : upper.f₁₂ ≫ f₂ = f₁ ≫ lower.f₁₂
  /-- The right square of the diagram commutes. -/
  comm₂₃ : upper.f₂₃ ≫ f₃ = f₂ ≫ lower.f₂₃
  /-- `(f, f₁)` is a strict morphism of thickenings. -/
  strict₁ : MorphismOfThickenings.IsStrict
    { X := upper.X, X' := upper.X₁, S := lower.X, S' := lower.X₁,
      i := upper.i₁, t := lower.i₁, f := f, f' := f₁,
      i_isThickening := upper.firstOrder₁.1,
      t_isThickening := lower.firstOrder₁.1,
      comm := restrict₁ }
  /-- `(f, f₂)` is a strict morphism of thickenings. -/
  strict₂ : MorphismOfThickenings.IsStrict
    { X := upper.X, X' := upper.X₂, S := lower.X, S' := lower.X₂,
      i := upper.i₂, t := lower.i₂, f := f, f' := f₂,
      i_isThickening := upper.firstOrder₂.1,
      t_isThickening := lower.firstOrder₂.1,
      comm := restrict₂ }
  /-- `(f, f₃)` is a strict morphism of thickenings. -/
  strict₃ : MorphismOfThickenings.IsStrict
    { X := upper.X, X' := upper.X₃, S := lower.X, S' := lower.X₃,
      i := upper.i₃, t := lower.i₃, f := f, f' := f₃,
      i_isThickening := upper.firstOrder₃.1,
      t_isThickening := lower.firstOrder₃.1,
      comm := restrict₃ }
  /-- The first vertical morphism is flat. -/
  flat₁ : AlgebraicGeometry.IsFlat f₁
  /-- The second vertical morphism is flat. -/
  flat₂ : AlgebraicGeometry.IsFlat f₂
  /-- The third vertical morphism is flat. -/
  flat₃ : AlgebraicGeometry.IsFlat f₃
  /-- The module `ℱ'₂` on the middle upper space. -/
  module₂ : SheafOfModules.{u} (structureSheafRing upper.X₂)
  /-- `ℱ'₂` is flat over `S'₂`. -/
  module₂_flat : AlgebraicGeometry.IsFlatOver f₂ module₂

/-- The restriction `ℱ = ℱ'₂|_X` of the relatively flat module to the original space. -/
noncomputable def FlatShortExactThickeningDiagram.restriction
    (D : FlatShortExactThickeningDiagram.{u}) : SheafOfModules.{u} (structureSheafRing D.upper.X) :=
  (modulePullback D.upper.i₂).obj D.module₂

end AlgebraicGeometry.RingedSpaceThickening

end
