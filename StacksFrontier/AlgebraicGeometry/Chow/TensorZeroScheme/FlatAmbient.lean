module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition

/-!
# The ambient space of Tag 0F97 is flat of relative dimension two over the base

Let `Y` be a scheme and let `L₁` and `L₂` be invertible `𝒪_Y`-modules. The scheme of [Stacks, Tag
0F97] is cut out by one equation inside the fibre product
`Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two line bundles of [Stacks, Tag 01M2], built in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic`. This file proves that the structure
morphism `q` of that fibre product is **flat of relative dimension two** over `Y`.

Both facts come from the rank-one local triviality of a line bundle,
`Stacks.LineBundle.isAffineSpaceBundle_lineBundleProj`: the first projection of the fibre product
is a base change of the second line bundle's structure morphism, and both flatness and
"locally of finite type of relative dimension `d`" are stable under base change; the composite
with the first line bundle's structure morphism is `q`, and relative dimensions of a composition
in which the first morphism is flat add, by [Stacks, Tag 02NL].

## Main results

* `Stacks.Chow.TensorZeroScheme.flat_firstProj` and
  `Stacks.Chow.TensorZeroScheme.locallyOfFiniteTypeRelativeDimension_firstProj`: the first
  projection of the fibre product is flat of relative dimension one.
* `Stacks.Chow.TensorZeroScheme.flat_totalProj` and
  `Stacks.Chow.TensorZeroScheme.locallyOfFiniteTypeRelativeDimension_totalProj`: **the structure
  morphism `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` is flat of relative dimension two.**

## Implementation notes

Relative dimension is carried here in the bundled form
`AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension`, which is a `MorphismProperty` and hence
has the base-change instance; `AlgebraicGeometry.RelativeDimension` itself takes a
`LocallyOfFiniteType` instance as an argument of the definition and so is not one.

The `IsStableUnderBaseChangeAlong` hypothesis of `MorphismProperty.pullback_fst` is produced by
hand from the `IsStableUnderBaseChange` instance in both cases, as in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FiniteType`: instance search does not chain
the two under this project's `maxSynthPendingDepth`.

*What this does not give.* Flatness of the structure morphism `p` of the scheme of Tag 0F97
itself — the tag's condition (2) — does not follow from anything here: `p` is the restriction of
`q` to the zero scheme of `z₁ ⊗ z₂ - q^*s`, and flatness of that closed subscheme over `Y` is
the statement that the equation is a nonzerodivisor on every fibre of `q`, which needs the
affine-local presentation `p^{-1}(Spec A) = Spec A[z₁, z₂]/(z₁z₂ - f)`. That is carried out in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FlatRelativeDimension`
(`Stacks.Chow.TensorZeroScheme.flat_proj`, `relativeDimension_proj`), which uses none of this
file.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02NL](https://stacks.math.columbia.edu/tag/02NL)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.LineBundle (lineBundleProj)

universe u

@[expose] public noncomputable section

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

/-- A base-change-stable property holding for the second line bundle's structure morphism holds
for the first projection of the fibre product. -/
private theorem firstProj_of_lineBundleProj (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (h : P (lineBundleProj Y L₂)) : P (firstProj Y L₁ L₂) := by
  let : MorphismProperty.IsStableUnderBaseChangeAlong P (lineBundleProj Y L₁) :=
    ⟨fun pb h => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  rw [firstProj]
  exact MorphismProperty.pullback_fst _ _ h

include h₁ h₂ in
/-- The first projection of the fibre product of the two line bundles is flat, being a base
change of the second line bundle's structure morphism. -/
theorem flat_firstProj : AlgebraicGeometry.Flat (firstProj Y L₁ L₂) :=
  firstProj_of_lineBundleProj Y L₁ L₂ (@AlgebraicGeometry.Flat.{u})
    (Stacks.LineBundle.flat_lineBundleProj Y L₂)

include h₁ h₂ in
/-- The first projection of the fibre product of the two line bundles is locally of finite type
of relative dimension one, being a base change of the second line bundle's structure
morphism. -/
theorem locallyOfFiniteTypeRelativeDimension_firstProj :
    AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension.{u} 1 (firstProj Y L₁ L₂) :=
  firstProj_of_lineBundleProj Y L₁ L₂ _
    (Stacks.LineBundle.locallyOfFiniteTypeRelativeDimension_lineBundleProj Y L₂)

include h₁ h₂ in
/-- **The structure morphism `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` is flat**, being the
composite of the flat first projection with the flat structure morphism of the first line
bundle. -/
theorem flat_totalProj : AlgebraicGeometry.Flat (totalProj Y L₁ L₂) := by
  have := flat_firstProj Y L₁ L₂
  have := Stacks.LineBundle.flat_lineBundleProj Y L₁
  rw [totalProj]
  infer_instance

include h₁ h₂ in
/-- **The structure morphism `q : Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` is locally of finite
type of relative dimension two.** The first projection is flat of relative dimension one and so
is the structure morphism of the first line bundle, and the relative dimensions of a composition
whose first morphism is flat add ([Stacks, Tag 02NL]). -/
theorem locallyOfFiniteTypeRelativeDimension_totalProj :
    AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension.{u} 2 (totalProj Y L₁ L₂) := by
  obtain ⟨hft₁, hdim₁⟩ := locallyOfFiniteTypeRelativeDimension_firstProj Y L₁ L₂
  obtain ⟨hft₂, hdim₂⟩ :=
    Stacks.LineBundle.locallyOfFiniteTypeRelativeDimension_lineBundleProj Y L₁
  have := hft₁
  have := hft₂
  have := flat_firstProj Y L₁ L₂
  have hcomp := AlgebraicGeometry.RelativeDimension.comp_of_flat
    (firstProj Y L₁ L₂) (lineBundleProj Y L₁) hdim₁ hdim₂
  rw [totalProj]
  exact ⟨inferInstance, hcomp⟩

end Stacks.Chow.TensorZeroScheme

end
