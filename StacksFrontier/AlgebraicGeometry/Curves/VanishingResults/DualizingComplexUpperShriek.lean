module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageQcqs
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic

/-!
# The dualizing complex of a proper scheme over a field as an upper shriek

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism. The dualizing complex
`ω_X^• = a(𝒪_{Spec k})` of [Stacks, Tag 0BS2] (`Stacks.Duality.dualizingComplexOverField`) is the
value at `𝒪_{Spec k}` of the upper shriek functor `f^!` of [Stacks, Tag 0A9Y], computed with the
compactification that a proper morphism is of itself: `ω_X^• = f^!𝒪_{Spec k}`.

## Main definitions

* `Stacks.Duality.curveFTS`, `Stacks.Duality.baseFTS`, `Stacks.Duality.curveFTSHom`: `X`, `Spec k`
  and `f` as objects and a morphism of the category `AlgebraicGeometry.FTS (Spec k)` of
  [Stacks, Tag 0F42].
* `Stacks.Duality.dualizingComplexOverFieldIsoUpperShriek`: `f^!𝒪_{Spec k} ≅ ω_X^•`.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open DerivedPushforward

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- `X`, with its proper structure morphism, as an object of the category of schemes separated
and of finite type over `Spec k` ([Stacks, Tag 0F42]). -/
abbrev curveFTS : FTS (Spec (CommRingCat.of k)) := FTS.mk f

variable (k) in
/-- `Spec k` as the final object of the category of schemes separated and of finite type over
`Spec k` ([Stacks, Tag 0F42]). -/
abbrev baseFTS : FTS (Spec (CommRingCat.of k)) := FTS.mk (𝟙 (Spec (CommRingCat.of k)))

/-- The structure morphism `f : X ⟶ Spec k` as a morphism of `FTS (Spec k)`. -/
abbrev curveFTSHom : curveFTS f ⟶ baseFTS k :=
  MorphismProperty.Over.homMk f (Category.comp_id f)

/-- The underlying morphism of schemes of `curveFTSHom f` is proper. -/
instance isProper_curveFTSHom_left : IsProper (curveFTSHom f).left :=
  inferInstanceAs (IsProper f)

/-- **`ω_X^• = f^!𝒪_{Spec k}`.** The dualizing complex `a(𝒪_{Spec k})` of a proper scheme over a
field is the upper shriek of [Stacks, Tag 0A9Y] of `𝒪_{Spec k}`, computed with the
compactification `X̄ = X` of the proper morphism `f` (`Stacks.Duality.properCompactification`). -/
def dualizingComplexOverFieldIsoUpperShriek :
    (upperShriek (curveFTSHom f) (properCompactification (curveFTSHom f))).obj
      (derivedStructureSheaf (Spec (CommRingCat.of k))) ≅
        @dualizingComplexOverField k _ X f inferInstance inferInstance :=
  (upperShriekProperIso (curveFTSHom f)).app _

end Stacks.Duality

end
