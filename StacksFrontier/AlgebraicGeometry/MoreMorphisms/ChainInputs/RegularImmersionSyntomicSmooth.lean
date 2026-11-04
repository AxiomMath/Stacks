module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-regular syntomic immersion into a smooth scheme is regular

Let `i : Y ⟶ X` be an immersion and `f : X ⟶ S` a smooth morphism, and assume the composite
`i ≫ f` is syntomic. Then `i` is a regular immersion as soon as it is a *quasi-regular*
immersion.

## Main results

* `Stacks.AlgebraicGeometry.isRegularImmersion_of_isQuasiRegularImmersion_of_syntomic_of_smooth`:
  a quasi-regular immersion whose source is syntomic over the base and whose target is smooth
  over the base is a regular immersion.

## Implementation notes

The structure morphism of the source is written as the composite `i ≫ f`, which encodes the
commutativity of the triangle of Stacks tag 067T.

## References

* [Stacks Project, Lemma 31.22.6 (Tag 067T)](https://stacks.math.columbia.edu/tag/067T)
* [Stacks Project, Lemma 31.22.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

/-- A quasi-regular immersion whose source is syntomic over the base and whose target is smooth
over the base is a regular immersion. -/
@[ega "IV 19.2.4" "c′) ⇒ c), special case"]
theorem isRegularImmersion_of_isQuasiRegularImmersion_of_syntomic_of_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i] [Smooth f]
    (h : Syntomic (i ≫ f)) (hqr : IsQuasiRegularImmersion i) :
    IsRegularImmersion i :=
  have : Flat f := AlgebraicGeometry.flat (syntomic_of_smooth f)
  have : LocallyOfFinitePresentation f :=
    AlgebraicGeometry.locallyOfFinitePresentation (syntomic_of_smooth f)
  isRegularImmersion_of_isRelativeQuasiRegularImmersion f i ⟨AlgebraicGeometry.flat h, hqr⟩

end Stacks.AlgebraicGeometry

end
