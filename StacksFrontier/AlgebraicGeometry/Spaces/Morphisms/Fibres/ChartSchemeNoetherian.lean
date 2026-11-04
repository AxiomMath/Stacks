module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian

/-!
# Local rings of the chart schemes of a locally Noetherian fibre

The scheme of an étale chart of a locally Noetherian algebraic space is locally Noetherian, so
its local rings are Noetherian and their maximal ideals are finitely generated. For a morphism
locally of finite type every fibre is locally Noetherian, so this holds on the chart schemes of
the fibre over any field-valued point of the target.

## Main results

* `AlgebraicGeometry.Space.fg_maximalIdeal_stalk_chartScheme`: the maximal ideal of a local
  ring of an étale chart scheme of a locally Noetherian algebraic space is finitely generated.
* `AlgebraicGeometry.Space.fg_maximalIdeal_stalk_chartScheme_fibre`: the same on the chart
  schemes of a fibre of a morphism locally of finite type.

## References

* [Stacks Project, Tag 0CUX](https://stacks.math.columbia.edu/tag/0CUX)
* [Stacks Project, Tag 0CUY](https://stacks.math.columbia.edu/tag/0CUY)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The maximal ideal of a local ring of the scheme of an étale chart of a locally Noetherian
algebraic space is finitely generated: the chart scheme is locally Noetherian, so that local
ring is Noetherian. -/
theorem fg_maximalIdeal_stalk_chartScheme (X : AlgebraicSpaces B S hS)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (V : SmallEtale B S hS X.1) (v : chartScheme V) :
    (IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk v)).FG :=
  have : IsLocallyNoetherian (chartScheme V) :=
    isLocallyNoetherian_chartScheme B S hS X hLN V
  Ideal.fg_of_isNoetherianRing _

/-- The maximal ideal of a local ring of the scheme of an étale chart of a fibre of a morphism
locally of finite type is finitely generated: the fibre over any field-valued point of the
target is locally Noetherian. -/
theorem fg_maximalIdeal_stalk_chartScheme_fibre {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (p : FieldValuedPoint B S hS Y.1)
    (W : SmallEtale B S hS (fibreAtFieldValuedPoint B S hS f p).1) (w : chartScheme W) :
    (IsLocalRing.maximalIdeal ((chartScheme W).presheaf.stalk w)).FG :=
  fg_maximalIdeal_stalk_chartScheme B S hS (fibreAtFieldValuedPoint B S hS f p)
    (isLocallyNoetherianFiberAt_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hf p) W w

end AlgebraicGeometry.Space

end
