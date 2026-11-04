module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Reduced

/-!
# Reducedness of schemes is local in the étale topology

Being reduced is a property of schemes local for jointly surjective families of étale
morphisms, the étale precoverage being contained in the smooth one.

## Main results

* `AlgebraicGeometry.isReduced_isLocal_etale` states that reducedness is local for the étale
  precoverage.

## Implementation notes

Locality for the smooth precoverage is `AlgebraicGeometry.isReduced_isLocal_smooth` of
`StacksFrontier/AlgebraicGeometry/Descent/LocalProperties/Reduced.lean`, which carries Tag 034E;
locality for a coarser precoverage is the weaker statement, so nothing beyond the inclusion
`Scheme.precoverage_mono` and `CategoryTheory.ObjectProperty.IsLocal.of_le` is needed here.

## References

* [Stacks Project, Tag 034E](https://stacks.math.columbia.edu/tag/034E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Reducedness of schemes is local for the étale precoverage, the étale precoverage being
contained in the smooth one. -/
public instance isReduced_isLocal_etale :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsReduced X)
      Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le
    (Scheme.precoverage_mono (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
      (Q := (@Smooth.{u} : MorphismProperty Scheme.{u})) (fun _ _ f hf => by
      have : Etale f := hf
      exact inferInstance))

end AlgebraicGeometry
