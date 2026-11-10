module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.ColengthDrop
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.LocalSplitting

/-!
# The colength descent of Tag 0AHH, reduced to the chart computation

`Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent` is the statement used by
[Stacks, Tag 0AHH], [Stacks, Tag 0AHI], [Stacks, Tag 0BIB], [Stacks, Tag 0C5H] and
[Stacks, Tag 0C5S]: at every point of the support of a sheaf of ideals supported on finitely many
closed points with regular two-dimensional local rings, one blowup at that point splits the
inverse image of the ideal as a power of the exceptional divisor times an ideal sheaf of strictly
smaller total colength.

Composing `CartierDescent.LocalSplitting` with `CartierDescent.Globalization` reduces it to a
single statement about the two standard charts of the blowup of a two-dimensional regular local
ring at its closed point — the colength drop of [Stacks, Tag 0AGT] — and that is
`CartierDescent.Colength.ColengthDrop`'s `sum_length_stalk_quotient_lt`.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.pointBlowupColengthDescent` — the descent.

## Implementation notes

The three inputs are `sum_length_stalk_quotient_lt`, the colength drop on the two charts;
`localColengthSplitting_of_colength`, which supplies a regular system of parameters and runs the
support half of [Stacks, Tag 0AGT]; and `pointBlowupColengthDescent_of_local`, the flat base
change to the local ring at the point.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-- **The colength descent of [Stacks, Tag 0AHH].** At every point of the support of a sheaf of
ideals supported on finitely many closed points with regular two-dimensional local rings, one
blowup at that point splits the inverse image of the ideal as a power of the exceptional divisor
times an ideal sheaf of strictly smaller total colength.

This is the local splitting of [Stacks, Tag 0AGT] globalised: the colength drop on the two
standard charts, the support half of Tag 0AGT, and the flat base change to the local ring at the
point. -/
public theorem pointBlowupColengthDescent :
    Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent.{u} :=
  pointBlowupColengthDescent_of_local
    (localColengthSplitting_of_colength fun A _ _ hdim _ _ hspan L n hmn _ _ hd _ hfac hmax T
      _ => sum_length_stalk_quotient_lt A hdim hspan L n hmn hd hfac hmax T)

end Stacks.ResolutionOfSurfaces.CartierDescent

end
