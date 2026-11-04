module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute

/-!
# Smooth, étale and Zariski coverings are fppf

A covering family of schemes is fppf when its members are flat and locally of finite
presentation and their images cover the target.  Smooth and étale morphisms are flat and
locally of finite presentation, so smooth and étale covering families are fppf; the same
holds for Zariski coverings, since open immersions are étale.

## Main results

* `AlgebraicGeometry.Scheme.smoothPrecoverage_le_fppfPrecoverage`: every smooth covering
  family is an fppf covering family.
* `AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage`: every étale covering
  family is an fppf covering family.

## Implementation notes

The comparisons are stated as inclusions of precoverages rather than of the generated
Grothendieck topologies, so that they retain the family-level data.  The Zariski inclusion
is `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_fppfPrecoverage`, which is already
available.

## References

* [Stacks Project, Tag 021N](https://stacks.math.columbia.edu/tag/021N)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

/-- **Stacks 021N.** Every smooth covering family is an fppf covering family. -/
@[stacks 021N "smooth coverings"]
public theorem smoothPrecoverage_le_fppfPrecoverage :
    Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) ≤
      Scheme.fppfPrecoverage :=
  Scheme.precoverage_mono fun _ _ f hf ↦ by
    let _ : Smooth f := hf
    exact ⟨inferInstance, inferInstance⟩

/-- **Stacks 021N.** Every étale covering family is an fppf covering family. -/
@[stacks 021N "étale coverings"]
public theorem etalePrecoverage_le_fppfPrecoverage :
    Scheme.etalePrecoverage ≤ Scheme.fppfPrecoverage :=
  Scheme.precoverage_mono fun _ _ f hf ↦ by
    let _ : Etale f := hf
    exact ⟨inferInstance, inferInstance⟩

add_to_stacks 021N "Zariski coverings" Scheme.zariskiPrecoverage_le_fppfPrecoverage

end AlgebraicGeometry.Scheme
