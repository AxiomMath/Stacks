module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fpqc case of Stacks 0D3C in the shape of the proof of Stacks 0D3D

`AlgebraicGeometry.Space.RelativeAmpleFpqcDescends` is the implication (2) ⟹ (1) of Stacks 0D3C
for an invertible module, in the shape the proof of Stacks 0D3D consumes it. It holds, by
`AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_isRelativelyAmple_of_isFpqcCovering`.

## Main results

* `AlgebraicGeometry.Space.relativeAmpleFpqcDescends`: the statement above.

## References

* [Stacks Project, Tag 0D3C](https://stacks.math.columbia.edu/tag/0D3C)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Space

/-- **The fpqc case of Stacks 0D3C, (2) implies (1).** Relative ampleness of an invertible
module may be checked on the base changes along the members of an fpqc covering of the
target. -/
@[sga "1 VIII 7.8" "Final clause only"]
theorem relativeAmpleFpqcDescends (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    RelativeAmpleFpqcDescends B S hS :=
  fun _ _ _ L hL _ _ _ _ _ _ hsq hfpqc hamp =>
    (isRelativelyAmple_iff_forall_isRelativelyAmple_of_isFpqcCovering hsq L hL hfpqc).2 hamp

end AlgebraicGeometry.Space

end
