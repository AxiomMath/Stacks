module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentSectionsTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags for three results on `D_QCoh` of algebraic spaces

The results are proved in the imported modules; this file records the tag on each of them.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjoint_boundedBelow`: the right adjoint of
  `Rf_*` maps `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)` (Stacks 0E56).
* `AlgebraicGeometry.Space.exists_isHomotopyColimit_isPerfect_iff_countable`: an object of
  `D_QCoh(𝒪_X)` is a homotopy colimit of perfect objects if and only if its cohomology sheaves
  have countable sections over the affine schemes étale over `X` (Stacks 0CRV).
* `AlgebraicGeometry.Space.isPseudoCoherent_representedAffineDerivedSections_tensor`:
  pseudo-coherence of `RΓ(X, E ⊗^L K)` passes from perfect to pseudo-coherent `E` (Stacks 0CWH).

## References

* [Stacks Project, Tag 0E56](https://stacks.math.columbia.edu/tag/0E56)
* [Stacks Project, Tag 0CRV](https://stacks.math.columbia.edu/tag/0CRV)
* [Stacks Project, Tag 0CWH](https://stacks.math.columbia.edu/tag/0CWH)
-/

@[expose] public section

add_to_stacks 0E56 AlgebraicGeometry.Space.quasicoherentDerivedRightAdjoint_boundedBelow

add_to_stacks 0CRV AlgebraicGeometry.Space.exists_isHomotopyColimit_isPerfect_iff_countable

add_to_stacks 0CWH AlgebraicGeometry.Space.isPseudoCoherent_representedAffineDerivedSections_tensor

end
