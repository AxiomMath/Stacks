module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePoints
public import StacksFrontier.AlgebraicGeometry.Variety.BaseFieldResidueField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Residue fields of a scheme étale over a field are separable

Let `k` be a field and let `p : X ⟶ Spec k` be smooth of relative dimension zero, equivalently
étale. Then every residue field of `X` is separable over `k`. This is the fact that "étale over a
field" means "a disjoint union of spectra of finite separable extensions", in the only form the
proof of Stacks 0FH5 needs it: Step 6 of that proof makes the complementary cycle `Z` étale over
`k`, and what is then used is that the residue fields at the points of `Z` are separable over
`k`.

## Main results

* `Stacks.Chow.hasSeparableResidueField_of_smoothOfRelativeDimension_zero` — for `p` smooth of
  relative dimension zero over `k`, every point of `X` satisfies
  `Stacks.Chow.HasSeparableResidueField k p`.

## Implementation notes

The hypothesis is `AlgebraicGeometry.SmoothOfRelativeDimension 0` rather than
`AlgebraicGeometry.Etale`, because that is the more usable of the two: Mathlib proves the two
properties equal (`AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero`) but only
`SmoothOfRelativeDimension 0` is derivable from the other by instance search, so a caller holding
either hypothesis can apply the statement in this form. Nothing is lost mathematically; the
étale hypothesis is recovered inside the proof.

The mathematics is two existing results joined by the comparison of the two algebra structures on
a residue field. Mathlib's instance in `Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean`
gives, for `p` formally unramified and locally of finite type, that `κ(x)` is separable over
`κ(p x)`; here `κ(p x)` is the residue field of `Spec k` at the image point, which
`AlgebraicGeometry.isSeparable_residueField_base_iff` identifies with `k` for the purpose of
separability. Both inputs hold for every point of `X`, so no hypothesis that `x` be closed is
needed — over a field every point of an étale scheme is closed anyway.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **The residue fields of a scheme smooth of relative dimension zero over `k` are separable
over `k`.** Equivalently, for `p` étale: étale over a field means a disjoint union of spectra of
finite separable extensions, and this is the separability half of that statement. No closedness
hypothesis on `x` is needed. -/
@[sga "1 IX 1.2" "partial"]
theorem hasSeparableResidueField_of_smoothOfRelativeDimension_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [SmoothOfRelativeDimension 0 p]
    (x : X) :
    HasSeparableResidueField k p x := by
  have : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).mpr ‹_›
  let : Algebra ((Spec (.of k)).residueField (p.base x)) (X.residueField x) :=
    (p.residueFieldMap x).hom.toAlgebra
  have hsep : Algebra.IsSeparable ((Spec (.of k)).residueField (p.base x)) (X.residueField x) :=
    inferInstance
  exact (isSeparable_residueField_base_iff k p x).mp hsep

end Stacks.Chow

end
