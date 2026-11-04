module

public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.Characterization

/-!
# Disjoint unions of ind-quasi-affine morphisms

A finite disjoint union of ind-quasi-affine morphisms is ind-quasi-affine: if `g j : X j ⟶ Y j`
is ind-quasi-affine for every member of a finite family, then so is the induced morphism
`∐ X ⟶ ∐ Y` of coproducts.

## Main results

* `AlgebraicGeometry.isIndQuasiAffineHom_sigmaMap`: a finite disjoint union of ind-quasi-affine
  morphisms is ind-quasi-affine.

## Implementation notes

Ind-quasi-affineness is Zariski local on the base, by
`AlgebraicGeometry.isIndQuasiAffineHom_isZariskiLocalAtTarget`, so this is an instance of
`AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap`. No hypothesis on the index type beyond
finiteness is needed, and in particular the empty family is allowed.

## References

* [Stacks Project, Tag 0F1U](https://stacks.math.columbia.edu/tag/0F1U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- A finite disjoint union of ind-quasi-affine morphisms, viewed as a morphism between the two
coproducts, is ind-quasi-affine. -/
theorem isIndQuasiAffineHom_sigmaMap {ι : Type v} [Finite ι] {X Y : ι → Scheme.{u}}
    (g : ∀ j, X j ⟶ Y j) (hg : ∀ j, IsIndQuasiAffineHom (g j)) :
    IsIndQuasiAffineHom (Limits.Sigma.map g) :=
  IsZariskiLocalAtTarget.sigmaMap g hg

end AlgebraicGeometry

end
