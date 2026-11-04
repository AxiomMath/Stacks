module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.ProjectiveBundle

/-!
# Abel projective bundles exist

For a smooth proper geometrically irreducible curve `X` over an algebraically closed field `k`
with a rational point `x` and every `n ≥ 2g + 1`, the Abel morphism `Hilb^n_{X/k} ⟶ Pic⁰_{X/k,x}`,
translated by `n[x]`, is a projective bundle of rank `n - g` over the group scheme representing
`Pic⁰_{X/k,x}`. This is `Stacks.Chow.AbelBundleExists`, the input the curve case of
[Stacks, Tag 0FH9] consumes, proved here with nothing granted.

## Main results

* `Stacks.RigidifiedPicard.abelBundleExists`: `Stacks.Chow.AbelBundleExists`, from
  `Stacks.RigidifiedPicard.abelBundleExists_of_isLocallyProjectiveSpace` and the projective bundle
  structure of the Abel morphism, `Stacks.RigidifiedPicard.abelMorphismIsLocallyProjectiveSpace`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public section

universe u

namespace Stacks.RigidifiedPicard

/-- **Abel projective bundles exist**, with nothing granted: the projective bundle structure of
the Abel morphism is `Stacks.RigidifiedPicard.abelMorphismIsLocallyProjectiveSpace`. -/
theorem abelBundleExists : Stacks.Chow.AbelBundleExists.{u} :=
  abelBundleExists_of_isLocallyProjectiveSpace abelMorphismIsLocallyProjectiveSpace

end Stacks.RigidifiedPicard

end
