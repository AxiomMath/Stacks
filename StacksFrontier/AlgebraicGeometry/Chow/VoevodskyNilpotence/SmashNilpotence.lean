module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerAbelMorphism
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.ProjectiveBundle

/-!
# Smash nilpotence for differences of rational points (Stacks 0FH9)

On a geometrically irreducible smooth projective variety `X` over a field `k`, for `k`-rational
points `x, x'` and `n` large enough, the class of the zero cycle
`([x] - [x']) × ⋯ × ([x] - [x'])` in `CH_0(Xⁿ)` is torsion. The class is
`Stacks.Chow.smashPointDifference`, the `n`-th exterior power of `[x] - [x']` in `CH_0(Xⁿ)` for
the exterior product of Stacks 0FBV over `fieldChowSituation k`.

## Main results

* `Stacks.Chow.isOfFinAddOrder_smashPointDifference`: for `n` large enough,
  `Stacks.Chow.smashPointDifference` is torsion.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Smash nilpotence for differences of rational points (Voevodsky).** Let `k` be a field and
`X` a geometrically irreducible smooth projective scheme over `k`, with `k`-rational points
`x, x'`. For `n` large enough the class of the zero cycle `([x] - [x']) × ⋯ × ([x] - [x'])` in
`CH_0(Xⁿ)` is torsion. Here `Stacks.Chow.smashPointDifference` is the class of the `n`-th exterior
power of `[x] - [x']`, built with the exterior product of Stacks 0FBV. -/
@[stacks 0FH9]
theorem isOfFinAddOrder_smashPointDifference (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [GeometricallyIrreducible f] [Smooth f]
    (hproj : AlgebraicGeometry.IsProjectiveMorphism f) [LocallyOfFiniteType f]
    (x x' : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ N : ℕ, ∀ n ≥ N, IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle :=
  isOfFinAddOrder_smashPointDifference_of_abelMorphismIsLocallyProjectiveSpace
    Stacks.RigidifiedPicard.abelMorphismIsLocallyProjectiveSpace k X f hproj x x' hx hx'

end Stacks.Chow

end
