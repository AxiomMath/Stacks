module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundleExists
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor

/-!
# Stacks 0FH9 from the projective bundle structure of the Abel morphism

The whole of Stacks 0FH9, at the source's hypotheses, from the single statement that the Abel
morphism `Hilb^d_{X/k} ⟶ Pic⁰_{X/k,σ}` of a curve is Zariski-locally a projective space bundle
in degrees `d ≥ 2g - 1`, `Stacks.RigidifiedPicard.AbelMorphismIsLocallyProjectiveSpace`.

## Main results

* `Stacks.Chow.smashNilpotenceCurveCase_of_abelMorphismIsLocallyProjectiveSpace`: the curve case.
* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_abelMorphismIsLocallyProjectiveSpace`:
  **Stacks 0FH9**, given the projective bundle structure of the Abel morphism.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **The curve case of Stacks 0FH9**, given the projective bundle structure of the Abel
morphism. -/
theorem smashNilpotenceCurveCase_of_abelMorphismIsLocallyProjectiveSpace
    (hbun : Stacks.RigidifiedPicard.AbelMorphismIsLocallyProjectiveSpace.{u}) :
    SmashNilpotenceCurveCase.{u} :=
  smashNilpotenceCurveCase_of_abelBundle
    (Stacks.RigidifiedPicard.abelBundleExists_of_claim
      (fun K _ _ => Stacks.WeilCohomology.cohomologyLocusDivisorExistence K)
      (fun K _ _ => Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness K) hbun)

/-- **Stacks 0FH9, given the projective bundle structure of the Abel morphism.** Let `k` be a
field and `X` a smooth, geometrically irreducible, H-projective scheme over `k` with `k`-rational
points `x, x'`. For `n` large enough the class of the zero cycle
`([x] - [x']) × ⋯ × ([x] - [x'])` in `CH_0(Xⁿ)` is torsion. -/
theorem isOfFinAddOrder_smashPointDifference_of_abelMorphismIsLocallyProjectiveSpace
    (hbun : Stacks.RigidifiedPicard.AbelMorphismIsLocallyProjectiveSpace.{u})
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ (fieldChowSituation k).S)
    [GeometricallyIrreducible f] [Smooth f] (hproj : IsProjectiveMorphism f)
    [LocallyOfFiniteType f] (x x' : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ N : ℕ, ∀ n ≥ N, IsOfFinAddOrder (smashPointDifference k f x x' hx hx' n).cycle :=
  isOfFinAddOrder_smashPointDifference_of_curveCase
    (smashNilpotenceCurveCase_of_abelMorphismIsLocallyProjectiveSpace hbun) k X f hproj x x' hx hx'

end Stacks.Chow

end
