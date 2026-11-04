module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.GradedModule.ExternalShift
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomial
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.StandardOpenBaseChange

/-!
# The twists of the weighted polynomial algebra and their degree-zero localizations

For the weighted polynomial algebra `S = k[x, y, z]` with `deg x, y, z = 1, 2, 3` of
`StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomial`, this file records `S` and its
twists `S(1)` and `S(2)` as externally graded objects, and their degree-zero localizations at `z`
as submodules of the ordinary localization `S_z`.

## Main definitions

* `Stacks.WeightedPolynomialSituation.externalGradedAlgebra`: `S` as an externally `ℤ`-graded
  algebra over `k`, and `Stacks.WeightedPolynomialSituation.regularModule`: `S` as the regular
  graded right module over itself.
* `Stacks.WeightedPolynomialSituation.firstTwist` and
  `Stacks.WeightedPolynomialSituation.secondTwist`: the shifts `S(1)` and `S(2)`.
* `Stacks.WeightedPolynomialSituation.localizedTwist`: the degree-zero localization of the twist
  `S(t)` at `z`, with `firstTwistLocalization` and `secondTwistLocalization` the cases
  `t = 1, 2`.

## Implementation notes

Two presentations of a twist are in play and they are used for different purposes. The *external*
one, `ExternallyGradedRightModule`, is a family of `k`-modules indexed by `ℤ`, and the twist is
the reindexing `ExternallyGradedRightModule.shift`; this is the shape the generalities about
graded modules are stated in. The *internal* one,
`Stacks.WeightedPolynomialSituation.twistGrading`, grades the single `S`-module `S` by
submodules; this is the shape the associated sheaf on `Proj` is built from. They describe the
same object, so both are supplied and neither is derived from the other.

The degree-zero localization of a twist is `Stacks.ProjStandardOpenBaseChange.twistAway`, which
realizes it inside the ordinary localization `S_z` as the span of the fractions `p / zⁿ` with
`p` homogeneous of weight `3n + t`; the degree of `z` is `3`.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

namespace Stacks.WeightedPolynomialSituation

/-- The weighted polynomial algebra, as an externally `ℤ`-graded algebra over the ground
field. -/
public def externalGradedAlgebra (E : WeightedPolynomialSituation) :
    ExternallyGradedAlgebra E.k where
  piece := fun n ↦ E.grading n
  mul := fun i j ↦
    { toFun := fun a ↦
        { toFun := fun b ↦ ⟨(a : E.S) * (b : E.S),
            MvPolynomial.IsWeightedHomogeneous.mul a.2 b.2⟩
          map_add' := by intro b c; ext; simp [mul_add]
          map_smul' := by intro r b; ext; simp }
      map_add' := by intro a b; ext c; simp [add_mul]
      map_smul' := by intro r a; ext b; simp }
  one := ⟨1, MvPolynomial.isWeightedHomogeneous_one E.k E.weight⟩
  mul_assoc := by
    intro i j l a b c
    rw [Subtype.heq_iff_coe_eq (by intro p; rw [add_assoc i j l])]
    exact mul_assoc _ _ _
  one_mul := by
    intro i a
    rw [Subtype.heq_iff_coe_eq (by intro p; rw [zero_add])]
    exact one_mul _
  mul_one := by
    intro i a
    rw [Subtype.heq_iff_coe_eq (by intro p; rw [add_zero])]
    exact mul_one _

/-- The weighted polynomial algebra, regarded as its regular graded right module. -/
public def regularModule (E : WeightedPolynomialSituation) :
    ExternallyGradedRightModule E.externalGradedAlgebra where
  piece := E.externalGradedAlgebra.piece
  smul := E.externalGradedAlgebra.mul
  smul_mul := E.externalGradedAlgebra.mul_assoc
  smul_one := E.externalGradedAlgebra.mul_one

/-- The first twist `M = S(1)` of the weighted polynomial algebra. -/
public def firstTwist (E : WeightedPolynomialSituation) :
    ExternallyGradedRightModule E.externalGradedAlgebra :=
  ExternallyGradedRightModule.shift E.regularModule 1

/-- The second twist `N = S(2)` of the weighted polynomial algebra. -/
public def secondTwist (E : WeightedPolynomialSituation) :
    ExternallyGradedRightModule E.externalGradedAlgebra :=
  ExternallyGradedRightModule.shift E.regularModule 2

/-- The degree-zero localization of `S(t)` at `z`, embedded in `S_z`. Its generators are the
fractions of a homogeneous polynomial of weight `3n + t` by `zⁿ`. -/
public noncomputable abbrev localizedTwist (E : WeightedPolynomialSituation) (t : ℤ) :=
  Stacks.ProjStandardOpenBaseChange.twistAway E.naturalGrading E.z 3 t

/-- The module `M₍z₎` for `M = S(1)`. -/
public noncomputable abbrev firstTwistLocalization (E : WeightedPolynomialSituation) :=
  E.localizedTwist 1

/-- The module `N₍z₎` for `N = S(2)`. -/
public noncomputable abbrev secondTwistLocalization (E : WeightedPolynomialSituation) :=
  E.localizedTwist 2

end Stacks.WeightedPolynomialSituation

end
