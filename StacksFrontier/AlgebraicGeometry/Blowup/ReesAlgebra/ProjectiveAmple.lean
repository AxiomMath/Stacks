module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Projective

/-!
# The blowup in a finite-type ideal sheaf is projective with relatively ample `𝒪(1)`

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals of finite type and `b : X' ⟶ X`
the blowup of `X` in `ℐ`. Then `b` is a projective morphism and `𝒪_{X'}(1)` is a `b`-relatively
ample invertible sheaf (Stacks 02NS).

## Main results

* `AlgebraicGeometry.isProjective_blowUpToBase_and_isRelativelyAmple_blowUpTwist`: both parts of
  Stacks tag 02NS, from `AlgebraicGeometry.isProjective_blowUpToBase` and
  `AlgebraicGeometry.exists_isInvertibleModule_isRelativelyAmple_blowUpTwist`.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Stacks Project, Tag 02NS.** Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals
of finite type and `b : X' ⟶ X` the blowup of `X` in `ℐ`. Then
1. `b : X' ⟶ X` is a projective morphism (Tag 01W8), and
2. `𝒪_{X'}(1)` is a `b`-relatively ample invertible sheaf: it is invertible, and with that
   invertibility it is ample relative to `b` (Tag 01VH).

The twist `𝒪_{X'}(1)` is `AlgebraicGeometry.blowUpTwist`, the first twisting sheaf of the relative
`Proj` of the Rees algebra `⨁_{d ≥ 0} ℐ^d`, which restricts on the chart over every affine open of
the base to the absolute `𝒪(1)` there (`AlgebraicGeometry.blowUpTwistChartIso`). -/
@[stacks 02NS "(1) `b` is projective and (2) `𝒪_{X'}(1)` is a `b`-relatively ample invertible \
sheaf"]
public theorem isProjective_blowUpToBase_and_isRelativelyAmple_blowUpTwist
    (hI : I.IsFiniteType) :
    IsProjective (blowUpToBase I) ∧
      ∃ _ : Stacks.Ample.IsInvertibleModule (blowUp I) (blowUpTwist I 1),
        Stacks.RelativeAmple.IsRelativelyAmple (blowUpToBase I) (blowUpTwist I 1) :=
  ⟨isProjective_blowUpToBase I hI, exists_isInvertibleModule_isRelativelyAmple_blowUpTwist I hI⟩

end AlgebraicGeometry
