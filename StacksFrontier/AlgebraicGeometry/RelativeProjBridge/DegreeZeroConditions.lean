module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing

/-!
# Conditions on the degree-zero part of sheaf-level graded algebra data

For a quasi-coherent graded `𝒪_S`-algebra `A` on a scheme, given as
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, two conditions on how `A` sits
over its degree-zero part `A₀` and over `𝒪_S`, both read over every affine open `U` of the base
on the graded ring of sections `Γ(U, A)`:

* `A` is of finite type as an `A₀`-algebra: `Γ(U, A)` is a finite type `Γ(U, A)₀`-algebra;
* `𝒪_S → A₀` is integral: `Γ(S, U) → Γ(U, A)₀` is integral.

These are the hypotheses of Stacks 07ZX and 07ZZ, the same affine-local readings as
`Stacks.RelativeProj.Situation.IsFiniteTypeOverDegreeZero` and
`Stacks.RelativeProj.Situation.IsIntegralInDegreeZero` on the other substrate.

## References

* [Stacks Project, Tag 07ZX](https://stacks.math.columbia.edu/tag/07ZX)
* [Stacks Project, Tag 07ZZ](https://stacks.math.columbia.edu/tag/07ZZ)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **`A` is of finite type as an `A₀`-algebra**: over every affine open `U` of the base the
graded ring of sections `Γ(U, A)` is a finite type algebra over its degree-zero piece. -/
def IsFiniteTypeOverDegreeZero : Prop :=
  ∀ U : S.Opens, IsAffineOpen U → Algebra.FiniteType (A.grading U 0) (A.sectionRing U)

/-- **`𝒪_S → A₀` is integral**: over every affine open `U` of the base the map from `Γ(S, U)` to
the degree-zero piece of the graded ring of sections is integral. -/
def IsIntegralInDegreeZero : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)).IsIntegral

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

end
