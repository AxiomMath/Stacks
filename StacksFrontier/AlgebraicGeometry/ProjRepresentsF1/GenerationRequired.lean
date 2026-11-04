module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationNecessary
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.ZeroNotInvertible

/-!
# Tag 01O4's generation hypothesis is required by its bundle

`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` is stated for an arbitrary quasi-coherent
graded algebra, where Tag 01O4 reads one generated as an `𝒜₀`-algebra by `𝒜₁`. When `𝒜₁` is a
zero object, a bundle exists only over an empty relative `Proj`.

Taking `𝒜 = 𝒪_S[x]` with `x` of degree two — so `𝒜₁ = 0` while `Proj_S(𝒜) = S` — the conclusion
fails for every nonempty base.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isEmpty_of_f1Pair_of_isZero_piece_one`: an
  invertible degree-one quotient over a test scheme empties that scheme as soon as `𝒜₁` is a zero
  object.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isEmpty_relativeProj_of_f1Bundle_of_isZero_piece_one`:
  a bundle for an algebra whose `𝒜₁` is a zero object empties the relative `Proj`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

/-- **An invertible degree-one quotient empties its test scheme when `𝒜₁` vanishes.** -/
public theorem isEmpty_of_f1Pair_of_isZero_piece_one {T : Scheme.{u}} {f : T ⟶ S}
    (P : F1Pair A TA f) (hA : IsZero (A.piece 1)) : IsEmpty T :=
  isEmpty_of_isZero_of_isInvertible T P.L P.invertible (isZero_L_of_isZero_piece_one A TA P hA)

/-- **A bundle for an algebra with vanishing degree-one piece empties the relative `Proj`.** -/
public theorem isEmpty_relativeProj_of_f1Bundle_of_isZero_piece_one
    {ι : TensorAlgebraPullbackIsos.{u} TA} (B : F1Bundle A TA ι) (hA : IsZero (A.piece 1)) :
    IsEmpty (relativeProj A).scheme :=
  isEmpty_of_f1Pair_of_isZero_piece_one A TA B.universal hA

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
