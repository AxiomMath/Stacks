module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic.ExteriorProductComponent
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic.PthRootDifferentials
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.HigherTrace.Basic.TraceMap

/-!
# Higher trace for an inseparable extension of degree `p`

Let `Λ → R → S` be ring maps in characteristic `p`, and suppose that `S` is obtained from `R`
by adjoining a root `x` of `X ^ p - C a`.  There is an `R`-linear trace from differential forms
on `S` to differential forms on `R`.  It sends `η₁ ∧ ⋯ ∧ ηₜ ∧ xᵐ dx` to zero below the top power,
and sends the top power to `η₁ ∧ ⋯ ∧ ηₜ ∧ da`.

## Main definitions

* `KaehlerDifferential.higherTrace` is the higher trace on differential forms.

## Main results

* `KaehlerDifferential.higherTrace_apply_of_le`: its value below the top power is zero.
* `KaehlerDifferential.higherTrace_apply_top`: its value at the top power is the wedge with
  `da`.
* `KaehlerDifferential.higherTrace_smul_baseForm`: it annihilates forms coming from `R` after an
  arbitrary multiplication by an element of `S`.
* `KaehlerDifferential.higherTrace_eq_of_presentations`: the map does not depend on the chosen
  purely inseparable presentation.
* `KaehlerDifferential.pthRootAbsoluteDifferentials_span_eq_top`: `Ω_{S/Λ}` is generated over `S`
  by the differentials pulled back from `R` together with `dx`, which is the set on which those
  three evaluation results compute the trace.

## Implementation notes

The chosen `R`-algebra equivalence from the adjoin-root algebra records both the presentation
`S ≅ R[X]/(X ^ p - a)` and the element denoted `x` in the source.  The vanishing statement is the
assertion that the trace annihilates the image of `S ⊗[R] Ω^{t+1}_{R/Λ}`; that image is generated
by the displayed scalar multiples of pure wedges.  The equality for two presentations makes the
trace canonical as a map attached to the extension `R → S`, rather than to a chosen generator or
polynomial presentation.

## References

* [Stacks Project, Tag 0AX5](https://stacks.math.columbia.edu/tag/0AX5)
-/
