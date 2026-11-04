module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceCoreProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundAffineLineReduction

/-!
# The curve case of Weil II on opens of the affine line from the purity of the Fourier family

The weight bound of Weil II for affine opens of `𝔸¹`
(`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine`) holds whenever the two-parameter Fourier
family is pure of weight `β + 1` off a curve (`Stacks.EtaleCohomology.LaumonFibrePurityInput`) and
this purity bounds the weights on `H¹_c(𝔸¹, ℱ_σ)`
(`Stacks.EtaleCohomology.LaumonFibreDegenerationInput`).

## Main results

* `Stacks.EtaleCohomology.weilIICurveBoundOpenAffineLine_of_fibrePurity`: the purity of the Fourier
  family and the resulting bound on `H¹_c(𝔸¹, ℱ_σ)` imply the weight bound of Weil II for affine
  opens of `𝔸¹`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.EtaleCohomology

/-- **The curve case of Weil II on affine opens of the affine line**: if the two-parameter Fourier
family is pure of weight `β + 1` off a curve (`Stacks.EtaleCohomology.LaumonFibrePurityInput`) and
this purity bounds the weights on `H¹_c(𝔸¹, ℱ_σ)`
(`Stacks.EtaleCohomology.LaumonFibreDegenerationInput`), then
`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine` holds. -/
public theorem weilIICurveBoundOpenAffineLine_of_fibrePurity (h7 : LaumonFibrePurityInput.{u})
    (h8 : LaumonFibreDegenerationInput.{u}) : WeilIICurveBoundOpenAffineLine.{u} :=
  weilIICurveBoundOpenAffineLine_of_laumonAffineLine curveTraceFormulaInput curveCoinvariantsInput
    (laumonAffineLineInput_of_fibrePurity h7 h8)

end Stacks.EtaleCohomology

end
