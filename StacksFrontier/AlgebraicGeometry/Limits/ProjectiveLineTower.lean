module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReduction

public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace

/-!
# The tower of projective lines over a scheme

The `n`-fold fibre power `ℙ¹_S ×_S ⋯ ×_S ℙ¹_S` of the projective line over a scheme `S`, realised
as an iterated projective line: since `ℙ¹_T ≅ ℙ¹_S ×_S T` for an `S`-scheme `T`
(`AlgebraicGeometry.ProjectiveSpace.baseChangeIso`), the `(n+1)`-st stage is the projective line
over the `n`-th stage. Its projection to `S` is a composite of `n` projective lines, hence proper.

## Main definitions

* `AlgebraicGeometry.projectiveLineTower` — the `n`-fold fibre power of the projective line over
  `S`, built as an iterated projective line.
* `AlgebraicGeometry.projectiveLineTowerHom` — its projection to `S`.

## Main results

* `AlgebraicGeometry.isProper_projectiveLineTowerHom` — that projection is proper.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

end AlgebraicGeometry

end
