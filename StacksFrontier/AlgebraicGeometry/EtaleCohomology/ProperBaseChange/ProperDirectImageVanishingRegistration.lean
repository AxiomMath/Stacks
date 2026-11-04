module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 095U: higher direct images along a proper morphism vanish above twice the fibre dimension

Let `f : X ⟶ Y` be a proper morphism of schemes all of whose fibres have dimension at most `n`.
Then `R^q f_* F = 0` for every abelian torsion sheaf `F` on `X_étale` and every `q > 2n`.

The statement is `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper`,
proved without hypotheses beyond the tag's own. Its proof is the source's induction on `n`
(`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper_of_fiberDim`):
the case `n = 0` through [Stacks, Tag 02LS] and [Stacks, Tag 03QP]; for `n ≥ 1`, the reduction to
geometric fibres by the proper base change theorem ([Stacks, Tag 095T], proved as
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, via [Stacks, Tag 0DDF]),
then the dévissage of a proper scheme over an algebraically closed field down to the curve case,
which is statement (1) of [Stacks, Tag 03SC]
(`Stacks.EtaleCohomology.TorsionSheafSituation.isVanishingAboveDegreeTwo`, Tag 0A53).
-/

add_to_stacks 095U "f proper (Mathlib's IsProper, which implies quasi-compact) with every fibre \
  of topological Krull dimension at most n, F any abelian torsion sheaf on the small étale site \
  of X: R^q f_* F = 0 for all q > 2n"
  Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper
