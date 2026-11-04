module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Statement (2) of Situation 0A52: vanishing above degree one on an affine scheme

Let `X` be a scheme and `F` an abelian sheaf on the small étale site of `X`. Statement (2) of
the list in Situation 0A52 is

> `H^q_étale(X, F) = 0` for `q > 1` if `X` is affine,

and this file states it as a predicate on `F`, with vanishing expressed as `Subsingleton` of
`CategoryTheory.Sheaf.H`.

## Main definitions

* `Stacks.EtaleCohomology.IsAffineVanishingAboveDegreeOne` is statement (2): if `X` is affine then
  the étale cohomology of `F` vanishes in every degree greater than one.

## Main results

* `Stacks.EtaleCohomology.IsAffineVanishingAboveDegreeOne.subsingleton` and
  `Stacks.EtaleCohomology.isAffineVanishingAboveDegreeOne_of_subsingleton` are the elimination and
  the introduction rule.
* `Stacks.EtaleCohomology.isAffineVanishingAboveDegreeOne_of_not_isAffine`: the statement holds
  for every `F` when `X` is not affine.

## References

* [Stacks Project, Tag 0A54](https://stacks.math.columbia.edu/tag/0A54)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Statement (2) of the list of Situation 0A52: the étale cohomology `H^q_étale(X, F)` vanishes
for every `q > 1` if `X` is affine. -/
@[stacks 0A54 "item (2) of 0A52: H^q(X, F) = 0 for q > 1 if X is affine"]
def IsAffineVanishingAboveDegreeOne
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : Prop :=
  IsAffine X → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} F q)

/-- Statement (2) of Situation 0A52 applied: on an affine scheme the étale cohomology of `F`
vanishes above degree one. -/
theorem IsAffineVanishingAboveDegreeOne.subsingleton
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (h : IsAffineVanishingAboveDegreeOne.{u, v, w} F) [IsAffine X] {q : ℕ} (hq : 1 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  h ‹IsAffine X› q hq

/-- Vanishing of the étale cohomology of `F` above degree one, with no use of the affineness of
`X`, gives statement (2) of Situation 0A52. -/
theorem isAffineVanishingAboveDegreeOne_of_subsingleton
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} F q)) :
    IsAffineVanishingAboveDegreeOne.{u, v, w} F :=
  fun _ ↦ h

/-- Statement (2) of Situation 0A52 holds for every `F` when `X` is not affine. -/
theorem isAffineVanishingAboveDegreeOne_of_not_isAffine
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (hX : ¬ IsAffine X) :
    IsAffineVanishingAboveDegreeOne.{u, v, w} F :=
  fun hX' ↦ absurd hX' hX

end Stacks.EtaleCohomology

end
