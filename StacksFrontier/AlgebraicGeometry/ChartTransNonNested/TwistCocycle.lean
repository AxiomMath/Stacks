module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.PushforwardCocycle
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.NestedCocycleReduction
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistCocycleSections
public import StacksFrontier.AlgebraicGeometry.NestedCocycleReduction.Basic

/-!
# The nested cocycle from the cocycle for Tag 01NO's twist isomorphism

`Stacks.AlgebraicGeometry.ChartTransRelativeProj.isNestedCocycle_of_pushNested_comp` reduces
`IsNestedCocycle A n` — the one hypothesis the glued twist of Tag 01NR, and hence the twist
`𝒪_{𝐏(E)}(1)` of Tag 01VM, is conditional on — to the single equation

`pushNested A W' U ≫ pushNested A W W' = pushNested A W U`

between morphisms of sheaves of modules on the relative Proj. This file reduces **that** to the
cocycle condition on Tag 01NO's canonical twist isomorphism
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso` alone, which is the third
assertion of Stacks Tag 01MZ and the only mathematics left in the chain: no pushforward, no chart,
no open of the relative Proj and no section occurs in it.

## Main results

* `…ChartTransRelativeProj.projInclusionMap_comp'`: Tag 01NP's transitivity of the transition
  morphisms, with the containment of the outer pair of affine opens a free argument.
* `…ChartTransRelativeProj.pushNested_comp_aux`: the composition law for the two factors
  separately, which is `…PushforwardCocycle.pushComparison_comp_of` at the chart data.
* `…ChartTransRelativeProj.pushNested_comp_of`: **the equation the reduction asks for.** Its one
  hypothesis is the cocycle condition on Tag 01NO's canonical twist isomorphisms, in which no
  pushforward, no chart, no open of the relative Proj and no section occurs — the third assertion
  of Stacks Tag 01MZ for the restriction maps of a quasi-coherent graded algebra.

## Implementation notes

**No reducibility attribute is set here, and that is what makes the file possible.** The sibling
files in this directory open with
`attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj`. With those
attributes the single step `pushNested = pushNestedUnit ≫ pushNestedTail.hom` exceeds the
**kernel's** deterministic timeout; without them it checks in about seventy-five seconds.

**Each identification is a separate declaration, and the comparison is never identified in one
step.** Asking for `pushNested A W U h hW hU n = pushComparison …` by `rfl` exceeds the
elaborator's budget however the reducibility attributes are set, so the unit factor, the tail and
their composite are identified separately —
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedUnit_app_apply` and `pushNestedTail_eq`
from the sibling `TwistCocycleSections.lean` for the first two, and
`Stacks.AlgebraicGeometry.NestedCocycleReduction.pushNested_eq` for the third. For the same
reason `pushNested_comp_aux` is split off from `pushNested_comp_of`: the
application of `…PushforwardCocycle.pushComparison_comp_of`, with its twenty-six explicit
arguments at this instance, needs a heartbeat budget of its own.

Every containment proof is a free argument, as in `IsNestedCocycle`. `projInclusionMap_comp'`
exists only to restate Tag 01NP's transitivity with the containment of the outer pair free; the
two statements are definitionally equal by proof irrelevance.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)

## Not done here

No tag is claimed. The cocycle condition on Tag 01NO's twist isomorphisms is a hypothesis of
`pushNested_comp_of`; it is Tag 01MZ's third assertion for the restriction maps of a
quasi-coherent graded algebra, and it is not proved in this file.

The hypothesis is **not** packaged as a named predicate quantified over all triples of nested
affine opens: a declaration whose hypothesis is such a predicate, or
which feeds `pushNested_comp_of` into
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.isNestedCocycle_of_pushNested_comp`, exceeds the
elaborator's deterministic budget at `whnf` in each of five spellings, including the predicate
as a `def` and as an `abbrev`, the application in term mode and after `intro`, and the triple
supplied before and after the degree. A consumer wanting `IsNestedCocycle A n` should therefore
apply `isNestedCocycle_of_pushNested_comp` to a `fun` built from `pushNested_comp_of` at its own
call site, where the surrounding declaration is small.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.PushforwardCocycle

namespace Stacks.AlgebraicGeometry.ChartTransRelativeProj

open Stacks.AlgebraicGeometry.NestedCocycleReduction (pushNested_eq)

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### Tag 01NO's comparison as the variable-level pushed-forward comparison -/

section Nested

variable (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W) (hU : IsAffineOpen U) (n : ℤ)

end Nested

/-! ### The cocycle condition on Tag 01NO's twist isomorphism -/

/-- **Tag 01NP's transitivity of the transition morphisms**, with the containment of the outer
pair of affine opens a free argument. Definitionally the same statement as
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.projInclusionMap_comp`, by proof irrelevance. -/
public theorem projInclusionMap_comp' (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U)
    (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U) :
    projInclusionMap A W W' hWW' hW hW' ≫ projInclusionMap A W' U hW'U hW' hU
      = projInclusionMap A W U hWU hW hU :=
  RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU

/-- **The equation the nested cocycle reduces to, from the cocycle for Tag 01NO's twist
isomorphism.** The three pushed-forward comparisons compose because the three twist isomorphisms
do; every structural factor is handled at the level of variables in
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/PushforwardCocycle.lean`. -/
public theorem pushNested_comp_aux (n : ℤ) (W W' U : S.Opens)
    (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (hU : IsAffineOpen U)
    (hcoc : (Scheme.Modules.pullbackCongr
            (projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullbackComp (projInclusionMap A W W' hWW' hW hW')
            (projInclusionMap A W' U hW'U hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullback (projInclusionMap A W W' hWW' hW hW')).map
          (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n).hom ≫
        (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n).hom =
      (ProjInclusionTwist.projInclusionTwistIso A W U hWU hW hU n).hom) :
    (pushNestedUnit A W' U hW'U hW' hU n ≫ (pushNestedTail A W' U hW'U hW' hU n).hom) ≫
        (pushNestedUnit A W W' hWW' hW hW' n ≫ (pushNestedTail A W W' hWW' hW hW' n).hom) =
      pushNestedUnit A W U hWU hW hU n ≫ (pushNestedTail A W U hWU hW hU n).hom :=
  pushComparison_comp_of ((relativeProj A).chart U hU)
    ((relativeProj A).chart W' hW') ((relativeProj A).chart W hW)
    (projInclusionMap A W W' hWW' hW hW') (projInclusionMap A W' U hW'U hW' hU)
    (projInclusionMap A W U hWU hW hU)
    (projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU)
    ((relativeProj A).chart_transition W' U hW'U hW' hU)
    ((relativeProj A).chart_transition W W' hWW' hW hW')
    ((relativeProj A).chart_transition W U hWU hW hU)
    (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
    (twistingSheaf (A.grading W) n)
    (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n)
    (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n)
    (ProjInclusionTwist.projInclusionTwistIso A W U hWU hW hU n)
    (pushNestedUnit A W' U hW'U hW' hU n) (pushNestedUnit A W W' hWW' hW hW' n)
    (pushNestedUnit A W U hWU hW hU n)
    (pushNestedTail A W' U hW'U hW' hU n) (pushNestedTail A W W' hWW' hW hW' n)
    (pushNestedTail A W U hWU hW hU n)
    (pushNestedUnit_app_apply A W' U hW'U hW' hU n)
    (pushNestedUnit_app_apply A W W' hWW' hW hW' n)
    (pushNestedUnit_app_apply A W U hWU hW hU n)
    ((pushNestedTail_eq A W' U hW'U hW' hU n).trans
      (pushComparisonTail_eq (projInclusionMap A W' U hW'U hW' hU)
        ((relativeProj A).chart U hU)
        ((relativeProj A).chart_transition W' U hW'U hW' hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
        (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n)).symm)
    ((pushNestedTail_eq A W W' hWW' hW hW' n).trans
      (pushComparisonTail_eq (projInclusionMap A W W' hWW' hW hW')
        ((relativeProj A).chart W' hW')
        ((relativeProj A).chart_transition W W' hWW' hW hW')
        (twistingSheaf (A.grading W') n) (twistingSheaf (A.grading W) n)
        (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n)).symm)
    ((pushNestedTail_eq A W U hWU hW hU n).trans
      (pushComparisonTail_eq (projInclusionMap A W U hWU hW hU)
        ((relativeProj A).chart U hU)
        ((relativeProj A).chart_transition W U hWU hW hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W) n)
        (ProjInclusionTwist.projInclusionTwistIso A W U hWU hW hU n)).symm)
    hcoc

/-- **The equation the nested cocycle reduces to, from the cocycle for Tag 01NO's twist
isomorphism.** The three pushed-forward comparisons compose because the three twist isomorphisms
do; every structural factor is handled at the level of variables in
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/PushforwardCocycle.lean`. -/
public theorem pushNested_comp_of (n : ℤ) (W W' U : S.Opens)
    (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
    (hU : IsAffineOpen U)
    (hcoc : (Scheme.Modules.pullbackCongr
            (projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullbackComp (projInclusionMap A W W' hWW' hW hW')
            (projInclusionMap A W' U hW'U hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullback (projInclusionMap A W W' hWW' hW hW')).map
          (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n).hom ≫
        (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n).hom =
      (ProjInclusionTwist.projInclusionTwistIso A W U hWU hW hU n).hom) :
    pushNested A W' U hW'U hW' hU n ≫ pushNested A W W' hWW' hW hW' n
      = pushNested A W U hWU hW hU n := by
  refine Eq.trans (eq_whisker (pushNested_eq A W' U hW'U hW' hU n) _) ?_
  refine Eq.trans (whisker_eq _
    (pushNested_eq A W W' hWW' hW hW' n)) ?_
  refine Eq.trans (pushNested_comp_aux A n W W' U hWW' hW'U hWU hW hW' hU hcoc) ?_
  exact (pushNested_eq A W U hWU hW hU n).symm

end Stacks.AlgebraicGeometry.ChartTransRelativeProj

end
