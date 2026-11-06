module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.Definition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.TorsionSheafSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
import StacksCore.Tactic.StacksAttribute

/-!
# Statement (5) of Situation 0A52: finiteness of cohomology on a proper curve

Stacks Project Tag 0A52 fixes an algebraically closed field `k`, a separated finite-type scheme
`X` of dimension at most one over `k`, and a torsion abelian sheaf `F` on `X_étale`, and then
lists eight statements that one wants to prove for such data. The fifth of them is Tag 0A57:

> `H^q_étale(X, F)` is finite if `X` is proper and `F` constructible,

The source does not assert it; it names it, so that later results can say that it *holds* in a
given instance of the situation (Tag 0A5B for a smooth `X` and constant coefficients of prime
order, Tag 0A5C for an extension of sheaves, Tag 0GJA for a dense open, and so on). The faithful
formalization of such a statement is therefore a predicate on the data of Situation 0A52, and that is
what this file provides.

## Main definitions

* `Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf` is constructibility of an abelian
  sheaf on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`, obtained by
  transporting the library's `AlgebraicGeometry.IsConstructibleAbelianSheaf` — Tag 03RW (2),
  stated on the small étale site of Tag 021B — along the identification of the two sheaf
  categories.
* `Stacks.EtaleCohomology.TorsionSheafSituation.FiniteCohomologyOfIsProper` is Tag 0A57: in
  Situation 0A52, if the structure morphism of `X` is proper and `F` is constructible, then
  `H^q_étale(X, F)` is finite in every degree.

## Main results

* `AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat` and
  `AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_addCommGrpCat`: the two families of
  instances `AlgebraicGeometry.IsConstructibleAbelianSheaf` takes, at the coefficient universe
  `max (u + 1) v`, by instance search; for consumers in which that search is too slow.

## Implementation notes

**Why the ambient big étale site appears.** The source's `X_étale` is the small étale site of Tag
021B, which is defined relative to a chosen big étale site; the library records that choice as
`AlgebraicGeometry.BigEtaleSite` and states constructibility, Tag 03RW (2), over it. Mathlib's
`AlgebraicGeometry.Scheme.smallEtaleTopology` makes the opposite choice and takes all schemes
étale over `X`, which is the site `CategoryTheory.Sheaf.H` and the rest of this chapter — Tag
0A52 itself (`Stacks.EtaleCohomology.TorsionSheafSituation`) and the other seven statements
(`Stacks.EtaleCohomology.CurveCohomologyStatements`) — are stated on. The two sites have the same
sheaves: the embedding of the size-bounded one is a dense subsite inclusion,
`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`, whence the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`. `IsConstructibleEtaleAbelianSheaf` is
`AlgebraicGeometry.IsConstructibleAbelianSheaf` read through that equivalence, so the parameters
`B` and `hX` carry no mathematical hypothesis on the situation beyond the choice of ambient site
that the source has already made, and no second notion of constructibility is introduced.

Before this file the chapter had no constructibility predicate on Mathlib's small étale site at
all, which is why
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/FiniteDirectImage.lean`
states the eight statements of Situation 0A52 with constructibility as an abstract predicate
parameter, and why
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/DenseOpenRestriction.lean`
has to transfer that parameter between two sheaves as a hypothesis. Those two files remain as
they are; `Stacks.EtaleCohomology.CurveCohomologyStatements.finite_of_isProper` is the same
assertion as the definition below, with its `constructible` parameter left free, and so does not
carry the tag.

**The instance arguments.** `AlgebraicGeometry.IsConstructibleAbelianSheaf` takes two families of
instances: that the inverse-image functors on abelian sheaves of the small étale sites of Tag 021B
exist, and that the localized sites admit sheafification. At the coefficient universe
`max (u + 1) v` used here both are found by instance search (as in
`AlgebraicGeometry.isConstructibleAbelianEtaleSheaf_iff`), so the definitions below do not take
them. `CategoryTheory.HasExt` is what makes `CategoryTheory.Sheaf.H` — an `Ext` group out of the
constant sheaf `ℤ` — defined; it is a choice of universe, not a hypothesis on the situation.
Nothing is assumed on Mathlib's side of the equivalence: abelian sheaves there are Grothendieck
abelian for every scheme, by `Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale`, and
sheafification exists for every scheme, by `AlgebraicGeometry.hasSheafify_smallEtaleTopology`.

Finiteness is `Finite` on the underlying type of the cohomology group, and the coefficient
universe is `AddCommGrpCat.{max (u + 1) v}` for `X : Scheme.{u}`, the family of universes in
which étale cohomology of such a scheme is computed, as elsewhere in this chapter.

## References

* [Stacks Project, Tag 0A57](https://stacks.math.columbia.edu/tag/0A57)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

set_option synthInstance.maxHeartbeats 400000 in
/-- **The direct image of abelian sheaves between small étale sites is a right adjoint**, at the
coefficient universe `max (u + 1) v`: weak sheafification exists there
(`Stacks.ConstantSheaf.hasWeakSheafify_addCommGrp_of_univLE`), so the pullback is constructed by
left Kan extension followed by sheafification. -/
public theorem AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat
    (B : BigEtaleSite.{u}) :
    ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v}
        (AlgebraicGeometry.SmallEtale.topology B S.obj S.property)
        (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  fun _ _ _ ↦ inferInstance

/-- **The localizations of a small étale site admit weak sheafification with abelian
coefficients**, at the coefficient universe `max (u + 1) v`. -/
public theorem AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_addCommGrpCat
    (B : BigEtaleSite.{u}) :
    ∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
      HasWeakSheafify ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
        AddCommGrpCat.{max (u + 1) v} :=
  fun _ _ ↦ inferInstance

namespace Stacks.EtaleCohomology

/-- **Constructibility of an abelian sheaf on Mathlib's small étale site.** The library's
constructibility predicate for abelian sheaves, `AlgebraicGeometry.IsConstructibleAbelianSheaf`
of Tag 03RW (2), is stated on the small étale site of Tag 021B, which is cut out of all schemes
étale over `X` by the size bound of an ambient big étale site `B`. That inclusion is a dense
subsite inclusion, so the two sites have the same abelian sheaves
(`AlgebraicGeometry.SmallEtale.sheafEquiv`), and a sheaf on Mathlib's site is declared
constructible when its counterpart on the site of Tag 021B is. -/
def IsConstructibleEtaleAbelianSheaf (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : Prop :=
  @AlgebraicGeometry.IsConstructibleAbelianSheaf B (B.obj X hX)
    (AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, v} B)
    (AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, v} B)
    ((AlgebraicGeometry.SmallEtale.sheafEquiv B X hX
      AddCommGrpCat.{max (u + 1) v}).inverse.obj F)

/-- **Stacks Project, Tag 0A57**, statement (5) of Situation 0A52. For an algebraically closed
field `k`, a separated finite-type scheme `X` of dimension at most one over `k` and a torsion
abelian sheaf `F` on the small étale site of `X`: if the structure morphism of `X` is proper and
`F` is constructible, then `H^q_étale(X, F)` is finite for every `q`.

The source states this as one entry of the list of eight statements that Situation 0A52 asks
for, not as an assertion, so it is a predicate on the data of the situation. -/
@[stacks 0A57 "statement (5) of Situation 0A52, as a predicate on the situation"]
def TorsionSheafSituation.FiniteCohomologyOfIsProper (S : TorsionSheafSituation.{u, v})
    (B : BigEtaleSite.{u}) (hX : B.Contains S.X)
    [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] : Prop :=
  IsProper S.structureMorphism →
    IsConstructibleEtaleAbelianSheaf.{u, v} B S.X hX S.F →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.F q)

end Stacks.EtaleCohomology

end
