module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterionUnconditional

/-!
# The stalk of an abelian étale sheaf on the size-bounded small étale site, on germs

For an abelian sheaf `F` on the small étale site of `X` and a geometric point `t`, the stalk at `t`
(Tag 040R) of the restriction of `F` to the size-bounded small étale site of a big étale site
containing `X` is the stalk of `F` at `t` on the small étale site
(`AlgebraicGeometry.etaleStalkIsoSmallEtaleStalkAb`): the étale neighbourhoods inside the
size-bounded site are initial among all étale neighbourhoods
(`AlgebraicGeometry.initial_neighborhoodInclusion`). This file records that identification on
germs.

## Main results

* `AlgebraicGeometry.ι_etaleStalkIsoSmallEtaleStalkAb_hom` — the identification
  `AlgebraicGeometry.etaleStalkIsoSmallEtaleStalkAb` on germs.

## References

* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Torsion Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)

/-- The identification of the two stalks carries the germ at an étale neighbourhood `(U, x)` of
`t` inside the size-bounded site to the germ at the same neighbourhood on the small étale site. -/
@[reassoc]
theorem ι_etaleStalkIsoSmallEtaleStalkAb_hom (t : GeometricPoint X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : SmallEtale B X hX)
    (x : (geometricPointFiber B X hX t).obj U) :
    colimit.ι ((Functor.Elements.π (geometricPointFiber B X hX t)).op ⋙
        (((SmallEtale.toEtaleSite B X hX).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X hX) X.smallEtaleTopology).obj F).obj)
        (op ((geometricPointFiber B X hX t).elementsMk U x)) ≫
        (etaleStalkIsoSmallEtaleStalkAb B hX t F).hom =
      (Scheme.pointSmallEtale t.hom).toPresheafFiber ((SmallEtale.toEtaleSite B X hX).obj U)
        (Over.homMk x.1 x.2) F.obj :=
  Functor.Final.ι_colimitIso_hom (neighborhoodInclusionPublic B X hX t).op
    ((Functor.Elements.π (Scheme.pointSmallEtale t.hom).fiber).op ⋙ F.obj)
    (op ((geometricPointFiber B X hX t).elementsMk U x))

end AlgebraicGeometry

end
