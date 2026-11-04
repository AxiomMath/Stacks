module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiberUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Stalks of abelian étale sheaves on the size-bounded small étale site

For an abelian sheaf `F` on the small étale site of a scheme `X` and a geometric point `t` of `X`,
the stalk at `t` of the restriction of `F` to the size-bounded small étale site of a big étale site
containing `X` is identified with the stalk of `F` at `t` on the small étale site.

## Main definitions

* `AlgebraicGeometry.etaleStalkIsoSmallEtaleStalkAb`: the identification of the two stalks.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Torsion Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)

/-- **The two stalks of an abelian étale sheaf agree.** For an abelian sheaf `F` on the small étale
site of `X` and a geometric point `t`, the stalk at `t` (Tag 040R) of the restriction of `F` to the
size-bounded small étale site of a big étale site containing `X` is the stalk of `F` at `t` on the
small étale site.

Both are colimits of the sections of `F` over étale neighbourhoods of `t`, the first over those
inside the size-bounded site and the second over all of them, and the first family is initial in
the second (`AlgebraicGeometry.initial_neighborhoodInclusion`). The identification is the
comparison of colimits along the inclusion of neighbourhoods, and carries the germ at a
neighbourhood to the germ at the same neighbourhood
(`AlgebraicGeometry.ι_etaleStalkIsoSmallEtaleStalkAb_hom`). -/
def etaleStalkIsoSmallEtaleStalkAb (t : GeometricPoint X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    etaleStalk B X hX t (((SmallEtale.toEtaleSite B X hX).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallEtale.topology B X hX) X.smallEtaleTopology).obj F).obj ≅
      (smallEtaleStalkAb t.hom).obj F :=
  Functor.Final.colimitIso (neighborhoodInclusionPublic B X hX t).op
    ((CategoryOfElements.π (Scheme.pointSmallEtale t.hom).fiber).op ⋙ F.obj)

end AlgebraicGeometry

end
