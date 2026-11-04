module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteLocallyConstantAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image of abelian sheaves between small étale sites is exact

Let `B` be a big étale site and `f : T ⟶ S` a morphism of its underlying category. Inverse image
of abelian sheaves along `AlgebraicGeometry.smallEtaleBaseChange` is left exact, and, being a left
adjoint, right exact. It therefore carries a short exact sequence of abelian sheaves on the small
étale site of `S` to a short exact sequence on that of `T`.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp`: inverse image of
  abelian sheaves between small étale sites is left exact.
* `AlgebraicGeometry.shortExact_map_smallEtaleSheafPullback_addCommGrp`: it carries short exact
  sequences to short exact sequences.

## References

* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.hasSheafify_addCommGrp

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The left Kan extension along the opposite of small étale base change is left exact, for
abelian coefficients in `AddCommGrpCat.{max (u + 1) w}`. -/
public theorem preservesFiniteLimits_lan_op_smallEtaleBaseChange :
    PreservesFiniteLimits ((smallEtaleBaseChange B f).op.lan :
      ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) w}) ⥤ _) := by
  refine Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun X => ?_
  have : IsFiltered (CostructuredArrow (smallEtaleBaseChange B f).op X) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange B f) (Opposite.unop X))
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) w, max (u + 1) w, u, u + 1} _
  infer_instance

attribute [local instance] preservesFiniteLimits_lan_op_smallEtaleBaseChange

/-- **Inverse image of abelian sheaves between small étale sites is left exact.** -/
@[sga "4½ Arcata 2.3.3" "partial", sga "5 VI 2.1" "left exactness of f*"]
public theorem preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp :
    PreservesFiniteLimits ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{max (u + 1) w}
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Inverse image of abelian sheaves between small étale sites preserves finite colimits. -/
public theorem preservesFiniteColimits_smallEtaleSheafPullback_addCommGrp :
    PreservesFiniteColimits ((smallEtaleBaseChange B f).sheafPullback
      AddCommGrpCat.{max (u + 1) w}
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)) :=
  let : ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{max (u + 1) w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsLeftAdjoint :=
    (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange B f)
      AddCommGrpCat.{max (u + 1) w} (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).isLeftAdjoint
  inferInstance

/-- Inverse image of abelian sheaves between small étale sites is additive. -/
public theorem additive_smallEtaleSheafPullback_addCommGrp :
    ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{max (u + 1) w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp
  preservesFiniteColimits_smallEtaleSheafPullback_addCommGrp
  additive_smallEtaleSheafPullback_addCommGrp

/-- **Inverse image carries a short exact sequence of abelian étale sheaves to a short exact
sequence.** -/
@[sga "4½ Arcata 2.3.3", sga "5 VI 2.1" "more general"]
public theorem shortExact_map_smallEtaleSheafPullback_addCommGrp
    {C : ShortComplex (Sheaf (SmallEtale.topology B S.obj S.property)
      AddCommGrpCat.{max (u + 1) w})} (hC : C.ShortExact) :
    (C.map ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{max (u + 1) w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property))).ShortExact :=
  hC.map_of_exact _

end AlgebraicGeometry

end
