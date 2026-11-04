module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image of module sheaves between small étale sites is exact

Let `B` be a big étale site, `f : T ⟶ S` a morphism of its underlying category, and `Λ` a ring.
Inverse image of sheaves of `Λ`-modules along `AlgebraicGeometry.smallEtaleBaseChange` is a left
adjoint, so it is right exact for free. This file proves it is left exact as well, hence exact,
and records that it is additive.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat`: inverse image of
  module sheaves between small étale sites is left exact.
* `AlgebraicGeometry.preservesFiniteColimits_smallEtaleSheafPullback_moduleCat`: it is right
  exact.
* `AlgebraicGeometry.additive_smallEtaleSheafPullback_moduleCat`: it is additive.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (Λ : Type r) [Ring Λ]

/-- The left Kan extension along the opposite of small étale base change is left exact, for
coefficients in `ModuleCat.{max (u + 1) w} Λ`. -/
public theorem preservesFiniteLimits_lan_op_smallEtaleBaseChange_moduleCat :
    PreservesFiniteLimits ((smallEtaleBaseChange B f).op.lan :
      ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) w} Λ) ⥤ _) := by
  refine Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun X => ?_
  have : IsFiltered (CostructuredArrow (smallEtaleBaseChange B f).op X) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange B f) (Opposite.unop X))
  have : PreservesColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) w, r, u, u + 1} Λ
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) w, max (u + 1) w, u, u + 1} _
  exact inferInstanceAs (PreservesColimitsOfShape
    (CostructuredArrow (smallEtaleBaseChange B f).op X)
    (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w} ⋙
      forget AddCommGrpCat.{max (u + 1) w}))

attribute [local instance] preservesFiniteLimits_lan_op_smallEtaleBaseChange_moduleCat

variable
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- Inverse image of module sheaves between small étale sites preserves finite colimits. -/
public theorem preservesFiniteColimits_smallEtaleSheafPullback_moduleCat :
    PreservesFiniteColimits ((smallEtaleBaseChange B f).sheafPullback
      (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)) :=
  let : ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsLeftAdjoint :=
    (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange B f)
      (ModuleCat.{max (u + 1) w} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).isLeftAdjoint
  inferInstance

variable
  [HasSheafify (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ)]
  [HasSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) w} Λ)]

/-- **Inverse image of module sheaves between small étale sites is left exact.** -/
@[sga "4½ Arcata 2.3.3" "partial"]
public theorem preservesFiniteLimits_smallEtaleSheafPullback_moduleCat :
    PreservesFiniteLimits ((smallEtaleBaseChange B f).sheafPullback
      (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

attribute [local instance] preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  preservesFiniteColimits_smallEtaleSheafPullback_moduleCat

/-- Inverse image of module sheaves between small étale sites is additive. -/
public theorem additive_smallEtaleSheafPullback_moduleCat :
    ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).Additive :=
  Functor.additive_of_preserves_binary_products _

end AlgebraicGeometry

end
