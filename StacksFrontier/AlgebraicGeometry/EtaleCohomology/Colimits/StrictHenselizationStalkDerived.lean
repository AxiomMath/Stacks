module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.StrictHenselizationInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers

/-!
# Inverse images of injective sheaves to the strict henselization are acyclic

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, `s` a geometric point of `Y` and
`p : X ×_Y Spec 𝒪^{sh}_{Y,s} ⟶ X` the projection. For an injective abelian sheaf `I` on
`X_étale`, the sheaf `p⁻¹I` is acyclic for global sections: its cohomology in positive degrees
vanishes by Stacks 09YQ
(`Stacks.EtaleCohomology.LimitExt.subsingleton_H_strictHenselization_of_injective`). This is the
acyclicity input of Stacks 03Q9 in positive degrees
(`Stacks.EtaleCohomology.LimitExt.isIso_derivedPushforwardStalk_single_of_injective`).

## Main results

* `Stacks.EtaleCohomology.LimitExt.rightAcyclic_strictHenselizationPullback_of_injective`.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace Stacks.EtaleCohomology.LimitExt

/-- **The inverse image of an injective sheaf to the strict henselization is acyclic for global
sections**, for `f` quasi-compact and quasi-separated. -/
theorem rightAcyclic_strictHenselizationPullback_of_injective (B : BigEtaleSite.{u})
    {X Y : Scheme.{u}} (hY : B.Contains Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (s : GeometricPoint Y) (I : Sheaf (smallEtaleTopology X) Ab.{u + 1}) [Injective I] :
    (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hY f s)) Ab.{u + 1}).rightAcyclic
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)).obj I) := by
  let Z := strictHenselizationBaseChange B hY f s
  have : EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives Z
  have : IsGrothendieckAbelian.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Z
  rw [rightAcyclic_iff_isZero_rightDerived]
  intro q hq
  rw [← Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}]
  exact (subsingleton_H_iff_of_iso ((Functor.sheafPullbackConstruction.sheafPullbackIso
    (smallEtaleBaseChange (strictHenselizationBaseChangeToSource B hY f s)) AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (smallEtaleTopology Z)).app I) q).2
    (subsingleton_H_strictHenselization_of_injective B hY f s I q hq)

end Stacks.EtaleCohomology.LimitExt
