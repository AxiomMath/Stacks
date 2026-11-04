module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonLeray
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonOnCartesianObjects

/-!
# The 0GZS condition is local over the objects of the site

Let `C` carry a Grothendieck topology `τ`, let `O` be a `τ`-sheaf of rings with commuting
sections and let `ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')` be the comparison with the chaotic topology.
An object `K` of `D(C_τ, O_τ)` satisfies the condition of Stacks 0GZS — `Rε_*K` has cartesian
derived sections — exactly when, for every object `U` of `C`, its restriction to the localized
site `C/U` satisfies the same condition there.

The condition on `Rε_*K` only involves pairs of objects `U' → U`, which already live in `C/U`;
restriction commutes with `Rε_*` (Stacks 0D6G for `ε`,
`Stacks.ModulesOnACategory.ChaoticComparison.derivedRestrictionPushforwardIso`), and cartesian
derived sections are local over the objects of `C`
(`Stacks.ModulesOnACategory.MorphismsOverAnObject.isQC_of_forall_isQC_derivedRestriction`).

## Main results

* `Stacks.ModulesOnACategory.ChaoticComparison.isCartesianPushforward_iff_forall_restriction`:
  `Rε_*K` has cartesian derived sections exactly when, for every object `U`, so does the derived
  pushforward of the restriction of `K` to `C/U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

namespace Stacks.ModulesOnACategory.ChaoticComparison

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

/-- **The condition of Stacks 0GZS is local over the objects of `C`.** `Rε_*K` has cartesian
derived sections exactly when, for every object `U`, the derived pushforward of the restriction
of `K` to `C/U` has cartesian derived sections on `C/U`. -/
theorem isCartesianPushforward_iff_forall_restriction
    (K : DerivedCategory (SheafOfModules.{max u v r w} R)) :
    IsCartesianPushforward.{w} R (baseChangeDataOfComm.{r, v, u, w} R.obj hO) K ↔
      ∀ U : C, IsCartesianPushforward.{w} (overRingSheaf R U)
        (baseChangeDataOfComm.{r, v, max u v, w} (overRingPresheaf R.obj U)
          (comm_overRingPresheaf R.obj U hO))
        ((sheafRestriction.{w} R U).mapDerivedCategory.obj K) := by
  have key (U : C) := ObjectProperty.prop_iff_of_iso
    (IsQC.{w} (baseChangeDataOfComm.{r, v, max u v, w} (overRingPresheaf R.obj U)
      (comm_overRingPresheaf R.obj U hO))) ((derivedRestrictionPushforwardIso.{w} R U).app K)
  refine ⟨fun hK U => (key U).mp (isQC_derivedRestriction.{w} R.obj U _ _ _ hK), fun hK => ?_⟩
  exact isQC_of_forall_isQC_derivedRestriction.{w} R.obj _
    (fun U ↦ baseChangeDataOfComm.{r, v, max u v, w} (overRingPresheaf R.obj U)
      (comm_overRingPresheaf R.obj U hO)) _ fun U ↦ (key U).mpr (hK U)

end Stacks.ModulesOnACategory.ChaoticComparison

end
