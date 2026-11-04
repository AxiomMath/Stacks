module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# The stalk of a higher direct image at a geometric point, as a vanishing criterion

For a quasi-compact and quasi-separated morphism `f : X ⟶ S`, a geometric point `s` of `S` and an
abelian sheaf `𝓕` on `X_étale`, the stalk of `R^q f_* 𝓕` at `s` is the étale cohomology of the
base change of `X` to the strict henselization of `S` at `s` (Stacks 03Q9):

`(R^q f_* 𝓕)_s ≅ H^q(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹𝓕)`,

`p` being the projection to `X`. This file reads that isomorphism as a vanishing criterion, in the
vocabulary of the Mathlib small étale sites, which is the form in which the estimates on
cohomological dimension in this directory consume it.

## Main results

* `AlgebraicGeometry.isZero_stalk_rightDerived_iff_subsingleton_sheafH`: the stalk of
  `R^q f_* 𝓕` at `s` vanishes exactly when `H^q(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹𝓕)` does.

## Implementation notes

The isomorphism is the first assertion of Stacks 03Q9,
`Stacks.EtaleCohomology.stalkHigherDirectImageIsoStrictHenselization`, whose left side is the stalk
of the `q`-th cohomology sheaf of `Rf_*` applied to `𝓕` in degree zero; that sheaf is identified
with `R^q f_* 𝓕` by `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`. The derived
categories through which it passes are the standard models, the model it is stated with.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology AlgebraicGeometry.Scheme

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **The stalk formula for higher direct images, as a vanishing criterion** (Stacks 03Q9). For
`f : X ⟶ S` quasi-compact and quasi-separated with `S` in a big étale site `B`, a geometric point
`s` of `S` and an abelian sheaf `𝓕` on `X_étale`, the stalk at `s` of `R^q f_* 𝓕` vanishes exactly
when `H^q(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹𝓕)` does. -/
theorem isZero_stalk_rightDerived_iff_subsingleton_sheafH (B : BigEtaleSite.{u})
    {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (s : GeometricPoint S) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (q : ℕ) :
    IsZero ((smallEtaleStalkAb s.hom).obj (((smallEtalePushforwardAb f).rightDerived q).obj F)) ↔
      Subsingleton (Sheaf.H.{u + 1, u + 1}
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) q) := by
  let := HasDerivedCategory.standard (Sheaf (smallEtaleTopology X) Ab.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (smallEtaleTopology S) Ab.{u + 1})
  let e := (smallEtaleStalkAb s.hom).mapIso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (smallEtalePushforwardAb f)
        (smallEtaleDerivedPushforwardAb f) (smallEtaleDerivedPushforwardAbUnit f)
        (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2}) F q).symm ≪≫
    Stacks.EtaleCohomology.stalkHigherDirectImageIsoStrictHenselization B hS f s F q
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}]
  exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

end AlgebraicGeometry

end
