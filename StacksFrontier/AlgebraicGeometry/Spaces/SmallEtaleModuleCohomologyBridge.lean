module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections

/-!
# From abelian sheaf cohomology to module-valued derived sections on a space's small étale site

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Cohomology on
its small étale site is `CategoryTheory.Sheaf.H'`, and every criterion in this tree that produces
a vanishing of it — the Čech criterion of [Stacks, Tag 03F9] among them — needs the category of
abelian sheaves on the site to have enough injectives, and needs `Ext` groups to exist there.
Both are proved, at the coefficient universe `u` of the schemes, in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartCohomologyVanishing.lean`:
`AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale` and
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale`, with their projection-spelling companions
`AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtaleRingedSite` and
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtaleRingedSite`, and the module pair
`AlgebraicGeometry.Space.enoughInjectives_modules` and `AlgebraicGeometry.Space.hasExt_modules`.
They are declared there as `local` instances, so they are instances nowhere else; files that
need them arm them with `attribute [local instance]`.

This file crosses from abelian sheaf cohomology to the module-valued derived sections over an
object, which is the shape every quasi-coherent consumer in this tree asks for.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isZero_rightDerived_moduleEvaluation_of_isZero_H'`:
  **vanishing of `H^{p+1}(U, Mᵃ)` forces vanishing of the right derived module sections of `M`
  over `U`**, with every instance hypothesis of the general comparison discharged.
* `AlgebraicGeometry.Space.SmallEtale.isZero_rightDerived_moduleEvaluation_of_isZero_H'_chgUniv`:
  the same from a vanishing measured at any other `Ext` universe, which is the form the
  Čech-theoretic results supply.
* `AlgebraicGeometry.Space.SmallEtale.chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H'`:
  the chart-indexed packaging, which is exactly the hypothesis named `h03DW` at the binder sites
  of this tree.

## Implementation notes

The general comparison is
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FppfEtaleComparison/ModuleHigherVanishing.lean`),
which takes its topology and sheaf of rings as *explicit* arguments and so needs no restating.
Three things have to be right for it to apply at the small étale site of an algebraic space,
whose objects lie in `Type (u + 1)` while its morphisms, structure rings and modules all lie
in `Type u`.

* The `Ext` universe must be written `u + 1`, **not** `max (u + 1) u`.  The two are the same
  universe, but instance search matches a carried `HasExt` only against the normalised form;
  given the `max` form it ignores the hypothesis and re-derives `HasExt` from scratch until the
  `synthInstance` heartbeat limit, reporting `failed to synthesize … HasSmallLocalizedHom`.
* The carried `HasExt` and `EnoughInjectives` must sit at the **projection** spelling
  `(smallEtaleRingedSite … ).J`, which is the topology the sheaf
  `(SheafOfModules.toSheaf (RingedSite.ringSheaf …)).obj M` of the hypothesis actually lives on.
  `enoughInjectives_sheaf_smallEtale` and `hasExt_sheaf_smallEtale` are stated at the reduced
  spelling `SmallEtale.topology`, so they must be introduced through a type *ascription* at the
  projection spelling: instance search unfolds neither the projection nor the `def`
  `AlgebraicGeometry.Space.smallEtaleRingedSite`, while the ascription is checked at default
  transparency and goes through.
* `attribute [local instance 5000] SheafOfModules.instAbelian` is required, and is the whole of
  what used to be recorded here as an irreducible universe clash on the module side.  No
  universe constraint has to be relaxed.  The tree's own global instance
  `Stacks.Cohomology.SiteModules.moduleSheavesAbelian`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean`) states
  `Abelian (SheafOfModules.{max u v r w} O)` for a site with objects in `Type u` and morphisms
  in `Type v`; being declared after Mathlib's `SheafOfModules.instAbelian` at the same priority
  it is tried first, and it pins the module universe to `max (u + 1) u ?w`, which is at least
  `u + 1` and so can never be the `u` this site's modules live in.  Instance search then
  reports `stuck at solving universe constraint  max (u + 1) ?w =?= u`, and the same instance
  blocks `EnoughInjectives`, `HasInjectiveResolutions` and `IsGrothendieckAbelian` downstream of
  it.  Raising `SheafOfModules.instAbelian` above it is what nineteen other modules of this tree
  do, among them `StacksFrontier/AlgebraicGeometry/Spaces/ModulesGlobalSections.lean` and
  `StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishing.lean`, and with it in
  force the module universe stays pinned at `u` *and* the abelian-sheaf `Ext` datum may sit in
  the same statement.

The two sheafification instances at the unsliced projection spelling that this file used to
restate are `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`, imported here; the copies carried
here were verbatim duplicates of those, down to the `change`-then-`infer_instance` proof, and
are gone.

No `@[stacks]` attribute is claimed.  Nothing here proves a vanishing: every result below turns
a vanishing of abelian sheaf cohomology into a vanishing of module-valued cohomology.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### From abelian sheaf cohomology to the module-valued derived sections -/

section Bridge

open Stacks.Cohomology.ModuleDirectImageOnACover

variable (hF : IsAlgebraicSpace B S hS F)

/-- **Vanishing of the abelian sheaf cohomology of `Mᵃ` over an étale chart `U` forces vanishing
of the right derived module sections of `M` over `U`.**

This is
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'` on the
small étale site of `F`, with all six of its instance hypotheses discharged: the two
sheafification instances from `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, the
abelian-sheaf pair `AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale` and
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale`, and the module pair
`AlgebraicGeometry.Space.enoughInjectives_modules` and `AlgebraicGeometry.Space.hasExt_modules`.
The `Ext` universe is `u + 1`, the morphism universe of both sheaf categories here; the degree is
written as a successor, which is the form the comparison takes. -/
theorem isZero_rightDerived_moduleEvaluation_of_isZero_H' (U : SmallEtale B S hS F) (p : ℕ)
    (M : Modules.{u, u} B S hS F hF) :
    have : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
      hasExt_sheaf_smallEtale B S hS F
    have := enoughInjectives_modules B S hS F hF
    IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf.{u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M) (p + 1) U) →
      IsZero (((SheafOfModules.evaluation
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (op U)).rightDerived (p + 1)).obj M) := by
  intro _ _ h
  have : EnoughInjectives (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
    enoughInjectives_sheaf_smallEtale B S hS F
  have := hasExt_modules B S hS F hF
  exact isZero_rightDerived_evaluation_of_isZero_H'
    (smallEtaleRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O) U p M h

/-- **The same bridge from a vanishing measured at any other `Ext` universe.**  This is the form
the Čech-theoretic vanishing results of this tree supply, their `Ext` universe being the
morphism universe of the site rather than the one enlarged by its objects; the choice is
immaterial by `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_sheafCohomology_chgUniv`. -/
theorem isZero_rightDerived_moduleEvaluation_of_isZero_H'_chgUniv
    [HasExt.{w} (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u})]
    (U : SmallEtale B S hS F) (p : ℕ) (M : Modules.{u, u} B S hS F hF) :
    have := enoughInjectives_modules B S hS F hF
    IsZero (Sheaf.H'.{w} ((SheafOfModules.toSheaf.{u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M) (p + 1) U) →
      IsZero (((SheafOfModules.evaluation
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (op U)).rightDerived (p + 1)).obj M) := by
  intro _ h
  have : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
    hasExt_sheaf_smallEtale B S hS F
  have : EnoughInjectives (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
    enoughInjectives_sheaf_smallEtale B S hS F
  have := enoughInjectives_modules B S hS F hF
  have := hasExt_modules B S hS F hF
  exact isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u, w}
    (smallEtaleRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O) U p M h

/-- **The chart-indexed packaging: the hypothesis `h03DW` of this tree from its abelian-sheaf
form.**

`h03DW` — that a quasi-coherent `𝒪_F`-module has no higher derived *module* sections over an
affine étale chart, the étale-site analogue of Stacks 01XC — is carried as an explicit
hypothesis by `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower` (Stacks 08F6) and
its companions.  This supplies it from the corresponding vanishing of `CategoryTheory.Sheaf.H'`,
degree by degree through
`AlgebraicGeometry.Space.SmallEtale.isZero_rightDerived_moduleEvaluation_of_isZero_H'`, so that
those statements can be aimed at the abelian-sheaf vanishing directly with no module-level
comparison left to construct.  The quasi-coherence of `M` and the affineness of `U` are carried
through untouched: neither is used here. -/
theorem chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H' :
    have : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
      hasExt_sheaf_smallEtale B S hS F
    have := enoughInjectives_modules B S hS F hF
    (∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
        ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
          IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf.{u}
            (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M) p U)) →
      ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
        ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
          IsZero (((SheafOfModules.evaluation
            (ringSheaf (smallEtaleRingedSite B S hS F hF).O)
            (op U)).rightDerived p).obj M) := by
  intro _ _ hab U hU M hM p hp
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  exact isZero_rightDerived_moduleEvaluation_of_isZero_H' B S hS F hF U n M
    (hab U hU M hM (n + 1) (Nat.succ_pos n))

end Bridge

end AlgebraicGeometry.Space.SmallEtale

end
