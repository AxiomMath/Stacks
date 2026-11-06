module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalCohomologyULiftComparison
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftSeparator

/-!
# Filtered colimits and the cohomology of modules on an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`.  Stacks 073E
says that the cohomology of `X` commutes with filtered colimits.  It is proved in this library for
abelian sheaves on the small étale site, with coefficients `AddCommGrpCat.{u + 1}`
(`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections`).  This file reads it for
`𝒪_X`-modules at the universe `u` of the structure rings — the universe of
`AlgebraicGeometry.Space.modulePushforward` and of the cohomology
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}` used throughout the
chapters on algebraic spaces — in the form the proof of Stacks 09TL consumes: the higher
cohomology of a filtered colimit vanishes as soon as it vanishes on the terms.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isColimit`: on a
  quasi-compact and quasi-separated algebraic space, if `H^n(X, 𝓕_i) = 0` for every term of a
  filtered diagram of `𝒪_X`-modules, then `H^n(X, colim_i 𝓕_i) = 0`.

## Implementation notes

The transport is `Stacks.Cohomology.ModuleULiftComparison.isZero_rightDerived_of_isColimit`: the
cohomology of a module is the abelian cohomology of the universe lift of its underlying abelian
sheaf (Stacks 03FD), and forgetting the module structure and lifting the universe preserve the
colimit.  The homological instances it asks for at the two coefficient universes `u` and `u + 1`
are supplied here; they hold because the small étale site is essentially small at `u`.

## References

* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.UniverseLift

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **Module cohomology of a filtered colimit on a quasi-compact and quasi-separated algebraic
space.**  If the `n`-th cohomology of every term of a filtered diagram of `𝒪_X`-modules vanishes,
so does that of its colimit.  This is Stacks 073E read for modules at the universe of the
structure rings. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_isColimit
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    {I : Type u} [SmallCategory I] [IsFiltered I] (D : I ⥤ Modules.{u, u} B S hS X hX)
    (c : Cocone D) (hc : IsColimit c) (n : ℕ)
    (hD : ∀ i, IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).rightDerived
        n).obj (D.obj i))) :
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).rightDerived
        n).obj c.pt) := by
  let J := (smallEtaleRingedSite B S hS X hX).J
  have : HasSheafify J AddCommGrpCat.{u} := SmallEtale.instHasSheafify B S hS X _
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS X _
  have : HasSheafify J AddCommGrpCat.{u + 1} :=
    hasSheafify_smallEtaleRingedSite_addCommGrpCat.{u, u} B S hS X hX
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat.{u, u} B S hS X hX
  have : EssentiallySmall.{u} (SmallEtale B S hS X) := SmallEtale.instEssentiallySmall B S hS X
  have : IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} (SmallEtale.topology B S hS X) _
  have : IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1}) :=
    have : EssentiallySmall.{u + 1} (SmallEtale B S hS X) :=
      essentiallySmallSelf.{0} (C := SmallEtale B S hS X)
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (SmallEtale.topology B S hS X) _
  have : EnoughInjectives (Sheaf J AddCommGrpCat.{u}) := IsGrothendieckAbelian.enoughInjectives
  have : EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.enoughInjectives
  have : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u}) := HasExt.standard _
  have : HasExt.{u + 1} (Modules.{u, u} B S hS X hX) := HasExt.standard _
  have : HasSeparator (Sheaf J AddCommGrpCat.{u}) := IsGrothendieckAbelian.hasSeparator.{u}
  have : (uliftSheafFunctor.{u + 1, u} J).PreservesInjectiveObjects :=
    preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{u + 1, u + 1, u} _
  have : HasGlobalSectionsFunctor J AddCommGrpCat.{u + 1} := inferInstance
  exact Stacks.Cohomology.ModuleULiftComparison.isZero_rightDerived_of_isColimit J _ D c hc n
    (isIso_colimit_post_rightDerived_globalSections B S hS hZ X hX hqc hqs n _) hD

end AlgebraicGeometry.Space

end
