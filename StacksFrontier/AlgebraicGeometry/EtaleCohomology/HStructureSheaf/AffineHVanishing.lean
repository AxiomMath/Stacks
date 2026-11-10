module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.EssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.ZariskiPerfection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningEssentialImage
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftSeparator
public import StacksFrontier.Homology.CompositeCollapse

/-!
# `𝒪^h` has no higher h cohomology over affine objects

Let `p` be a prime, `S` a scheme over `𝔽_p` and `B` a big h site containing `S`, and let
`ε : (Sch/S)_h ⟶ (Sch/S)_{fppf}` be the comparison of the two topologies on the big h category
over `S`. Stacks 0EWT says that `𝒪^{perf} = colim_F 𝒪`, as an object of the derived category of
the big fppf site, is `Rε_*` of an object. This file draws the consequence used in the proof of
Stacks 0EWU: the h sheaf `𝒪^h = (X ↦ Γ(Xᵃʷⁿ, 𝒪))` is `ε_*`-acyclic, so its h cohomology over an
object is its fppf cohomology there, and over an object with affine underlying scheme the latter
vanishes in positive degrees. Hence

`H^n((Sch/S)_h, U, 𝒪^h) = 0` for `U` affine and `n > 0`,

first for `𝒪^h` as a sheaf of modules over itself, then for its underlying abelian sheaf, and
finally for that abelian sheaf at the morphism universe of the site.

## Main definitions

* `AlgebraicGeometry.BigHOver.awnRing`: the h sheaf of rings `𝒪^h`.
* `AlgebraicGeometry.BigHOver.awnModule`: `𝒪^h` as a module over itself, with its sections at the
  coefficient universe `u + 1` of the site.

## Main results

* `AlgebraicGeometry.BigHOver.isZero_rightDerived_modulePushforward_awnModule`: `R^n ε_* 𝒪^h = 0`
  for `n > 0`.
* `AlgebraicGeometry.BigHOver.isZero_rightDerived_sections_awnModule`: the higher h cohomology of
  `𝒪^h` over an affine object vanishes, for sheaves of `𝒪^h`-modules.
* `AlgebraicGeometry.BigHOver.isZero_rightDerived_sheafSections_awnSheafAb`: the same for the
  underlying abelian sheaf at the morphism universe `u`.

## Implementation notes

`R^n ε_* 𝒪^h` vanishes by
`Stacks.Sites.CoarserTopology.isZero_rightDerived_modulePushforward_of_essImage`, the essential
image condition being Stacks 0EWT; the right derived functor `Rε_*` it is applied to is the total
right derived functor, which exists because K-injective resolutions do. The collapse
`R^n(ε_* ⋙ Γ_{fppf}(U, -)) ≅ R^n Γ_{fppf}(U, -) ∘ ε_*` at an `ε_*`-acyclic object is
`Stacks.RightDerivedComp.objIso`, `ε_*` preserving injectives as the right adjoint of the exact
functor `ε^*`, and `ε_* ⋙ Γ_{fppf}(U, -)` is `Γ_h(U, -)` on the nose.

The descent from the coefficient universe `u + 1`, where sheaves of modules on the big site live,
to the morphism universe `u`, where the Leray collapse onto the small Zariski site of `S` is
stated, is `CategoryTheory.Functor.rightDerivedIsoOfSquare` along the universe lift of abelian
sheaves, which preserves injective objects.

## References

* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 0EWU](https://stacks.math.columbia.edu/tag/0EWU)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.CoarserTopology

universe u

namespace AlgebraicGeometry.BigHOver

-- The global instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian`, `…Grothendieck` and
-- `…EnoughInjectives` are stated at a module universe that is a `max` of four universes, against
-- which `SheafOfModules.{u + 1} _` leaves a stuck universe constraint; the instances used here are
-- Mathlib's and the ones below.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The h sheaf of rings `𝒪^h`**, `X ↦ Γ(Xᵃʷⁿ, 𝒪)`, as a sheaf of rings for the h topology. -/
abbrev awnRing : Sheaf (BigHOver.topology B S hS) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (awnRingSheaf B S hS)

/-- **`𝒪^h` as a module over itself**, with its sections raised to the module universe `u + 1`
of the big site. Its direct image to the fppf topology is
`AlgebraicGeometry.BigHOver.perfectionModule`. -/
abbrev awnModule : SheafOfModules.{u + 1} (awnRing B S hS) :=
  Stacks.SheafOfModules.uliftUnit.{u + 1} (awnRing B S hS)

/-- The direct image of `awnModule` to the fppf topology is `perfectionModule`, on the nose. -/
theorem modulePushforward_obj_awnModule :
    (modulePushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS)
      (awnRing B S hS)).obj (awnModule B S hS) = perfectionModule B S hS :=
  rfl

section Instances

/-- Sheaves of modules over `𝒪^h` at the module universe `u + 1` have enough injectives. -/
theorem enoughInjectives_sheafOfModules_awnRing :
    EnoughInjectives (SheafOfModules.{u + 1} (awnRing B S hS)) :=
  _root_.SheafOfModules.enoughInjectives_of_univLE.{u + 1, u, u + 1, u} (awnRing B S hS)

/-- Sheaves of modules over `𝒪^{perf}` at the module universe `u + 1` have enough injectives. -/
theorem enoughInjectives_sheafOfModules_perfectionRing :
    EnoughInjectives (SheafOfModules.{u + 1} (perfectionRing B S hS)) :=
  _root_.SheafOfModules.enoughInjectives_of_univLE.{u + 1, u, u + 1, u} (perfectionRing B S hS)

/-- Abelian fppf sheaves at the coefficient universe `u + 1` have `Ext` groups in that universe. -/
theorem hasExt_sheaf_fppfTopology :
    HasExt.{u + 1} (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, 0}

/-- Abelian h sheaves at the coefficient universe `u + 1` have `Ext` groups in that universe. -/
theorem hasExt_sheaf_topology :
    HasExt.{u + 1} (Sheaf (BigHOver.topology B S hS) AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, 0}

/-- Abelian h sheaves at the morphism universe `u` are the localization of presheaves at the
locally bijective maps, the big h category being essentially small at that universe. -/
theorem wEqualsLocallyBijective_topology :
    (BigHOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  .ofEssentiallySmall _

end Instances

attribute [local instance] enoughInjectives_sheafOfModules_awnRing
  enoughInjectives_sheafOfModules_perfectionRing hasExt_sheaf_fppfTopology hasExt_sheaf_topology
  Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_join
  wEqualsLocallyBijective_topology
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

include hSp in
/-- **`𝒪^h` is `ε_*`-acyclic**: `R^n ε_* 𝒪^h = 0` for every `n > 0`. By Stacks 0EWT,
`(ε_* 𝒪^h)[0] = 𝒪^{perf}[0]` lies in the essential image of every right derived functor of `ε_*`,
here the total right derived functor. -/
theorem isZero_rightDerived_modulePushforward_awnModule (n : ℕ) (hn : 0 < n) :
    IsZero (((modulePushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS)
      (awnRing B S hS)).rightDerived n).obj (awnModule B S hS)) := by
  -- Stacks 0EWT, `AlgebraicGeometry.BigHOver.essImage_singleFunctor_perfectionModule`
  -- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/HStructureSheaf/EssentialImage.lean:119`),
  -- is stated over the standard model of the derived category.
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (awnRing B S hS))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (ringSheafOfLe (fppfTopology_le_topology B S hS) (awnRing B S hS)))
  let F := (modulePushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS)
    (awnRing B S hS)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have : F.HasPointwiseRightDerivedFunctor (HomotopyCategory.quasiIso
      (SheafOfModules.{u + 1} (awnRing B S hS)) (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 2, 0, u + 2, u + 2, 0} F
      (Stacks.MayerVietoris.CanonicalMapOfComplexes.exists_kInjectiveResolution.{u + 1, u + 1}
        (R := awnRing B S hS))).1
  let Rε := F.totalRightDerived DerivedCategory.Qh (HomotopyCategory.quasiIso
    (SheafOfModules.{u + 1} (awnRing B S hS)) (ComplexShape.up ℤ))
  let η := F.totalRightDerivedUnit DerivedCategory.Qh (HomotopyCategory.quasiIso
    (SheafOfModules.{u + 1} (awnRing B S hS)) (ComplexShape.up ℤ))
  have hRε : Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
    (SheafOfModules.{u + 1} (awnRing B S hS)) (ComplexShape.up ℤ)) := inferInstance
  exact isZero_rightDerived_modulePushforward_of_essImage (fppfTopology_le_topology B S hS)
    (awnRing B S hS) Rε η (awnModule B S hS)
    (@essImage_singleFunctor_perfectionModule B S hS p _ hSp Rε η hRε) n hn

/-- `ε_*` on sheaves of `𝒪^h`-modules preserves finite limits, being a right adjoint. -/
theorem preservesFiniteLimits_modulePushforward_awnRing :
    PreservesFiniteLimits (modulePushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS)
      (awnRing B S hS)) :=
  ⟨fun _ ↦ (modulePullbackAdjPushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS)
    (awnRing B S hS)).rightAdjoint_preservesLimits.preservesLimitsOfShape⟩

/-- `ε_*` on sheaves of `𝒪^h`-modules preserves injective objects, being right adjoint to the
exact functor `ε^*`. -/
theorem preservesInjectiveObjects_modulePushforward_awnRing :
    (modulePushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS)
      (awnRing B S hS)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (modulePullbackAdjPushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS)
      (awnRing B S hS))

attribute [local instance] preservesFiniteLimits_modulePushforward_awnRing
  preservesInjectiveObjects_modulePushforward_awnRing

include hSp in
/-- **The higher h cohomology of `𝒪^h` over an affine object vanishes**, for the sections functor
on sheaves of `𝒪^h`-modules: `𝒪^h` being `ε_*`-acyclic, its h cohomology over `U` is the fppf
cohomology of `ε_* 𝒪^h = 𝒪^{perf}` over `U`, which vanishes for `U` affine. -/
theorem isZero_rightDerived_sections_awnModule
    (U : BigHOver B S hS) (hU : IsAffine ((BigHOver.toScheme B S hS).obj U)) (n : ℕ) (hn : 0 < n) :
    IsZero (((Stacks.MayerVietoris.CanonicalMapOfComplexes.sections.{u + 1, u + 1}
      (awnRing B S hS) U).rightDerived n).obj (awnModule B S hS)) :=
  (isZero_rightDerived_sections_perfectionModule B S hS p hSp U hU n hn).of_iso
    (Stacks.RightDerivedComp.objIso
      (modulePushforward.{u + 1, u + 1, u, u} (fppfTopology_le_topology B S hS) (awnRing B S hS))
      (injectiveResolution (awnModule B S hS))
      (isZero_rightDerived_modulePushforward_awnModule B S hS p hSp)
      (Stacks.MayerVietoris.CanonicalMapOfComplexes.sections.{u + 1, u + 1}
        (ringSheafOfLe (fppfTopology_le_topology B S hS) (awnRing B S hS)) U) n)

include hSp in
/-- **The higher h cohomology of `𝒪^h` over an affine object vanishes**, for its underlying
abelian sheaf at the coefficient universe `u + 1`: the higher sections of a sheaf of modules over
an object are those of its underlying abelian sheaf (Stacks 03FD). -/
theorem isZero_rightDerived_sheafSections_toSheaf_awnModule
    (U : BigHOver B S hS) (hU : IsAffine ((BigHOver.toScheme B S hS).obj U)) (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u + 1}).obj
      (op U)).rightDerived n).obj
        ((SheafOfModules.toSheaf (awnRing B S hS)).obj (awnModule B S hS))) :=
  (isZero_rightDerived_sections_awnModule B S hS p hSp U hU n hn).of_iso
    ((Stacks.Cohomology.ObjectSections.rightDerivedSectionsIsoUnivLE.{0, u, u, u + 1}
      (BigHOver.topology B S hS) (awnRing B S hS) U n).app (awnModule B S hS)).symm

/-- **The universe lift from `u` to `u + 1` of abelian h sheaves preserves injective objects**:
abelian h sheaves at the morphism universe `u` have a separator, and those at `u + 1` form a
Grothendieck abelian category, the big h category being essentially small at both universes. -/
theorem preservesInjectiveObjects_uliftSheafFunctor_topology :
    (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
      (BigHOver.topology B S hS)).PreservesInjectiveObjects := by
  have : IsGrothendieckAbelian.{u} (Sheaf (BigHOver.topology B S hS) AddCommGrpCat.{u}) :=
    Stacks.Cohomology.BiggerSite.isGrothendieckAbelian_sheaf.{u} _
  have := Stacks.Cohomology.ColimitsOfCohomology.essentiallySmall_join (C := BigHOver B S hS)
  have : IsGrothendieckAbelian.{u + 1} (Sheaf (BigHOver.topology B S hS) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _
  exact Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{
    u + 1, u + 1, u, u, u + 1} (BigHOver.topology B S hS)

attribute [local instance] preservesInjectiveObjects_uliftSheafFunctor_topology

include hSp in
/-- **`𝒪^h` has no higher h cohomology over affine objects**, as an abelian sheaf at the morphism
universe `u` of the site: `H^n(U, 𝒪^h) = 0` for `U` affine and `n > 0`. The lift of the
coefficients from `u` to `u + 1` commutes with the higher sections over `U`, because it is exact
and preserves injective objects, and it reflects the vanishing of an abelian group. -/
theorem isZero_rightDerived_sheafSections_awnSheafAb
    (U : BigHOver B S hS) (hU : IsAffine ((BigHOver.toScheme B S hS).obj U)) (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj (op U)).rightDerived
      n).obj (awnSheafAb B S hS)) := by
  have : AddCommGrpCat.uliftFunctor.{u + 1, u}.PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have h := (isZero_rightDerived_sheafSections_toSheaf_awnModule B S hS p hSp U hU n hn).of_iso
    ((Functor.rightDerivedIsoOfSquare
      (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} (BigHOver.topology B S hS))
      ((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj (op U))
      ((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u + 1}).obj (op U))
      AddCommGrpCat.uliftFunctor.{u + 1, u}
      (Stacks.Sheaves.UniverseLift.sheafSectionsULiftIso (BigHOver.topology B S hS) U) n).app
        (awnSheafAb B S hS))
  rw [AddCommGrpCat.isZero_iff_subsingleton] at h ⊢
  exact Equiv.ulift.subsingleton_congr.1 h

end AlgebraicGeometry.BigHOver
