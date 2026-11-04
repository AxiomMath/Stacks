module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ModuleRingUniverseFreeDerived
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AS parts (2) and (4): derived lower shriek on modules for the two subsites

Let `𝒳` be an algebraic stack, `𝒳_τ` its big site of **Stacks 06TP** and `𝒳'` a full subsite of
it — the lisse-étale site or the flat-fppf site of **Stacks 0787** — and let
`g : Sh(𝒳') ⟶ Sh(𝒳_τ)` be the morphism of topoi of **Stacks 0788**.  **Stacks 07AS** parts (2)
and (4) assert that the lower-shriek functor

`g_! : Mod(𝒪_{𝒳'}) ⥤ Mod(𝒪_𝒳)`

has an unbounded left derived functor `Lg_! : D(𝒪_{𝒳'}) ⟶ D(𝒪_𝒳)`, that `Lg_!` is left adjoint
to `g^*`, and that `g^* ∘ Lg_! = id`.  This file proves all three, for every algebraic stack and
with nothing assumed, over the **actual** structure sheaf of **Stacks 06TV**.

Parts (1) and (3), the abelian-sheaf statements, are
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleDerivedLowerShriek.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedLowerShriekUnconditional.lean`; they are
untouched here.

## The universe question, and how it is answered

The structure sheaf of **Stacks 06TV** has its sections in `Type u`, while the two sites have
objects in `Type (u+1)` and morphisms in `Type u`, so their sheaves of modules have sections in
`Type (u+1)`: the module universe must contain both object universes for `Mod(𝒪)` to be
Grothendieck abelian and for the Čech computation of **Stacks 0D6X** to run.  The derived
lower-shriek-on-modules development of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedAdjunction.lean` ties the two
universes together and therefore does not apply as stated.  What is used here instead is its
generalization with the two universes separated (of which it is the case `m = r`),
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ModuleRingUniverseFree.lean` and
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ModuleRingUniverseFreeDerived.lean`; the structure sheaf is the one of Stacks 06TV on the
nose, not a universe lift of it.

## Main results

* `AlgebraicGeometry.Stack.subsiteLowerShriekModulesAcyclic`: the acyclicity statement of
  **Stacks 07AC** for modules on a full subsite, with no hypothesis, from the Čech data of
  **Stacks 0D6X**.
* `AlgebraicGeometry.Stack.LisseEtale.lowerShriekModules_derived`: **Stacks 07AS (2)**, the three
  assertions in one statement; its three components are
  `AlgebraicGeometry.Stack.LisseEtale.hasPointwiseLeftDerivedLowerShriekModules`,
  `...LisseEtale.derivedLowerShriekModulesAdjunction`,
  `...LisseEtale.derivedLowerShriekModulesRestrictionIso`.
* `AlgebraicGeometry.Stack.FlatFppf.lowerShriekModules_derived`: **Stacks 07AS (4)**, likewise;
  its three components are
  `AlgebraicGeometry.Stack.FlatFppf.hasPointwiseLeftDerivedLowerShriekModules`,
  `...FlatFppf.derivedLowerShriekModulesAdjunction`,
  `...FlatFppf.derivedLowerShriekModulesRestrictionIso`.

## What is assumed

Nothing.  The covering-pullback condition of **Stacks 00WV** for the two inclusions holds for
every algebraic stack (`AlgebraicGeometry.Stack.FlatFppf.preservesCoveringPullbacks_inclusion`
and its lisse-étale counterpart), continuity and cocontinuity of the inclusions are theorems,
sheafification and enough injectives at the module universe `u+1` come from
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteGlobalCohomology.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SeparatorUnivLE.lean`, the module-level `g_!`
exists by `SheafOfModules.pushforward_isRightAdjoint_of_univLE`, and the acyclicity statement of
**Stacks 07AC** is proved here.  `g^* g_! = id` is **Stacks 077I** through
`SheafOfModules.isIso_unit_of_isIso_coefficient`, the inclusion of a full subsite being fully
faithful.

## Implementation notes

The Čech data fed to **Stacks 0D6X** is the one of
`AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero`: the coverings whose arrows admit
pullbacks against arbitrary morphisms to the base, preserved by the inclusion.  Those exist
because the total category of a category fibred in groupoids has pullbacks, are cofinal by
`Stacks.Sites.exists_preZeroHypercover_le`, and have invertible Čech comparison by
`Stacks.Sites.preservesLimit_fibreProducts_overPost` and
`Stacks.CechSite.isIso_cechProductMapOfFunctor`.  Only the coefficient category changes from
that statement: abelian sheaves there, sheaves of modules here.

`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its two companions are switched off,
for the reason recorded in `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ModuleRingUniverseFree.lean`: their module universe is a join of
four variables of which the arguments pin only three, so instance search against a category of
modules at `u+1` leaves an unsolvable universe metavariable.  The replacements are
`SheafOfModules.isGrothendieckAbelian_of_univLE` and `SheafOfModules.enoughInjectives_of_univLE`,
whose hypotheses are `UnivLE` and hold here.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.DerivedLowerShriek

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack

universe u w

/-! ### A full subsite of the site of Stacks 06TP -/

section Subsite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type (u + 1)} [Category.{u} X] (p : X ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)

/-- The sheaf of rings on the site of **Stacks 06TP** over which the sheaves of modules are
taken: the `RingCat`-valued sheaf underlying the structure sheaf of **Stacks 06TV**.  It is
`AlgebraicGeometry.Stack.ringStructureSheafCore` on the nose. -/
abbrev ambientModuleRing : Sheaf (associatedTopology B S hS p τ) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS p hp τ hτ)

variable [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- The structure sheaf of the full subsite, as a sheaf of rings: the restriction of
`AlgebraicGeometry.Stack.ambientModuleRing` along the inclusion.  That this restriction *is* the
structure sheaf of the subsite is **Stacks 0788** (f). -/
abbrev subsiteModuleRing : Sheaf (subsiteTopology B S hS p τ P) RingCat.{u} :=
  Stacks.SheafOfModules.inverseImageRing (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)

/-- Sheaves of modules on the subsite at the module universe `u+1` form a Grothendieck abelian
category: the `UnivLE` conditions of `SheafOfModules.isGrothendieckAbelian_of_univLE` hold, the
objects of the site lying in `Type (u+1)` and its morphisms and the structure rings in
`Type u`. -/
theorem isGrothendieckAbelian_subsiteModules :
    IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P)) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1, u, u + 1, u} _

/-- Sheaves of modules on the site of **Stacks 06TP** at the module universe `u+1` form a
Grothendieck abelian category. -/
theorem isGrothendieckAbelian_ambientModules :
    IsGrothendieckAbelian.{u + 1}
      (SheafOfModules.{u + 1} (ambientModuleRing B S hS p hp τ hτ)) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{u + 1, u, u + 1, u} _

/-- Sheaves of modules on the subsite at the module universe `u+1` have enough injectives. -/
theorem enoughInjectives_subsiteModules :
    EnoughInjectives (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P)) :=
  SheafOfModules.enoughInjectives_of_univLE.{u + 1, u, u + 1, u} _

/-- Sheaves of modules on the subsite at the module universe `u+1` have `Ext`-groups there:
they are locally `u+1`-small and have enough injectives. -/
theorem hasExt_subsiteModules :
    HasExt.{u + 1} (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P)) :=
  have : LocallySmall.{u + 1}
      (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P)) :=
    SheafOfModules.locallySmall_of_univLE.{u + 1, u, u + 1, u} _
  have := enoughInjectives_subsiteModules B S hS p hp τ hτ P
  hasExt_of_enoughInjectives _

attribute [local instance] isGrothendieckAbelian_subsiteModules
  isGrothendieckAbelian_ambientModules enoughInjectives_subsiteModules hasExt_subsiteModules

variable [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

omit [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)] in
/-- **The acyclicity statement of Stacks 07AC for sheaves of modules on a full subsite of the
site of Stacks 06TP, with no hypothesis.** The lower-shriek functor
`g_! : Mod(𝒪_{𝒳'}) ⥤ Mod(𝒪_𝒳)` carries every bounded above acyclic complex whose terms are
direct sums of the generators `j_{U!} 𝒪_U` to an acyclic complex.

This is the module-level counterpart of
`AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero`, run through
`Stacks.Cohomology.DerivedLowerShriek.FreeRingUniverse.lowerShriekModules_acyclic_of_cech` rather
than through the abelian-sheaf Čech statement; the Čech data is the same, and the structure sheaf
keeps its sections in `Type u` while the modules have theirs in `Type (u+1)`.

It is the single input of the three assertions of **Stacks 07AS** parts (2) and (4) below, so the
tag sits there and not here. -/
theorem subsiteLowerShriekModulesAcyclic
    [Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p τ P) P.ι]
    (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P)) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, FreeRingUniverse.IsSumOfExtensionByZeroUnits.{u + 1}
      (subsiteTopology B S hS p τ P) (subsiteModuleRing B S hS p hp τ hτ P) (L.X n))
    (hLac : L.Acyclic) :
    (((FreeRingUniverse.lowerShriekModules.{u + 1} (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι
        (ambientModuleRing B S hS p hp τ hτ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  have hcart : ∀ {a b : X} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f := fun f =>
    hp.isStronglyCartesian_homLift (p.map f) f
  have : p.IsFibered := hp.isFibered
  have : HasPullbacks X :=
    @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} {f g} =>
      p.hasPullback_of_forall_isStronglyCartesian hcart f g
  set J := subsiteTopology B S hS p τ P with hJ
  set ι := P.ι with hι
  set Cov : ∀ U : P.FullSubcategory,
      Set { E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ J U } :=
    fun U => { E | (∀ (j : E.1.I₀) ⦃W : P.FullSubcategory⦄ (g : W ⟶ U),
        HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : P.FullSubcategory⦄ (g : W ⟶ U),
        PreservesLimit (cospan (E.1.f j) g) ι) } with hCov
  have hProducts : ∀ {U : P.FullSubcategory}
      (E : { E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun b ↦ Over.mk (E.1.f (i b))) :=
    fun E hE q i => Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i
  have hImageProducts : ∀ {U : P.FullSubcategory}
      (E : { E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → (E.1.map ι).I₀),
        HasProduct (fun b ↦ Over.mk ((E.1.map ι).f (i b))) :=
    fun E _ q i =>
      Stacks.Sites.hasProduct_fibreProducts (E.1.map ι) (fun _ _ _ => inferInstance) q i
  exact FreeRingUniverse.lowerShriekModules_acyclic_of_cech.{u} J
    (associatedTopology B S hS p τ) ι (structureSheaf B S hS p hp τ hτ)
    Cov hProducts hImageProducts
    (fun V R hR => by
      obtain ⟨E, hJE, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J ι R hR
      exact ⟨⟨E, hJE⟩, ⟨hpb, hpr⟩, hle⟩)
    (fun E hE q i => by
      let := hProducts E hE
      let := hImageProducts E hE
      let := Stacks.Sites.preservesLimit_fibreProducts_overPost ι E.1 hE.1 hE.2 q i
      exact Stacks.CechSite.isIso_cechProductMapOfFunctor ι E.1 q i)
    a L hLE hLP hLac

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p τ P) P.ι]

omit [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)] in
/-- **Stacks 07AC, existence, on a full subsite of the site of Stacks 06TP, with no
hypothesis.** Degreewise lower shriek of sheaves of modules, followed by the localization of the
homotopy category of `Mod(𝒪_𝒳)`, has a pointwise left derived functor.  The acyclicity statement
it is reduced to is `AlgebraicGeometry.Stack.subsiteLowerShriekModulesAcyclic`. -/
theorem hasPointwiseLeftDerivedSubsiteLowerShriekModules :
    (FreeRingUniverse.lowerShriekOnHomotopy.{u + 1} (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (FreeRingUniverse.sourceQuasiIso.{u + 1} (subsiteTopology B S hS p τ P)
          (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)) :=
  FreeRingUniverse.hasPointwiseLeftDerivedLowerShriek_of_acyclic.{u} _ _ _ _
    (subsiteLowerShriekModulesAcyclic B S hS p hp τ hτ P)

omit [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)] in
/-- The absoluteness of `Lg_!` on a full subsite, with no hypothesis: the second input of the
derived adjunction, from the same acyclicity statement as the first. -/
theorem isLeftDerivedFunctor_derivedSubsiteLowerShriekModules_comp
    {E : Type*} [Category E]
    (G : DerivedCategory (SheafOfModules.{u + 1}
      (ambientModuleRing B S hS p hp τ hτ)) ⥤ E) :
    haveI := hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS p hp τ hτ P
    (FreeRingUniverse.derivedLowerShriek.{u + 1} (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ) ⋙
      G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh
          (FreeRingUniverse.derivedLowerShriek.{u + 1} (subsiteTopology B S hS p τ P)
            (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)) G).inv ≫
        Functor.whiskerRight (FreeRingUniverse.derivedLowerShriekComparison.{u + 1}
          (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι
          (ambientModuleRing B S hS p hp τ hτ)) G)
      (FreeRingUniverse.sourceQuasiIso.{u + 1} (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)) :=
  have := hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS p hp τ hτ P
  FreeRingUniverse.isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic.{u} _ _ _ _
    (subsiteLowerShriekModulesAcyclic B S hS p hp τ hτ P) G

/-- `g^*` on the unbounded derived categories of modules, for a full subsite. -/
abbrev derivedSubsiteRestrictionModules :
    DerivedCategory (SheafOfModules.{u + 1} (ambientModuleRing B S hS p hp τ hτ)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P)) :=
  FreeRingUniverse.derivedRestriction.{u + 1} (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)

/-- **`Lg_!` on sheaves of modules for a full subsite of the site of Stacks 06TP**, with no
hypothesis. -/
abbrev derivedSubsiteLowerShriekModules :
    DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (ambientModuleRing B S hS p hp τ hτ)) :=
  haveI := hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS p hp τ hτ P
  FreeRingUniverse.derivedLowerShriek.{u + 1} (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)

/-- **The derived adjunction `Lg_! ⊣ g^*` on sheaves of modules for a full subsite**, with no
hypothesis.  This is **Stacks 07AC** at the structure sheaf of **Stacks 06TV**. -/
def derivedSubsiteLowerShriekModulesAdjunction :
    derivedSubsiteLowerShriekModules B S hS p hp τ hτ P ⊣
      derivedSubsiteRestrictionModules B S hS p hp τ hτ P :=
  haveI := hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS p hp τ hτ P
  haveI := isLeftDerivedFunctor_derivedSubsiteLowerShriekModules_comp B S hS p hp τ hτ P
    (derivedSubsiteRestrictionModules B S hS p hp τ hτ P)
  FreeRingUniverse.derivedLowerShriekAdjunction.{u + 1} (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)

/-- **`g^* ∘ Lg_! = id` on sheaves of modules for a full subsite**, with no hypothesis: the
inclusion of a full subcategory is fully faithful, so the unit of the ordinary adjunction is an
isomorphism — that is **Stacks 077I** — and uniqueness of left derived functors carries that to
the derived adjunction. -/
def derivedSubsiteLowerShriekModulesRestrictionIso :
    derivedSubsiteLowerShriekModules B S hS p hp τ hτ P ⋙
        derivedSubsiteRestrictionModules B S hS p hp τ hτ P ≅
      𝟭 (DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRing B S hS p hp τ hτ P))) :=
  haveI := hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS p hp τ hτ P
  haveI := isLeftDerivedFunctor_derivedSubsiteLowerShriekModules_comp B S hS p hp τ hτ P
    (derivedSubsiteRestrictionModules B S hS p hp τ hτ P)
  FreeRingUniverse.derivedLowerShriekRestrictionIso.{u + 1} (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)
    (FreeRingUniverse.isIso_adjunctionModules_unit.{u} (subsiteTopology B S hS p τ P)
      (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ))

/-- **The unit of `Lg_! ⊣ g^*` on sheaves of modules for a full subsite is an isomorphism**, with
no hypothesis: `g^* ∘ Lg_! = id` through the canonical map. -/
theorem isIso_derivedSubsiteLowerShriekModulesAdjunction_unit :
    IsIso (derivedSubsiteLowerShriekModulesAdjunction B S hS p hp τ hτ P).unit :=
  have := hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS p hp τ hτ P
  have := isLeftDerivedFunctor_derivedSubsiteLowerShriekModules_comp B S hS p hp τ hτ P
    (derivedSubsiteRestrictionModules B S hS p hp τ hτ P)
  FreeRingUniverse.isIso_derivedLowerShriekAdjunction_unit.{u + 1} (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ)
    (FreeRingUniverse.isIso_adjunctionModules_unit.{u} (subsiteTopology B S hS p τ P)
      (associatedTopology B S hS p τ) P.ι (ambientModuleRing B S hS p hp τ hτ))

end Derived

end Subsite

/-! ### Stacks 07AS (4): the flat-fppf site -/

namespace FlatFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  preservesCoveringPullbacks_inclusion

attribute [local instance] HasDerivedCategory.standard

/-- The sheaf of rings on the fppf site of an algebraic stack over which the sheaves of modules
of **Stacks 07AS** (4) are taken: the `RingCat`-valued sheaf underlying the structure sheaf of
**Stacks 06TV**.  It is `AlgebraicGeometry.Stack.FlatFppf.ambientRingStructureSheaf` on the
nose. -/
abbrev moduleRing : Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) RingCat.{u} :=
  ambientModuleRing B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl

/-- The structure sheaf of the flat-fppf site as a sheaf of rings: the restriction of
`AlgebraicGeometry.Stack.FlatFppf.moduleRing` along the inclusion of the flat objects.  That
this restriction *is* the structure sheaf of the subsite is **Stacks 0788** (2)(f). -/
abbrev subsiteModuleRingFlat : Sheaf (inclusionTopology B S hS 𝒳) RingCat.{u} :=
  subsiteModuleRing B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
    (objectProperty B S hS 𝒳)

/-- **Stacks 07AS (4), existence of `Lg_!` on modules, for every algebraic stack and with NO
hypothesis.** Degreewise lower shriek of sheaves of `𝒪_{𝒳_{flat,fppf}}`-modules, followed by the
localization of the homotopy category of `Mod(𝒪_𝒳)`, has a pointwise left derived functor along
the localization of the homotopy category of `Mod(𝒪_{𝒳_{flat,fppf}})`.

The structure sheaf is the one of **Stacks 06TV**, with sections in `Type u`; the modules have
sections in `Type (u+1)`, the universe the Čech computation of **Stacks 0D6X** forces, and that
split is what `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ModuleRingUniverseFreeDerived.lean` provides.  The acyclicity statement of
**Stacks 07AC** is `AlgebraicGeometry.Stack.subsiteLowerShriekModulesAcyclic`, a theorem here and
not a hypothesis. -/
theorem hasPointwiseLeftDerivedLowerShriekModules :
    (FreeRingUniverse.lowerShriekOnHomotopy.{u + 1} (inclusionTopology B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
        (moduleRing B S hS 𝒳) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (FreeRingUniverse.sourceQuasiIso.{u + 1} (inclusionTopology B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
          (moduleRing B S hS 𝒳)) :=
  hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)

/-- `g^*` on the unbounded derived categories of modules for the flat-fppf site. -/
abbrev derivedRestrictionModules :
    DerivedCategory (SheafOfModules.{u + 1} (moduleRing B S hS 𝒳)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRingFlat B S hS 𝒳)) :=
  derivedSubsiteRestrictionModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl (objectProperty B S hS 𝒳)

/-- **`Lg_!` on sheaves of modules for the flat-fppf site of an algebraic stack**, with no
hypothesis. -/
abbrev derivedLowerShriekModules :
    DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRingFlat B S hS 𝒳)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (moduleRing B S hS 𝒳)) :=
  derivedSubsiteLowerShriekModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl (objectProperty B S hS 𝒳)

/-- **Stacks 07AS (4), adjointness, for every algebraic stack and with NO hypothesis**: the
unbounded derived lower-shriek functor on sheaves of `𝒪_{𝒳_{flat,fppf}}`-modules is left adjoint
to derived restriction `g^*`.  This is **Stacks 09T5** on the unbounded derived category of the
Grothendieck abelian category `Mod(𝒪_𝒳)`, whose two inputs — existence of `Lg_!` and its
absoluteness — both come from the acyclicity statement of **Stacks 07AC**, proved here. -/
def derivedLowerShriekModulesAdjunction :
    derivedLowerShriekModules B S hS 𝒳 ⊣ derivedRestrictionModules B S hS 𝒳 :=
  derivedSubsiteLowerShriekModulesAdjunction B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)

/-- **Stacks 07AS (4), `g^* Lg_! = id`, for every algebraic stack and with NO hypothesis**:
restriction of modules after derived lower shriek is canonically the identity of
`D(𝒪_{𝒳_{flat,fppf}})`.

The ordinary unit `F ⟶ g^* g_! F` is an isomorphism, the inclusion of the flat objects being
continuous, cocontinuous and fully faithful — that is **Stacks 077I** — and uniqueness of left
derived functors carries that to the unit of the derived adjunction. -/
def derivedLowerShriekModulesRestrictionIso :
    derivedLowerShriekModules B S hS 𝒳 ⋙ derivedRestrictionModules B S hS 𝒳 ≅
      𝟭 (DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRingFlat B S hS 𝒳))) :=
  derivedSubsiteLowerShriekModulesRestrictionIso B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)

/-- **Stacks 07AS (4)**, all three assertions, for every algebraic stack and with NO
hypothesis.  For `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_τ)` the morphism of ringed topoi of
**Stacks 0788**:

* the functor `g_! : Mod(𝒪_{𝒳_{flat,fppf}}) ⥤ Mod(𝒪_𝒳)` has a left derived functor
  `Lg_! : D(𝒪_{𝒳_{flat,fppf}}) ⟶ D(𝒪_𝒳)` — degreewise `g_!` followed by the localization of the
  homotopy category of `Mod(𝒪_𝒳)` has a pointwise left derived functor along the localization of
  the homotopy category of `Mod(𝒪_{𝒳_{flat,fppf}})`, and `Lg_!` is that total left derived functor;
* `Lg_!` is left adjoint to `g^*`, by an adjunction whose unit is an isomorphism;
* `g^* ∘ Lg_! = id`.

The structure sheaf is the one of **Stacks 06TV**, with sections in `Type u`, and the modules
have their sections in `Type (u+1)`. -/
@[stacks 07AS "part (4), the whole of it: existence of the unbounded left derived functor \
`Lg_!` of `g_!` on sheaves of modules for the flat-fppf site, its adjunction \
`Lg_! ⊣ g^*` (with invertible unit), and `g^* ∘ Lg_! = id`, for every algebraic stack and with \
NO hypothesis. The structure sheaf is the one of Tag 06TV; the acyclicity statement of Tag 07AC \
is a theorem here, `AlgebraicGeometry.Stack.subsiteLowerShriekModulesAcyclic`, and the \
invertibility of the ordinary unit is Tag 077I"]
theorem lowerShriekModules_derived :
    (FreeRingUniverse.lowerShriekOnHomotopy.{u + 1} (inclusionTopology B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
        (moduleRing B S hS 𝒳) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (FreeRingUniverse.sourceQuasiIso.{u + 1} (inclusionTopology B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
        (moduleRing B S hS 𝒳)) ∧
    (∃ adj : derivedLowerShriekModules B S hS 𝒳 ⊣ derivedRestrictionModules B S hS 𝒳,
      IsIso adj.unit) ∧
    Nonempty (derivedLowerShriekModules B S hS 𝒳 ⋙ derivedRestrictionModules B S hS 𝒳 ≅
      𝟭 (DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRingFlat B S hS 𝒳)))) :=
  ⟨hasPointwiseLeftDerivedLowerShriekModules B S hS 𝒳,
    ⟨derivedLowerShriekModulesAdjunction B S hS 𝒳,
      isIso_derivedSubsiteLowerShriekModulesAdjunction_unit B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)⟩,
    ⟨derivedLowerShriekModulesRestrictionIso B S hS 𝒳⟩⟩

end FlatFppf

/-! ### Stacks 07AS (2): the lisse-étale site -/

namespace LisseEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  preservesCoveringPullbacks_inclusion

attribute [local instance] HasDerivedCategory.standard

/-- The sheaf of rings on the big étale site of an algebraic stack over which the sheaves of
modules of **Stacks 07AS** (2) are taken: the `RingCat`-valued sheaf underlying the structure
sheaf of **Stacks 06TV**.  It is
`AlgebraicGeometry.Stack.LisseEtale.ambientRingStructureSheaf` on the nose. -/
abbrev moduleRing : Sheaf (ambientTopology B S hS 𝒳) RingCat.{u} :=
  ambientModuleRing B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B)

/-- The structure sheaf of the lisse-étale site as a sheaf of rings: the restriction of
`AlgebraicGeometry.Stack.LisseEtale.moduleRing` along the inclusion of the smooth objects.  That
this restriction *is* the structure sheaf of the subsite is **Stacks 0788** (1)(f). -/
abbrev subsiteModuleRingSmooth :
    Sheaf (inclusionTopology.{u, w} B S hS 𝒳) RingCat.{u} :=
  subsiteModuleRing B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳)

/-- **Stacks 07AS (2), existence of `Lg_!` on modules, for every algebraic stack and with NO
hypothesis.** Degreewise lower shriek of sheaves of `𝒪_{𝒳_{lisse,étale}}`-modules, followed by
the localization of the homotopy category of `Mod(𝒪_𝒳)`, has a pointwise left derived functor
along the localization of the homotopy category of `Mod(𝒪_{𝒳_{lisse,étale}})`.

The structure sheaf is the one of **Stacks 06TV**, with sections in `Type u`; the modules have
sections in `Type (u+1)`, the universe the Čech computation of **Stacks 0D6X** forces.  The
acyclicity statement of **Stacks 07AC** is
`AlgebraicGeometry.Stack.subsiteLowerShriekModulesAcyclic`, a theorem here and not a
hypothesis. -/
theorem hasPointwiseLeftDerivedLowerShriekModules :
    (FreeRingUniverse.lowerShriekOnHomotopy.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (ambientTopology B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒳).ι
        (moduleRing.{u, w} B S hS 𝒳) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (FreeRingUniverse.sourceQuasiIso.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
          (ambientTopology B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒳).ι
          (moduleRing.{u, w} B S hS 𝒳)) :=
  hasPointwiseLeftDerivedSubsiteLowerShriekModules B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
    (smoothObject.{u, w} B S hS 𝒳)

/-- `g^*` on the unbounded derived categories of modules for the lisse-étale site. -/
abbrev derivedRestrictionModules :
    DerivedCategory (SheafOfModules.{u + 1} (moduleRing.{u, w} B S hS 𝒳)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRingSmooth.{u, w} B S hS 𝒳)) :=
  derivedSubsiteRestrictionModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳)

/-- **`Lg_!` on sheaves of modules for the lisse-étale site of an algebraic stack**, with no
hypothesis. -/
abbrev derivedLowerShriekModules :
    DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRingSmooth.{u, w} B S hS 𝒳)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (moduleRing.{u, w} B S hS 𝒳)) :=
  derivedSubsiteLowerShriekModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳)

/-- **Stacks 07AS (2), adjointness, for every algebraic stack and with NO hypothesis**: the
unbounded derived lower-shriek functor on sheaves of `𝒪_{𝒳_{lisse,étale}}`-modules is left
adjoint to derived restriction `g^*`. -/
def derivedLowerShriekModulesAdjunction :
    derivedLowerShriekModules.{u, w} B S hS 𝒳 ⊣ derivedRestrictionModules.{u, w} B S hS 𝒳 :=
  derivedSubsiteLowerShriekModulesAdjunction B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
    (smoothObject.{u, w} B S hS 𝒳)

/-- **Stacks 07AS (2), `g^* Lg_! = id`, for every algebraic stack and with NO hypothesis**:
restriction of modules after derived lower shriek is canonically the identity of
`D(𝒪_{𝒳_{lisse,étale}})`.

The ordinary unit `F ⟶ g^* g_! F` is an isomorphism, the inclusion of the smooth objects being
continuous, cocontinuous and fully faithful — that is **Stacks 077I** — and uniqueness of left
derived functors carries that to the unit of the derived adjunction. -/
def derivedLowerShriekModulesRestrictionIso :
    derivedLowerShriekModules.{u, w} B S hS 𝒳 ⋙ derivedRestrictionModules.{u, w} B S hS 𝒳 ≅
      𝟭 (DerivedCategory (SheafOfModules.{u + 1}
        (subsiteModuleRingSmooth.{u, w} B S hS 𝒳))) :=
  derivedSubsiteLowerShriekModulesRestrictionIso B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
    (smoothObject.{u, w} B S hS 𝒳)

/-- **Stacks 07AS (2)**, all three assertions, for every algebraic stack and with NO
hypothesis.  For `g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_τ)` the morphism of ringed topoi of
**Stacks 0788**:

* the functor `g_! : Mod(𝒪_{𝒳_{lisse,étale}}) ⥤ Mod(𝒪_𝒳)` has a left derived functor
  `Lg_! : D(𝒪_{𝒳_{lisse,étale}}) ⟶ D(𝒪_𝒳)` — degreewise `g_!` followed by the localization of the
  homotopy category of `Mod(𝒪_𝒳)` has a pointwise left derived functor along the localization of
  the homotopy category of `Mod(𝒪_{𝒳_{lisse,étale}})`, and `Lg_!` is that total left derived
  functor;
* `Lg_!` is left adjoint to `g^*`, by an adjunction whose unit is an isomorphism;
* `g^* ∘ Lg_! = id`.

The structure sheaf is the one of **Stacks 06TV**, with sections in `Type u`, and the modules
have their sections in `Type (u+1)`. -/
@[stacks 07AS "part (2), the whole of it: existence of the unbounded left derived functor \
`Lg_!` of `g_!` on sheaves of modules for the lisse-étale site, its adjunction \
`Lg_! ⊣ g^*` (with invertible unit), and `g^* ∘ Lg_! = id`, for every algebraic stack and with \
NO hypothesis. The structure sheaf is the one of Tag 06TV; the acyclicity statement of Tag 07AC \
is a theorem here, `AlgebraicGeometry.Stack.subsiteLowerShriekModulesAcyclic`, and the \
invertibility of the ordinary unit is Tag 077I"]
theorem lowerShriekModules_derived :
    (FreeRingUniverse.lowerShriekOnHomotopy.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (ambientTopology B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒳).ι
        (moduleRing.{u, w} B S hS 𝒳) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (FreeRingUniverse.sourceQuasiIso.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (ambientTopology B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒳).ι
        (moduleRing.{u, w} B S hS 𝒳)) ∧
    (∃ adj : derivedLowerShriekModules B S hS 𝒳 ⊣ derivedRestrictionModules B S hS 𝒳,
      IsIso adj.unit) ∧
    Nonempty (derivedLowerShriekModules B S hS 𝒳 ⋙ derivedRestrictionModules B S hS 𝒳 ≅
      𝟭 (DerivedCategory (SheafOfModules.{u + 1} (subsiteModuleRingSmooth B S hS 𝒳)))) :=
  ⟨hasPointwiseLeftDerivedLowerShriekModules B S hS 𝒳,
    ⟨derivedLowerShriekModulesAdjunction B S hS 𝒳,
      isIso_derivedSubsiteLowerShriekModulesAdjunction_unit B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
        (smoothObject.{u, w} B S hS 𝒳)⟩,
    ⟨derivedLowerShriekModulesRestrictionIso B S hS 𝒳⟩⟩

end LisseEtale

end AlgebraicGeometry.Stack

end
