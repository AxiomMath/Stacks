module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleInverseImagePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjointAcyclicObjects
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded left derived lower shriek on sheaves of modules for a morphism of fibred
categories

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and let `g : (Sh(C'), O_{C'}) ⟶ (Sh(C), O_C)` be the morphism of
ringed topoi it induces. Stacks 08PC part (1) gives the lower-shriek functor
`g_! : Mod(O_{C'}) ⥤ Mod(O_C)`, the left adjoint of `g^*`, as
`Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriek`. **Stacks 08PC part (3) for
sheaves of modules** asserts that `g_!` has an unbounded left derived functor
`Lg_! : D(O_{C'}) ⥤ D(O_C)` and that `Lg_!` is left adjoint to `g^*` on the unbounded derived
categories.

This file is the module-sheaf counterpart of the abelian-sheaf development in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/DerivedLowerShriekFunctoriality.lean`,
which carries `Lg_!^{Ab}` and its derived adjunction for the same situation. As there, the
existence of the derived functor is the criterion of Stacks 0794 run at the class `P` of direct
sums of the extensions by zero `j_{U'!} O_{U'}`, and every hypothesis of that criterion is
discharged here for this situation except the one that is the mathematical content of Stacks
07AC: that `g_!` carries a bounded above acyclic complex with terms in `P` to an acyclic
complex. That single statement is `MorphismSituation.ModuleLowerShriekAcyclic` and is carried as
an explicit argument.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.ModuleLowerShriekAcyclic`: the acyclicity
  statement of Stacks 07AC for `g_!` on sheaves of modules at this situation.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriekAcyclic_of_ext_vanishing`: that
  statement reduced to the `Ext` vanishing of Stacks 0D6X in the category of sheaves of modules.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriekOnHomotopy`,
  `moduleInverseImageOnHomotopy` and `moduleHomotopyAdjunction`: `g_!`, `g^*` and their
  adjunction, read degreewise on the unbounded homotopy categories.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedModuleInverseImage`: `g^*` on the
  unbounded derived categories, induced degreewise because `g^*` is exact.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedModuleLowerShriek`: `Lg_!`, the total
  left derived functor of degreewise `g_!`, with its counit
  `derivedModuleLowerShriekComparison`.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.hasPointwiseLeftDerivedModuleLowerShriek`:
  **Stacks 08PC part (3) for sheaves of modules, existence**, conditional on
  `ModuleLowerShriekAcyclic`.
* `MorphismSituation.isLeftDerivedFunctor_derivedModuleLowerShriek_comp`:
  `Lg_!` stays a left derived functor after composition with any functor out of `D(O_C)`, which
  is the absoluteness hypothesis that the derived adjunction of Stacks 09T5 imposes.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedModuleLowerShriekAdjunction`:
  **Stacks 08PC part (3) for sheaves of modules, the adjunction** `Lg_! ⊣ g^*`, conditional on
  the same statement, together with the two factorizations
  `derivedModuleLowerShriekAdjunction_unit_fac` and
  `derivedModuleLowerShriekAdjunction_counit_fac` of its unit and counit through the canonical
  comparisons.

## Why nothing here carries the tag of Stacks 08PC

The declarations below take the acyclicity statement `ModuleLowerShriekAcyclic` of Stacks 07AC
as their one argument. It is discharged in `MorphismModuleLowerShriekAcyclic.lean`
(`MorphismSituation.moduleLowerShriekAcyclic`), from part (2) of Stacks 08PC and the vanishing of
Stacks 0D6X for the abelian sheaves underlying the `j_{U'!} O_{U'}`; the unconditional statements
of part (3) for sheaves of modules,
`MorphismSituation.hasPointwiseLeftDerivedModuleLowerShriekUnconditional` and
`MorphismSituation.derivedModuleLowerShriekAdjunctionUnconditional`, are registered there. Parts
(2) and (4) are in `ModuleLowerShriekForgetSquare.lean` and `ModuleDerivedLowerShriekForget.lean`.

## Implementation notes

The ring sheaves are taken in the ringed-topos spelling
`Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O` and
`… (S.totalTopos S.pi)`, which is the spelling part (1) pins into the types of
`MorphismSituation.moduleInverseImage` and `MorphismSituation.moduleLowerShriek`. Writing the
rings at `S.sourceTopology` instead leaves the universe of the module sections an uninvertible
`max`, the friction recorded in the implementation notes of `ModuleInverseImage.lean`; there is
no second spelling of either ring here and so no conversion between two of them.

Smallness of the source fibred category in the universe of the sections, which the generating
lemma of Stacks 03EW (3) needs, is taken locally from `small_max` inside the two theorems that
use it rather than registered as an instance: the abelian development already carries that
instance as `MorphismSituation.small_source`, and a second copy of it here would be duplicate
infrastructure.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w t

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})
  [HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.sourceTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [HasSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [HasSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]

/-- Abelian sheaves can be sheafified on the source ringed topos. Registered separately from the
instance for `S.sourceTopology`, exactly as `MorphismSituation.hasWeakSheafifySourceTopos` is:
instance search does not see through the `sourceTopos` projection, and it is `HasSheafify` at this
spelling that Mathlib's `Abelian (SheafOfModules R)` asks for once `R` is a structure sheaf given
in ringed-topos form. Without it instance search goes off to re-derive sheafification of abelian
groups from scratch and fails on the universe constraint `max u₁ v₁ =?= max w u₀ u₁ u₂ v₀ v₁ v₂`,
the site's universes against the universe of the sections. -/
instance hasSheafifySourceTopos
    (π' : _root_.MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    HasSheafify (S.sourceTopos π').J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  inferInstanceAs (HasSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- Abelian sheaves can be sheafified on the target ringed topos. The mirror of
`hasSheafifySourceTopos`, needed for the same reason. -/
instance hasSheafifyTotalTopos
    (π : _root_.MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    HasSheafify (S.totalTopos π).J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  inferInstanceAs (HasSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- `O_{C'}`, the structure sheaf of the source ringed topos read as a sheaf of rings. This is
the ring over which the source of `MorphismSituation.moduleLowerShriek` is taken. -/
abbrev sourceModuleRing :=
  Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O

/-- `O_C`, the structure sheaf of the target ringed topos read as a sheaf of rings. This is the
ring over which the target of `MorphismSituation.moduleLowerShriek` is taken. -/
abbrev totalModuleRing :=
  Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O

/-- Sheaves of `O_C`-modules form a Grothendieck abelian category, the universes of the site, of
its morphisms, of the sheaf of rings and of the module sections being related by `UnivLE`. This
is what makes the unbounded derived category of `Mod(O_C)` carry the localization theory the
derived adjunction of Stacks 09T5 needs.

The four universes are written out: the statement determines the universe of the sections only
inside the `max` that fixes it, and `SheafOfModules.isGrothendieckAbelian_of_univLE` leaves it a
metavariable when it is not given, Lean's level normaliser having no way to invert a `max`. -/
instance isGrothendieckAbelianTotalModules :
    IsGrothendieckAbelian.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE.{max w u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁,
    max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing

/-- `g_!` preserves finite colimits, being a left adjoint. -/
instance moduleLowerShriekPreservesFiniteColimits :
    PreservesFiniteColimits S.moduleLowerShriek :=
  have : PreservesColimitsOfSize.{max w u₀ u₁ u₂ v₀ v₁ v₂, max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.moduleLowerShriek :=
    S.moduleLowerShriekAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} S.moduleLowerShriek :=
    preservesColimitsOfSize_shrink _
  inferInstance

/-- `g_!` commutes with `ℕ`-indexed colimits, being a left adjoint. This is the last of the four
conditions of Stacks 0794. -/
instance moduleLowerShriekPreservesColimitsOfShapeNat :
    PreservesColimitsOfShape ℕ S.moduleLowerShriek :=
  have : PreservesColimitsOfSize.{max w u₀ u₁ u₂ v₀ v₁ v₂, max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.moduleLowerShriek :=
    S.moduleLowerShriekAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} S.moduleLowerShriek :=
    preservesColimitsOfSize_shrink _
  inferInstance

/-- **The acyclicity statement of Stacks 07AC for `g_!` on sheaves of modules.** Lower shriek
along the 1-morphism of fibred categories carries a bounded above acyclic complex of
`O_{C'}`-modules whose terms are direct sums of the extensions by zero `j_{U'!} O_{U'}` of the
structure sheaves of the slices of `C'` to an acyclic complex of `O_C`-modules.

This is the one statement of Stacks 07AC that is not formal, and the only argument the
existence and adjunction statements below take. -/
abbrev ModuleLowerShriekAcyclic : Prop :=
  ∀ (a : ℤ)
    (L : CochainComplex
      (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) ℤ),
    L.IsStrictlyLE a →
    (∀ n, Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits
      S.sourceModuleRing (L.X n)) → L.Acyclic →
    ((S.moduleLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic

/-- **The acyclicity statement of Stacks 07AC for `g_!` on sheaves of modules follows from the
vanishing of Stacks 0D6X.** If `Ext^n_{O_{C'}}(j_{U'!} O_{U'}, g^* I) = 0` for every object `U'`
of the source fibred category, every injective `O_C`-module `I` and every `n ≥ 1`, then `g_!`
carries every bounded above acyclic complex with terms in the class of direct sums of the
`j_{U'!} O_{U'}` to an acyclic complex.

The module-side counterpart of
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing`, and the same
formal argument: `CategoryTheory.Adjunction.map_acyclic_of_extAcyclic` for the adjunction
`g_! ⊣ g^*` of part (1), with the hypothesis saying exactly that each `j_{U'!} O_{U'}` is
`Ext`-acyclic for it, `CategoryTheory.Adjunction.extAcyclic_coproduct` closing that class under
the direct sums that make up the terms of such a complex, and
`CategoryTheory.Adjunction.extAcyclic_of_iso` transporting along the isomorphism exhibiting a term
as such a sum.

So the whole of part (3) for sheaves of modules rests on that `Ext` vanishing; the module
docstring above records what stands between it and the full Stacks 0D6X. `HasExt` is an instance
binder rather than inferred: synthesising it for `SheafOfModules S.sourceModuleRing` runs out of
heartbeats, and the abelian counterpart takes it as a binder for the same reason. -/
theorem moduleLowerShriekAcyclic_of_ext_vanishing
    [HasExt.{t} (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing)]
    (hExt : ∀ (U' : S.source)
        (I : SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing), Injective I →
        ∀ n : ℕ, 1 ≤ n → Subsingleton (Abelian.Ext
          (Cohomology.DerivedLowerShriek.extensionByZeroUnit S.sourceModuleRing U')
          (S.moduleInverseImage.obj I) n)) :
    S.ModuleLowerShriekAcyclic := by
  intro a L hLE hLP hLac
  have := hLE
  refine S.moduleLowerShriekAdjunction.map_acyclic_of_extAcyclic L a hLac fun n => ?_
  obtain ⟨ι, U, ⟨e⟩⟩ := hLP n
  exact S.moduleLowerShriekAdjunction.extAcyclic_of_iso e
    (S.moduleLowerShriekAdjunction.extAcyclic_coproduct _ fun i => hExt (U i))

/-- `g_!` applied degreewise to unbounded complexes of sheaves of modules, read on the homotopy
categories. -/
abbrev moduleLowerShriekOnHomotopy :
    HomotopyCategory
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) (ComplexShape.up ℤ) ⥤
      HomotopyCategory
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) (ComplexShape.up ℤ) :=
  S.moduleLowerShriek.mapHomotopyCategory (ComplexShape.up ℤ)

/-- `g^*` applied degreewise to unbounded complexes of sheaves of modules, read on the homotopy
categories. -/
abbrev moduleInverseImageOnHomotopy :
    HomotopyCategory
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) (ComplexShape.up ℤ) ⥤
      HomotopyCategory
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) (ComplexShape.up ℤ) :=
  S.moduleInverseImage.mapHomotopyCategory (ComplexShape.up ℤ)

/-- The adjunction `g_! ⊣ g^*` of Stacks 08PC part (1), read on the unbounded homotopy
categories. Its unit and counit are the degreewise unit and counit of
`MorphismSituation.moduleLowerShriekAdjunction`. -/
abbrev moduleHomotopyAdjunction :
    S.moduleLowerShriekOnHomotopy ⊣ S.moduleInverseImageOnHomotopy :=
  S.moduleLowerShriekAdjunction.mapHomotopyCategory (ComplexShape.up ℤ)

/-- The quasi-isomorphisms of the unbounded homotopy category of `Mod(O_{C'})`, the class at
which the left derived functor of `g_!` is taken. -/
abbrev moduleSourceQuasiIso :
    MorphismProperty
      (HomotopyCategory
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso
    (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) (ComplexShape.up ℤ)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The smallness of the source and the exactness of `ℕ`-indexed colimits on both module
categories, as needed by the criterion of Stacks 0794. -/
private theorem small_source_and_hasExactColimitsOfShape_nat :
    Small.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.source ∧
      HasExactColimitsOfShape ℕ
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) ∧
      HasExactColimitsOfShape ℕ
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) :=
  ⟨small_max.{max w u₀ u₁ v₀ v₁ v₂, u₂} _,
    Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat _,
    Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat _⟩

/-- **Stacks 08PC part (3) for sheaves of modules, existence**, conditional on the acyclicity
statement of Stacks 07AC. Degreewise `g_!`, followed by the localization of the homotopy category
of `Mod(O_C)`, has a pointwise left derived functor along the localization of the homotopy
category of `Mod(O_{C'})`.

Every other hypothesis of the criterion of Stacks 0794 is discharged here, with the class of
objects taken to be the direct sums of the `j_{U'!} O_{U'}`: that class contains a zero object,
is closed under binary direct sums and generates — the last being Stacks 03EW (3), which needs
smallness of `C'` in the universe of the sections — `ℕ`-indexed colimits exist and are exact in
sheaves of modules on either site, and `g_!` is additive and commutes with all colimits, being a
left adjoint. -/
theorem hasPointwiseLeftDerivedModuleLowerShriek (h : S.ModuleLowerShriekAcyclic) :
    (S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      S.moduleSourceQuasiIso := by
  obtain ⟨_, _, _⟩ := S.small_source_and_hasExactColimitsOfShape_nat
  exact Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    S.moduleLowerShriek
    (Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits S.sourceModuleRing)
    (fun _ _ => Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnits_biprod _)
    (fun M => Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnits _ M) h

/-- `g^* : D(O_C) ⥤ D(O_{C'})` on the unbounded derived categories, induced degreewise because
`g^*` is exact (`MorphismSituation.moduleInverseImage_exact`). -/
abbrev derivedModuleInverseImage :
    DerivedCategory (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) ⥤
      DerivedCategory (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) :=
  S.moduleInverseImage.mapDerivedCategory

/-- The comparison from degreewise `g^*` to `g^*` on the derived categories. It is an
isomorphism, `g^*` being exact. -/
abbrev derivedModuleInverseImageComparison :
    S.moduleInverseImageOnHomotopy ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ S.derivedModuleInverseImage :=
  S.moduleInverseImage.mapDerivedCategoryFactorsh.inv

/-- `g^*` on the derived categories is the right derived functor of degreewise `g^*`, its
comparison transformation being invertible. -/
instance isRightDerivedFunctorDerivedModuleInverseImage :
    S.derivedModuleInverseImage.IsRightDerivedFunctor S.derivedModuleInverseImageComparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    S.moduleInverseImage.mapDerivedCategoryFactorsh

variable [(S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  S.moduleSourceQuasiIso]

/-- **`Lg_! : D(O_{C'}) ⥤ D(O_C)`**, the unbounded total left derived functor of lower shriek on
sheaves of modules along the 1-morphism of fibred categories. -/
abbrev derivedModuleLowerShriek :
    DerivedCategory (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) ⥤
      DerivedCategory (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) :=
  (S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
    S.moduleSourceQuasiIso

/-- The comparison `Lg_! ⟶ g_!` on the homotopy category: the counit exhibiting `Lg_!` as a left
derived functor of degreewise `g_!`. -/
abbrev derivedModuleLowerShriekComparison :
    DerivedCategory.Qh ⋙ S.derivedModuleLowerShriek ⟶
      S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh :=
  (S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
    S.moduleSourceQuasiIso

/-- **`Lg_!` is absolute.** Under the acyclicity statement of Stacks 07AC, `Lg_!` stays a left
derived functor after composition with any functor out of `D(O_C)`, because it is constructed by
resolutions. Taking that functor to be `derivedModuleInverseImage` is exactly the hypothesis the
derived adjunction of Stacks 09T5 imposes on its left derived functor. -/
theorem isLeftDerivedFunctor_derivedModuleLowerShriek_comp
    (h : S.ModuleLowerShriekAcyclic)
    {E : Type*} [Category E]
    (G : DerivedCategory (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) ⥤ E) :
    (S.derivedModuleLowerShriek ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh S.derivedModuleLowerShriek G).inv ≫
        Functor.whiskerRight S.derivedModuleLowerShriekComparison G)
      S.moduleSourceQuasiIso := by
  obtain ⟨_, _, _⟩ := S.small_source_and_hasExactColimitsOfShape_nat
  exact Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    S.moduleLowerShriek
    (Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits S.sourceModuleRing)
    (fun _ _ => Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnits_biprod _)
    (fun M => Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnits _ M) h
    DerivedCategory.Qh S.derivedModuleLowerShriek S.derivedModuleLowerShriekComparison G

/-- **Stacks 08PC part (3) for sheaves of modules, the adjunction**, conditional on the
acyclicity statement of Stacks 07AC: the unbounded left derived lower-shriek functor `Lg_!` is
left adjoint to `g^*` on the unbounded derived categories. This is Stacks 09T5 on the unbounded
derived category of the Grothendieck abelian category `Mod(O_C)`; the acyclicity statement enters
twice, once for the existence of `Lg_!` and once through
`isLeftDerivedFunctor_derivedModuleLowerShriek_comp` to make it stay a left derived functor after
composition with derived `g^*`. -/
def derivedModuleLowerShriekAdjunction (h : S.ModuleLowerShriekAcyclic) :
    S.derivedModuleLowerShriek ⊣ S.derivedModuleInverseImage :=
  have := S.isLeftDerivedFunctor_derivedModuleLowerShriek_comp h S.derivedModuleInverseImage
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction S.moduleHomotopyAdjunction
    S.moduleSourceQuasiIso S.derivedModuleLowerShriekComparison
    S.derivedModuleInverseImageComparison

/-- **Stacks 08PC part (3) for sheaves of modules**, unit factorization: the unit of the derived
adjunction is the one induced by the unit of the ordinary adjunction `g_! ⊣ g^*` of part (1),
through the two canonical comparison transformations. -/
theorem derivedModuleLowerShriekAdjunction_unit_fac (h : S.ModuleLowerShriekAcyclic)
    (M : HomotopyCategory
      (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) (ComplexShape.up ℤ)) :
    (S.derivedModuleLowerShriekAdjunction h).unit.app (DerivedCategory.Qh.obj M) ≫
        S.derivedModuleInverseImage.map (S.derivedModuleLowerShriekComparison.app M) =
      DerivedCategory.Qh.map (S.moduleHomotopyAdjunction.unit.app M) ≫
        S.derivedModuleInverseImageComparison.app (S.moduleLowerShriekOnHomotopy.obj M) :=
  have := S.isLeftDerivedFunctor_derivedModuleLowerShriek_comp h S.derivedModuleInverseImage
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction_unit_app S.moduleHomotopyAdjunction
    S.moduleSourceQuasiIso S.derivedModuleLowerShriekComparison
    S.derivedModuleInverseImageComparison M

/-- **Stacks 08PC part (3) for sheaves of modules**, counit factorization: the counit of the
derived adjunction is the one induced by the counit of the ordinary adjunction `g_! ⊣ g^*` of
part (1), through the two canonical comparison transformations. -/
theorem derivedModuleLowerShriekAdjunction_counit_fac (h : S.ModuleLowerShriekAcyclic)
    (N : HomotopyCategory
      (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) (ComplexShape.up ℤ)) :
    S.derivedModuleLowerShriek.map (S.derivedModuleInverseImageComparison.app N) ≫
        (S.derivedModuleLowerShriekAdjunction h).counit.app (DerivedCategory.Qh.obj N) =
      S.derivedModuleLowerShriekComparison.app (S.moduleInverseImageOnHomotopy.obj N) ≫
        DerivedCategory.Qh.map (S.moduleHomotopyAdjunction.counit.app N) :=
  have := S.isLeftDerivedFunctor_derivedModuleLowerShriek_comp h S.derivedModuleInverseImage
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction_counit_app S.moduleHomotopyAdjunction
    S.moduleSourceQuasiIso S.derivedModuleLowerShriekComparison
    S.derivedModuleInverseImageComparison N

end Derived

end Stacks.Sites.FibredCategory.MorphismSituation

end
