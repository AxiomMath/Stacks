module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafificationAdjunctIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonRestrictionComposition

/-!
# The sheafified comparison of Stacks 0762, and `D_{LQCoh^fbc}`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `F` a presheaf of modules over
the structure sheaf of **Stacks 06TV**, and `φ : x ⟶ y` an arrow of `𝒳` lying over a morphism of
schemes `f : U ⟶ V`. **Stacks 06WC** is the comparison map
`c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}`, with `f_{small}^*` the pullback of *sheaves* of
modules, and **Stacks 0762** asks that `c_φ` be an isomorphism for every `φ` over a flat `f`.

The flat base change property in that reading,
`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`, the membership condition
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange` and the subcategory
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules` of `Mod(𝒪_𝒳)` are those of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafFlatBaseChangeProperty.lean`. This file
adds the comparison at one arrow, the identification of that condition with the invertibility of
the sheafified comparison, `LQCoh^fbc` inside the étale modules `Mod(𝒳_étale, 𝒪_𝒳)` of the
fibred site, and the derived subcategories `D_{LQCoh^fbc}(𝒪_𝒳)` and
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.

## Main definitions

* `AlgebraicGeometry.Stack.IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE`: the
  comparison `c_φ` of Stacks 06WC at one arrow becomes an isomorphism on the sheaf pullback.
* `AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChangeEtaleModulesUnivLE` and its
  module-universe-`u` form: `LQCoh^fbc(𝒪_𝒳)` inside `Mod(𝒳_étale, 𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentSheafFlatBaseChangeUnivLE` and
  `AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentSheafFlatBaseChangeUnivLE` (and
  their module-universe-`u` forms): `D_{LQCoh^fbc}(𝒪_𝒳)` and `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparisonUnivLE_iff_of_isSheaf`: when
  the presheaf pullback is a sheaf the presheaf and sheaf readings agree at that arrow.
* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictModulePullbackComparison_iff`: the condition
  at an arrow is the invertibility of the sheafified comparison.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModules_le` and
  `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeEtaleModules_le`: the presheaf-level
  `LQCoh^fbc` of the library is contained in these.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w m t d

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Predicate

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **The comparison `c_φ` of Stacks 06WC is an isomorphism of sheaves.** The presheaf comparison
`f^*_{psh}(F|_{V_ét}) ⟶ F|_{U_ét}` is locally injective and locally surjective for the small étale
topology of `U`, that is, it becomes an isomorphism after sheafification, where its source becomes
the pullback of sheaves `f_{small}^*(F|_{V_ét})`. -/
abbrev IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE [UnivLE.{u, m}]
    {x y : 𝒳} (φ : x ⟶ y)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) : Prop :=
  Presheaf.IsLocallyInjective
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F)) ∧
    Presheaf.IsLocallySurjective
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F))

/-- **Where the two readings of Stacks 0762 agree.** At an arrow `φ` where both the presheaf
pullback `f^*_{psh}(F|_{V_ét})` and the restriction `F|_{U_ét}` are sheaves, the comparison is an
isomorphism of presheaves exactly when it is locally bijective. -/
theorem isIso_restrictModulePullbackComparisonUnivLE_iff_of_isSheaf [UnivLE.{u, m}]
    {x y : 𝒳} (φ : x ⟶ y)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hsrc : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((PresheafOfModules.pullback.{m}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).presheaf)
    (htgt : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf) :
    IsIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F) ↔
      IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE B E h S hS p hp τ hτ φ F := by
  set J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  set c := restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F
  let f : (⟨_, hsrc⟩ : Sheaf J AddCommGrpCat.{m}) ⟶ ⟨_, htgt⟩ :=
    ⟨(PresheafOfModules.toPresheaf _).map c⟩
  have key : IsIso f ↔ IsIso c :=
    (isIso_iff_of_reflects_iso f (sheafToPresheaf J _)).symm.trans
      (isIso_iff_of_reflects_iso c (PresheafOfModules.toPresheaf _))
  rw [← key, ← Sheaf.isLocallyBijective_iff_isIso f]
  rfl

/-- **Stacks 0762 is the invertibility of the sheafified comparison.** At module universe `u`,
when the restriction `F|_{U_ét}` is a sheaf, the comparison of Stacks 06WC is locally bijective
exactly when the morphism of sheaves of modules it induces out of the sheafified pullback,
`(f^*_{psh}(F|_{V_ét}))^# ⟶ F|_{U_ét}`, is an isomorphism. The source of that morphism is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison` at `F|_{V_ét}`, which
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso` identifies with the pullback of sheaves
of modules along the morphism of ringed small étale sites; so this is the comparison map of the
source. -/
theorem isIso_sheafifiedRestrictModulePullbackComparison_iff {x y : 𝒳} (φ : x ⟶ y)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hx : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _
              (restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F x hx)).symm
          (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)) ↔
      Presheaf.IsLocallyInjective
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          ((PresheafOfModules.toPresheaf _).map
            (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)) ∧
        Presheaf.IsLocallySurjective
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          ((PresheafOfModules.toPresheaf _).map
            (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)) :=
  PresheafOfModules.isIso_sheafificationAdjunction_homEquiv_symm_iff (𝟙 _) _

end Predicate

section Classes

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The library's `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` is contained in the one of the source. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModules_le :
    locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳 ≤
      lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 :=
  fun F hF =>
    isLocallyQuasicoherentWithSheafFlatBaseChange_of_flatBaseChange B E h S hS _ _ F.val hF

/-- **The subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)`**, at a module universe `t` above the
universe of the schemes, with the flat base change property of **Stacks 0762** read with the
pullback of sheaves. -/
abbrev locallyQuasicoherentSheafFlatBaseChangeEtaleModulesUnivLE [UnivLE.{u, t}] :
    ObjectProperty (SheafOfModules.{t} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .etale)) :=
  fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val

/-- **The subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)`** at module universe `u`, with the
flat base change property of **Stacks 0762** read with the pullback of sheaves. -/
abbrev locallyQuasicoherentSheafFlatBaseChangeEtaleModules :
    ObjectProperty (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .etale)) :=
  locallyQuasicoherentSheafFlatBaseChangeEtaleModulesUnivLE.{u, w, u} B E h S hS 𝒳

/-- The library's `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒳_étale, 𝒪_𝒳)` is contained in the one of the
source. -/
theorem locallyQuasicoherentFlatBaseChangeEtaleModules_le :
    locallyQuasicoherentFlatBaseChangeEtaleModules B E h S hS 𝒳 ≤
      locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 :=
  fun F hF =>
    isLocallyQuasicoherentWithSheafFlatBaseChange_of_flatBaseChange B E h S hS _ _ F.val hF

end Classes

section Derived

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  [Abelian (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)]
  [HasDerivedCategory.{d} (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)] [UnivLE.{u, t}]

/-- **The subcategory `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)`**, with the flat base change property of
**Stacks 0762** read with the pullback of sheaves, at a module universe `t` above the universe
of the schemes: the complexes of fppf modules all of whose cohomology modules lie in
`LQCoh^fbc(𝒪_𝒳)`. -/
abbrev derivedLocallyQuasicoherentSheafFlatBaseChangeUnivLE :
    ObjectProperty (DerivedCategory (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (lqcohSheafFbcFppfModules.{u, w, t} B E h S hS 𝒳)

/-- **The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)`**, with the flat base change
property of **Stacks 0762** read with the pullback of sheaves, at a module universe `t` above
the universe of the schemes: the complexes of fppf modules all of whose cohomology modules are
parasitic (**Stacks 0773**) and lie in `LQCoh^fbc(𝒪_𝒳)`. -/
abbrev derivedParasiticLocallyQuasicoherentSheafFlatBaseChangeUnivLE :
    ObjectProperty (DerivedCategory (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (parasiticModules.{u, w, t} B S hS 𝒳 .fppf ⊓
      lqcohSheafFbcFppfModules.{u, w, t} B E h S hS 𝒳)

end Derived

section DerivedU

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  [Abelian (fppfModules B S hS 𝒳)] [HasDerivedCategory.{d} (fppfModules B S hS 𝒳)]

/-- **The subcategory `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)`** at module universe `u`, with the flat
base change property of **Stacks 0762** read with the pullback of sheaves. -/
abbrev derivedLocallyQuasicoherentSheafFlatBaseChange :
    ObjectProperty (DerivedCategory (fppfModules B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)

/-- **The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)`** at module universe `u`, with
the flat base change property of **Stacks 0762** read with the pullback of sheaves. -/
abbrev derivedParasiticLocallyQuasicoherentSheafFlatBaseChange :
    ObjectProperty (DerivedCategory (fppfModules B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf ⊓
      lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)

end DerivedU

end AlgebraicGeometry.Stack

end
