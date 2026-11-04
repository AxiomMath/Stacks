module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic

/-!
# Sheaves of modules on the small étale site and their derived functors

Fix a ring `Λ`.  Sheaves of `Λ`-modules on the small étale site of a scheme `X` form a
Grothendieck abelian category, hence one with enough injectives and a derived category.  This
file records that category together with the four functors between such categories that
cohomology with compact support is built from — direct image `f_*` along an arbitrary morphism
of schemes, restriction `j^{-1}` and extension by zero `j_!` along an étale morphism, and
global sections `Γ` — and the bounded below right derived functor of each.

## Main definitions

* `Stacks.EtaleCohomology.EtaleModules`: sheaves of `Λ`-modules on the small étale site.
* `Stacks.EtaleCohomology.etaleModuleDirectImage`, `etaleModuleRestriction`,
  `etaleModuleExtensionByZero` and `etaleModuleGlobalSections`: the four underived functors.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImage`,
  `etaleModuleDerivedExtensionByZero` and `etaleModuleDerivedGlobalSections`: their right
  derived functors on bounded below derived categories.

## Main results

* `Stacks.EtaleCohomology.etaleModules_isGrothendieckAbelian` and
  `Stacks.EtaleCohomology.etaleModules_enoughInjectives`: the category is Grothendieck abelian
  and has enough injectives.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj`: `j_! ⊣ j^{-1}`.

## Implementation notes

Coefficients are `ModuleCat.{max (u + 1) r} Λ` for a scheme universe `u` and a ring universe
`r`.  The cutoff `u + 1` is forced twice: the objects of the small étale site of a scheme in
`Scheme.{u}` live in `Type (u + 1)`, so the coefficient category has to receive the colimits
computing the left Kan extension that defines `j_!`, and it has to be large enough for the site
to be essentially small in it.  The instances on the coefficient category itself are stated for
an arbitrary coefficient universe `s` in which `Λ` is small, so that they apply at the chosen
cutoff with no further hypothesis.

Extension by zero is the sheafified left Kan extension along composition with the étale
morphism, i.e. Mathlib's `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`, and
restriction is literally precomposition with that functor of sites; the two are adjoint.  Both
site functors are continuous, which is
`Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous` for base change and
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_isContinuous` for composition with an étale
morphism.

Global sections are Mathlib's `CategoryTheory.Sheaf.Γ`, the right adjoint of the constant sheaf
functor; it exists because the small étale site of `X` has a terminal object, namely `X` itself,
and on that site it is the functor of sections over `X`.

The derived functors are the bounded below ones, obtained from injective resolutions by
`CategoryTheory.Functor.rightDerivedFunctorPlus`.  The derived category used throughout is the
one of `CategoryTheory.HasDerivedCategory.standard`, made a local instance as elsewhere in this
development.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe t u r s

namespace Stacks.EtaleCohomology

section Coefficients

variable (Λ : Type r) [Ring Λ]

/-- Modules in a universe in which the ring is small have limits of every size that universe
accommodates.  This is Mathlib's `ModuleCat.hasLimitsOfSize`, which is not an instance. -/
theorem moduleCat_hasLimitsOfSize [UnivLE.{u, s}] :
    HasLimitsOfSize.{t, u} (ModuleCat.{s} Λ) :=
  ModuleCat.hasLimitsOfSize

attribute [local instance] moduleCat_hasLimitsOfSize

/-- Modules over a ring satisfy Grothendieck's axiom AB5 in any universe: filtered colimits are
computed on underlying abelian groups, where they are exact. -/
instance moduleCat_ab5 : AB5 (ModuleCat.{s} Λ) where
  ofShape J _ _ := by
    let : PreservesColimits (forget₂ (ModuleCat.{s} Λ) AddCommGrpCat.{s}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{s, r, s, s} Λ
    exact HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{s} Λ) AddCommGrpCat.{s})

/-- Modules over a ring form a Grothendieck abelian category in any universe in which the ring
is small: the category satisfies AB5 and a shrunk copy of the ring is a separator. -/
instance moduleCat_isGrothendieckAbelian [Small.{s} Λ] :
    IsGrothendieckAbelian.{s} (ModuleCat.{s} Λ) where

/-- Module-valued presheaves on a small site can be sheafified, the coefficient category having
all the limits and colimits that the plus construction uses. -/
instance moduleCat_hasSheafify {C : Type s} [SmallCategory C] (J : GrothendieckTopology C)
    [Small.{s} Λ] : HasSheafify J (ModuleCat.{s} Λ) := by
  let : PreservesColimits (forget₂ (ModuleCat.{s} Λ) AddCommGrpCat.{s}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{s, r, s, s} Λ
  let : PreservesFilteredColimits (forget (ModuleCat.{s} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{s} Λ) AddCommGrpCat) (forget AddCommGrpCat)
  exact HasSheafify.mk' _ _ (plusPlusAdjunction J (ModuleCat.{s} Λ))

end Coefficients

section Category

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

attribute [local instance] moduleCat_hasLimitsOfSize

/-- Module-valued presheaves on the small étale site can be sheafified, by transport from a
small model of the site. -/
instance etaleModules_hasSheafify :
    HasSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) r} _ _

/-- Sheaves of `Λ`-modules on the small étale site of a scheme `X`, with coefficients in the
smallest universe containing both the objects of the site and the ring. -/
abbrev EtaleModules :=
  Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)

/-- Sheaves of `Λ`-modules on the small étale site of a scheme form an abelian category. -/
instance etaleModules_abelian : Abelian (EtaleModules.{u, r} Λ X) := inferInstance

/-- Sheaves of modules on the small étale site of a scheme form a Grothendieck abelian
category, transported along the equivalence with sheaves on a small model of the site. -/
instance etaleModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{max (u + 1) r} (EtaleModules.{u, r} Λ X) :=
  have : ∀ W : X.Etaleᵒᵖ,
      HasLimitsOfShape (StructuredArrow W (equivSmallModel.{max (u + 1) r} X.Etale).inverse.op)
        (ModuleCat.{max (u + 1) r} Λ) := fun _ ↦ inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _

/-- Sheaves of modules on the small étale site of a scheme have enough injectives, being a
Grothendieck abelian category. -/
instance etaleModules_enoughInjectives : EnoughInjectives (EtaleModules.{u, r} Λ X) :=
  have := etaleModules_isGrothendieckAbelian.{u, r} Λ X
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives

end Category

section Functors

variable (Λ : Type r) [Ring Λ]

/-- Direct image `f_*` of sheaves of modules along a morphism of schemes, for the small étale
topologies: restriction of sections along base change. -/
abbrev etaleModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ Y :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- Direct image of sheaves of modules is additive. -/
instance etaleModuleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDirectImage.{u, r} Λ f).Additive where
  map_add := by intros; rfl

/-- Restriction `j^{-1}` of sheaves of modules along an étale morphism: precomposition with
composition with `j`, so that `(j^{-1} G)(V) = G(V)` for `V` étale over the source. -/
abbrev etaleModuleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ U :=
  (Scheme.Etale.smallEtaleCompose j).sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) r} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- Restriction of sheaves of modules along an étale morphism is additive. -/
instance etaleModuleRestriction_additive {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleRestriction.{u, r} Λ j).Additive where
  map_add := by intros; rfl

/-- Extension by zero `j_!` of sheaves of modules along an étale morphism: the left adjoint of
restriction, realised as the sheafified left Kan extension along composition with `j`. -/
abbrev etaleModuleExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    EtaleModules.{u, r} Λ U ⥤ EtaleModules.{u, r} Λ X :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.Etale.smallEtaleCompose j)
    (ModuleCat.{max (u + 1) r} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- Extension by zero is left adjoint to restriction, on sheaves of modules. -/
def etaleModuleExtensionByZeroAdj {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleExtensionByZero.{u, r} Λ j ⊣ etaleModuleRestriction.{u, r} Λ j :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- Extension by zero of sheaves of modules is additive, being left adjoint to an additive
functor. -/
instance etaleModuleExtensionByZero_additive {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleModuleExtensionByZero.{u, r} Λ j).Additive :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ j).left_adjoint_additive

/-- Global sections of a sheaf of modules on the small étale site of `X`: the sections over the
terminal object `X` of the site, with their `Λ`-module structure. -/
abbrev etaleModuleGlobalSections (X : Scheme.{u}) :
    EtaleModules.{u, r} Λ X ⥤ ModuleCat.{max (u + 1) r} Λ :=
  Sheaf.Γ X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)

/-- Global sections of sheaves of modules is additive, being a right adjoint. -/
instance etaleModuleGlobalSections_additive (X : Scheme.{u}) :
    (etaleModuleGlobalSections.{u, r} Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

end Functors

section Derived

variable (Λ : Type r) [Ring Λ]

/-- The bounded below derived direct image `Rf_*` of sheaves of modules on small étale
sites. -/
abbrev etaleModuleDerivedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) :=
  (etaleModuleDirectImage.{u, r} Λ f).rightDerivedFunctorPlus

/-- The bounded below derived extension by zero `Rj_!` of sheaves of modules along an étale
morphism.  Extension by zero is exact, so this is extension by zero applied degreewise. -/
abbrev etaleModuleDerivedExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ U) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X) :=
  (etaleModuleExtensionByZero.{u, r} Λ j).rightDerivedFunctorPlus

/-- The bounded below derived global sections `RΓ(X, -)` of sheaves of modules on the small
étale site of `X`. -/
abbrev etaleModuleDerivedGlobalSections (X : Scheme.{u}) :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (etaleModuleGlobalSections.{u, r} Λ X).rightDerivedFunctorPlus

end Derived

end Stacks.EtaleCohomology

end
