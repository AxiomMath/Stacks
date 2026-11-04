module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.AffineBaseChangeDerived

/-!
# Derived global sections on the big affine fppf site exist

`AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison` is stated for an *arbitrary* total
right derived functor `RΓ` of global sections, taken as a parameter together with its universal
unit and the hypothesis `CategoryTheory.Functor.IsRightDerivedFunctor`. That phrasing says
nothing on its own about whether such a functor exists, and a theorem quantified over an
uninhabited parameter is empty. This module discharges that: the hypothesis triple is inhabited,
so the comparison theorem has content.

Sheaves of `𝒪`-modules on `(Aff/Spec A)_fppf` are a Grothendieck abelian category
(`AlgebraicGeometry.BigAffineFppf.affineFppf_modules_grothendieck`), so every cochain complex of
them admits a quasi-isomorphism into a K-injective complex
(`Stacks.Injectives.kInjectiveResolutionInclusion`, Tag 079P). Tag 070K, in the
`CategoryTheory.Functor` namespace as
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`,
turns that into a pointwise right derived functor of *every* functor out of the homotopy
category, in particular of global sections, and Mathlib's
`CategoryTheory.Functor.totalRightDerived` then names the functor.

## Main results

* `AlgebraicGeometry.BigAffineFppf.hasRightDerivedFunctor_homotopyGlobalSections`: global
  sections on the homotopy category have a right derived functor along the localization at the
  quasi-isomorphisms.
* `AlgebraicGeometry.BigAffineFppf.exists_isRightDerivedFunctor_homotopyGlobalSections`: the
  hypotheses of `AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison` are inhabited.
* `AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison_totalRightDerived`: the comparison
  theorem applied to the canonical derived functor, with no derived-functor parameter left.

## References

* [Stacks Project, Tag 0H0U](https://stacks.math.columbia.edu/tag/0H0U)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

-- The same ambient-universe instances that
-- `StacksFrontier/AlgebraicGeometry/Topologies/Fppf/AffineBaseChangeDerived.lean` removes: the
-- sheaves of modules here have their sections a universe below the objects of the site, which
-- those instances cannot describe, and left in place they leave the universe of every statement
-- about them unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u

namespace AlgebraicGeometry.BigAffineFppf

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (A : CommRingCat.{u})
  (hS : B.Contains (Spec A))

attribute [local instance] HasDerivedCategory.standard

/-- The category of sheaves of `𝒪`-modules on `(Aff/Spec A)_fppf` is Grothendieck abelian. -/
local instance : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheaf B A hS)) :=
  affineFppf_modules_grothendieck B A hS

/-- Every cochain complex of sheaves of `𝒪`-modules on `(Aff/Spec A)_fppf` admits a
quasi-isomorphism into a K-injective complex. -/
public lemma exists_quasiIso_isKInjective_sheafOfModules
    (K : CochainComplex (SheafOfModules.{u} (structureSheaf B A hS)) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheaf B A hS)) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor _).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion _).app K, inferInstance, inferInstance⟩

/-- **Derived global sections are defined everywhere.** Global sections on the homotopy category
of complexes of sheaves of `𝒪`-modules on `(Aff/Spec A)_fppf`, followed by localization, have a
*pointwise* right derived functor: K-injective resolutions exist because the category is
Grothendieck abelian, and Tag 070K converts them into one. -/
public lemma hasPointwiseRightDerivedFunctor_homotopyGlobalSections :
    (homotopyGlobalSections B A hS).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS))
        (ComplexShape.up ℤ)) :=
  -- The second conjunct of Tag 070K quantifies over an arbitrary localization target, whose
  -- universes this projection leaves free; they are pinned here.
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (homotopyGlobalSections B A hS) (exists_quasiIso_isKInjective_sheafOfModules B A hS)).1

/-- **Derived global sections exist.** The functor of the previous lemma has a total right
derived functor along the localization at the quasi-isomorphisms. -/
public lemma hasRightDerivedFunctor_homotopyGlobalSections :
    (homotopyGlobalSections B A hS).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS))
        (ComplexShape.up ℤ)) :=
  have := hasPointwiseRightDerivedFunctor_homotopyGlobalSections B A hS
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

attribute [local instance] hasRightDerivedFunctor_homotopyGlobalSections

/-- **The hypotheses of `AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison` are
inhabited.** There is a functor `RΓ` on derived categories together with a unit exhibiting it as
a total right derived functor of global sections, so that theorem is not vacuous. -/
public theorem exists_isRightDerivedFunctor_homotopyGlobalSections :
    ∃ (RGamma : DerivedCategory (SheafOfModules.{u} (structureSheaf B A hS)) ⥤
        DerivedCategory (ModuleCat.{u} A))
      (unit : homotopyGlobalSections B A hS ⟶ DerivedCategory.Qh ⋙ RGamma),
      RGamma.IsRightDerivedFunctor unit
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS))
          (ComplexShape.up ℤ)) :=
  ⟨_, (homotopyGlobalSections B A hS).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS))
      (ComplexShape.up ℤ)), inferInstance⟩

/-- **Stacks 0H0U for the canonical derived functor.** The conclusion of
`AlgebraicGeometry.BigAffineFppf.isIso_derivedComparison` with no derived-functor parameter
left: for the total right derived functor of global sections supplied by
`CategoryTheory.Functor.totalRightDerived`, the canonical map
`M^• ⟶ RΓ((Aff/S)_fppf, F^•)` is a quasi-isomorphism. -/
@[stacks 0H0U "the canonical map M^• ⟶ RΓ((Aff/S)_fppf, F^•) is a quasi-isomorphism, for the \
canonical total right derived functor of global sections -- no derived-functor parameter assumed"]
public theorem isIso_derivedComparison_totalRightDerived
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (derivedComparison B A hS
      ((homotopyGlobalSections B A hS).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS))
          (ComplexShape.up ℤ)))
      ((homotopyGlobalSections B A hS).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf B A hS))
          (ComplexShape.up ℤ))) M) :=
  isIso_derivedComparison B A hS _ _ inferInstance M

end AlgebraicGeometry.BigAffineFppf

end
