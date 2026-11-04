module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image commutes with étale restriction

For a cartesian square of algebraic spaces with `g : Y' ⟶ Y` étale and base change `i : X' ⟶ X` of
`g`, restriction along `g` of the derived direct image along `f` is the derived direct image along
`f'` of the restriction along `i`: `(Rf_*E)|_{Y'} ≅ Rf'_*(E|_{X'})`. Restriction along an étale
morphism preserves K-injective complexes.

## Main results

* `AlgebraicGeometry.Space.isKInjective_etaleModulePullback_of_isEtale`: restriction along an
  étale morphism of algebraic spaces preserves K-injective complexes.
* `AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIsoOfIsEtale`: the isomorphism
  `(Rf_*E)|_{Y'} ≅ Rf'_*(E|_{X'})`.

## References

* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- Restriction of modules along an étale morphism `f : X ⟶ Y` of algebraic spaces carries a
K-injective complex of `𝒪_Y`-modules to a K-injective complex of `𝒪_X`-modules. -/
theorem isKInjective_etaleModulePullback_of_isEtale
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((etaleModulePullback.{u, u} B S hS f hf).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  isKInjective_etaleModulePullback B S hS f hf (etaleModuleLowerShriekAdjunction B S hS f hf) I hI

variable {X Y X' Y' : AlgebraicSpaces B S hS} {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y}

/-- Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let
`g : Y' ⟶ Y` be an étale morphism, set `X' = Y' ×_Y X` (the square `sq` is cartesian) and let
`f' : X' ⟶ Y'` be the projection. Then `(Rf_*E)|_{Y'} ≅ Rf'_*(E|_{X'})` naturally in `E ∈ D(𝒪_X)`,
where `Rf`, `Rf'`, `Ri` and `Rg` are any right derived functors of the direct images along `f`,
`f'` and of the restrictions along `i`, `g`, with units `αf`, `αf'`, `αi` and `αg`. -/
@[stacks 08GE]
def derivedModulePushforwardEtaleRestrictIsoOfIsEtale (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X'.1 X'.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y'.1 Y'.2)]
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (Rf' : DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2))
    (Ri : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2))
    (Rg : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2))
    (αf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    (αf' : (modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
    (αi : (etaleModulePullback.{u, u} B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)
    (αg : (etaleModulePullback.{u, u} B S hS g hg).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    [Rf'.IsRightDerivedFunctor αf'
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X'.1 X'.2) (ComplexShape.up ℤ))]
    [Ri.IsRightDerivedFunctor αi
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))] :
    Rf ⋙ Rg ≅ Ri ⋙ Rf' :=
  derivedModulePushforwardEtaleRestrictIso B S hS sq hg
    (etaleModuleLowerShriekAdjunction B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    Rf Rf' Ri Rg αf αf' αi αg

end AlgebraicGeometry.Space

end
