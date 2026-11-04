module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coextension of scalars for sheaves of modules preserves K-injectivity

For a morphism `φ : O ⟶ O'` of sheaves of rings on a site, the sheaf-level coextension of
scalars `Stacks.SheafOfModules.CoextendScalars.coextendScalars φ : SheafOfModules O ⥤
SheafOfModules O'` of Stacks Tag 0932 sends K-injective cochain complexes of `O`-modules to
K-injective cochain complexes of `O'`-modules.

## Main results

* `Stacks.SheafOfModules.CoextendScalars.coextendScalars_isKInjective`: the statement above.

## Implementation notes

A right adjoint whose left adjoint is exact preserves K-injectivity (Stacks 08BJ,
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`). The left adjoint of
`coextendScalars φ` is `SheafOfModules.restrictScalars φ`, which is exact because it commutes
with the forgetful functor to sheaves of abelian groups.

The additive structure on `coextendScalars φ` is the one supplied by its adjunction with
restriction of scalars (`Adjunction.right_adjoint_additive`).

## References

* [Stacks Project, Tag 0917](https://stacks.math.columbia.edu/tag/0917)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.SheafOfModules.CoextendScalars

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {O O' : Sheaf J RingCat.{u}}

/-- Restriction of scalars along `φ : O ⟶ O'`, followed by the forgetful functor to sheaves of
abelian groups, is the forgetful functor for `O'`-modules; the isomorphism is the identity on
components. -/
@[sga "4 IV 11.1.5" "partial"]
noncomputable def restrictScalarsCompToSheafIso (φ : O ⟶ O') :
    SheafOfModules.restrictScalars.{u} φ ⋙ SheafOfModules.toSheaf.{u} O ≅
      SheafOfModules.toSheaf.{u} O' :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite limits. -/
instance preservesFiniteLimits_restrictScalars (φ : O ⟶ O') :
    Limits.PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} φ) :=
  letI : Limits.PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u} φ ⋙ SheafOfModules.toSheaf.{u} O) :=
    Limits.preservesFiniteLimits_of_natIso (restrictScalarsCompToSheafIso φ).symm
  Limits.preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} O)

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite colimits. -/
instance preservesFiniteColimits_restrictScalars (φ : O ⟶ O') :
    Limits.PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} φ) :=
  letI : Limits.PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u} φ ⋙ SheafOfModules.toSheaf.{u} O) :=
    Limits.preservesFiniteColimits_of_natIso (restrictScalarsCompToSheafIso φ).symm
  Limits.preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} O)

/-- **Stacks Tag 0917, sheaf level.** Coextension of scalars, applied degreewise to cochain
complexes of sheaves of `O`-modules, sends K-injective complexes to K-injective complexes of
sheaves of `O'`-modules. -/
theorem coextendScalars_isKInjective (φ : O ⟶ O')
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    letI := (restrictScalars_coextendScalars_adjunction φ).right_adjoint_additive
    CochainComplex.IsKInjective
      (((coextendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  let : (coextendScalars φ).Additive :=
    (restrictScalars_coextendScalars_adjunction φ).right_adjoint_additive
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (restrictScalars_coextendScalars_adjunction φ) I

end Stacks.SheafOfModules.CoextendScalars

end
