module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Constant functions on the fibres of a family of curves, and its first higher direct image

This file sets up the statement of Stacks 0E1J. Let `f : X → S` be a family of curves
(Stacks 0D4Z). The lemma's hypothesis is that `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s` of
the base scheme `S`. Its conclusions are about `f_*𝒪_X` and the first higher direct image
`R¹f_*𝒪_X`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.residueFieldBase`: the residue-field point `Spec κ(s)` of the
  base, as an object of the big fppf site.
* `AlgebraicGeometry.CurveFamily.HasResidueFieldGlobalFunctions`: the hypothesis of Stacks 0E1J.
  For every point `s` of the base, pulling back global regular functions along
  `X_s = X ×_S Spec κ(s) → Spec κ(s)` is bijective.
* `AlgebraicGeometry.CurveFamily.HasFiniteLocallyFreeFirstHigherDirectImage`: part (2) of the
  conclusion, `R¹f_*𝒪_X` finite locally free.

## Main results

* `CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions`:
  "`f_*𝒪_X = 𝒪_S`, universally" (`AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions`, the
  conclusion of part (1) of Stacks 0E1J) implies the hypothesis of the lemma. It is the special
  case of the base change along `Spec κ(s) → S`.

## Implementation notes

The hypothesis is written in the same terms as
`AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions` (Stacks 0E6T), with the test space
restricted to the residue-field points of the base. So part (1) of Stacks 0E1J goes from
`HasResidueFieldGlobalFunctions` to `HasUniversallyBijectiveGlobalFunctions`, two statements in
the same language. The source's proof gets there from Stacks 0E6B, part (a), whose hypothesis
quantifies over all morphisms `Spec k → S` from a field. That reduction is flat base change of
global functions along the field extension `κ(s) ⊂ k`.

The total space of a family of curves is an algebraic space, so `R¹f_*𝒪_X` is a module on the
small étale site of the base, read as an algebraic space by `AlgebraicGeometry.schemeSpace`.
It is the right derived functor of `AlgebraicGeometry.Space.modulePushforward`. That is the
same functor in which `AlgebraicGeometry.Space.homologyDerivedModulePushforwardSingleIso`
computes the cohomology sheaves of the derived direct image.

No tag is placed in this file: it only states the vocabulary.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. (Not `private`: the exposed definitions below
cannot use private instances.) -/
local instance (priority := high) hasPullbacks_presheaf_curveFamilyFirstCohomology
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_curveFamilyFirstCohomology
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}


namespace CurveFamily

/-- The residue-field point `Spec κ(s)` of the base of a family of curves at a point `s`, as an
object of the big fppf site. -/
abbrev residueFieldBase (X : CurveFamily B hZ) (s : X.base.left.1) :
    BigFppfOver B integerBase hZ :=
  Space.residueFieldObject B integerBase hZ X.base s
    (B.residueField_spec_contains X.base.left.property s)

/-- The canonical morphism `Spec κ(s) → S` from a residue-field point to the base of a family of
curves, as a morphism of algebraic spaces. -/
abbrev residueFieldBaseMap (X : CurveFamily B hZ) (s : X.base.left.1) :
    schemeSpace (X.residueFieldBase s) ⟶ schemeSpace X.base :=
  schemeSpaceMap (Space.residueFieldMap B integerBase hZ X.base s
    (B.residueField_spec_contains X.base.left.property s))

/-- **The hypothesis of Stacks 0E1J: `κ(s) = H⁰(X_s, 𝒪_{X_s})` for all `s ∈ S`.** For every
point `s` of the base scheme, pulling back global regular functions along the projection
`X_s = X ×_S Spec κ(s) → Spec κ(s)` is bijective. -/
def HasResidueFieldGlobalFunctions (X : CurveFamily B hZ) : Prop :=
  ∀ s : X.base.left.1,
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ
      (ObjectProperty.homMk (pullback.snd X.toBase.hom (X.residueFieldBaseMap s).hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (X.residueFieldBaseMap s) ⟶
          schemeSpace (X.residueFieldBase s)))

/-- "`f_*𝒪_X = 𝒪_S`, universally" implies `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s` of the
base: it is the special case of the base change along `Spec κ(s) → S`. -/
theorem hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions
    {X : CurveFamily B hZ} (h : HasUniversallyBijectiveGlobalFunctions B hZ X) :
    X.HasResidueFieldGlobalFunctions :=
  fun s => h (schemeSpace (X.residueFieldBase s)) (X.residueFieldBaseMap s)

/-- **The conclusion of part (2) of Stacks 0E1J**: `R¹f_*𝒪_X` is a finite locally free module on
the base (Stacks 01C6, part (2)). -/
abbrev HasFiniteLocallyFreeFirstHigherDirectImage (X : CurveFamily B hZ) : Prop :=
  SheafOfModules.IsFiniteLocallyFree (X.firstDirectImage B hZ)

end CurveFamily

end AlgebraicGeometry

end
