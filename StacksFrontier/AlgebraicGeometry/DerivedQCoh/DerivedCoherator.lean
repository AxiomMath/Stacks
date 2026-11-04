module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorQuasiInverse

/-!
# The total right derived functor of the coherator of an arbitrary scheme

Let `X` be a scheme. The inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` of the quasi-coherent modules has a
right adjoint `Q_X`, the coherator of [Stacks, Tag 077P]. This file constructs a total right
derived functor `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` of `Q_X` for an **arbitrary** scheme `X`, together
with its derivation unit, where
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/CoheratorQuasiInverse.lean` builds one only on
`Spec R`.

The existence is Spaltenstein's: `Mod(𝒪_X) = Mod(SheafOfModules 𝒪_X)` is Grothendieck abelian for
every scheme, so every cochain complex of `𝒪_X`-modules has a functorial K-injective resolution
and the degreewise extension of the additive `Q_X`, followed by the localization of the
quasi-coherent cochain complexes, has a right derived functor on all of `D(𝒪_X)`. Nothing affine
is used, and no boundedness is assumed.

## Main definitions

* `Stacks.DerivedQCoh.derivedCoheratorOfScheme` — the total right derived functor `RQ_X` of the
  coherator of an arbitrary scheme `X`, relative to the localization
  `CategoryTheory.DerivedCategory.Q`.
* `Stacks.DerivedQCoh.derivedCoheratorOfSchemeUnit` — its derivation unit
  `Q_X ∘ (-) ⋙ Q ⟶ Q ⋙ RQ_X` at the level of cochain complexes.

## Main results

* `Stacks.DerivedQCoh.derivedCoheratorOfScheme_isRightDerivedFunctor` — `RQ_X` together with
  its unit is a total right derived functor of the coherator, which is the universal property
  characterising it.
* `Stacks.DerivedQCoh.derivedCoheratorIsoAffine` — on `X = Spec R` the functor built here agrees
  with `Stacks.DerivedQCoh.affineDerivedCoherator`, by uniqueness of right derived functors.

## Implementation notes

The two derived categories are instance arguments, as in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/CoheratorQuasiInverse.lean`: `HasDerivedCategory`
carries the localized category as data, so no statement about `D(𝒪_X)` may pin a model. The
localization of the cochain complexes is `CategoryTheory.DerivedCategory.Q` at those free
instances, which is the shape `Stacks.DerivedQCoh.derivedCoheratorAdjunction` and
`Stacks.DerivedQCoh.derivedCoherator_isoInv` consume; feeding them
`Stacks.DerivedQCoh.derivedCoheratorOfScheme` discharges the "let `RQ_X` be a total right
derived functor" hypothesis of [Stacks, Tag 09T5] and of [Stacks, Tag 09T6] for every scheme.

The existence input is
`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`,
which asks for `CategoryTheory.IsGrothendieckAbelian` of the *source* abelian category only. For
`SheafOfModules.{u} X.ringCatSheaf` that instance is `SheafOfModules.instIsGrothendieckAbelian`,
available for the sheaves of modules over any sheaf of rings on a small site and hence for every
scheme; the target `QCoh(𝒪_X)` needs only `Abelian` and a chosen derived category. So the
construction is uniform in `X`.

Both free instances are in fact satisfiable for an arbitrary scheme at `w := u`, by the global
instances `SheafOfModules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` and
`Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/TildeFactorization.lean`; this is what lets
`Stacks.DerivedQCoh.derivedCoheratorIsoAffine` be stated with no model bookkeeping.

## References

* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Injectives.KInjectiveResolution (hasRightDerivedFunctor_mapHomologicalComplex_comp_Q)

universe w u

namespace Stacks.DerivedQCoh

section General

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]

/-- **The derived coherator of an arbitrary scheme** at the cochain-complex level: a total right
derived functor `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` of the coherator `Q_X` of [Stacks, Tag 077P],
relative to the localization `CategoryTheory.DerivedCategory.Q`. It exists because `Mod(𝒪_X)` is
Grothendieck abelian, so every cochain complex has a K-injective resolution. -/
def derivedCoheratorOfScheme :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator X)
  ((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- The derivation unit of `Stacks.DerivedQCoh.derivedCoheratorOfScheme`: the canonical
comparison from the degreewise coherator followed by localization to localization followed by
`RQ_X`. -/
def derivedCoheratorOfSchemeUnit :
    (modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q
          (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ derivedCoheratorOfScheme X :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator X)
  ((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- `Stacks.DerivedQCoh.derivedCoheratorOfScheme` is a total right derived functor of the
coherator of `X`, which is the universal property characterising it up to a unique natural
isomorphism. -/
instance derivedCoheratorOfScheme_isRightDerivedFunctor :
    (derivedCoheratorOfScheme X).IsRightDerivedFunctor (derivedCoheratorOfSchemeUnit X)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator X)
  inferInstanceAs ((((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)))
    (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)))

end General

/-! ### Agreement with the affine construction -/

/-- On an affine scheme the derived coherator built here is canonically isomorphic to
`Stacks.DerivedQCoh.affineDerivedCoherator`: both are total right derived functors of the same
coherator along the same localization, and such a functor is unique up to a unique natural
isomorphism compatible with the two derivation units. -/
def derivedCoheratorIsoAffine (R : CommRingCat.{u}) :
    derivedCoheratorOfScheme (Spec R) ≅ affineDerivedCoherator R :=
  Functor.rightDerivedUnique _ _ (derivedCoheratorOfSchemeUnit (Spec R))
    (affineDerivedCoheratorUnit R)
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Spec R).ringCatSheaf)
      (ComplexShape.up ℤ))

end Stacks.DerivedQCoh

end
