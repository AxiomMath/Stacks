module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpenPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.NoetherianExtension.AffineOpenCompatible
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.NoetherianExtension.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived category of quasi-coherent modules on a Noetherian scheme

Let `X` be a scheme and `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` the comparison functor of
[Stacks, Tag 06VT] from the derived category of the quasi-coherent `𝒪_X`-modules to the complexes
of `𝒪_X`-modules with quasi-coherent cohomology. If `X` is Noetherian, or quasi-compact and
separated, then `i_X` is an equivalence whose quasi-inverse is the derived coherator `RQ_X`
[Stacks, Tag 09T4].

## Main results

* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isNoetherian`: the
  comparison functor of [Stacks, Tag 06VT] is an equivalence on a Noetherian scheme.
* `Stacks.DerivedQCoh.derivedCoherator_isoInv_of_isNoetherian`: its quasi-inverse is any total
  right derived functor of the coherator, and
  `Stacks.DerivedQCoh.derivedCoherator_isoInv_of_isNoetherian'` is the case of
  `Stacks.DerivedQCoh.schemeDerivedCoherator`.
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isSeparated` and
  `Stacks.DerivedQCoh.derivedCoherator_isoInv_of_isSeparated`: the same conclusions on a
  quasi-compact separated scheme.

## Implementation notes

The statements are at the standard model `CategoryTheory.HasDerivedCategory.standard` of the two
derived categories of `X`, i.e. at `w = u + 1`, installed as a local instance of raised priority.

The quasi-inverse is identified for an arbitrary total right derived functor of the coherator
together with its derivation unit, since `RQ_X` is determined only up to canonical isomorphism.
The conclusion is stated after a `letI` introducing the equivalence, and is therefore wrapped in
`Nonempty`.

## References

* [Stacks Project, Tag 09T4](https://stacks.math.columbia.edu/tag/09T4)
* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 09T3](https://stacks.math.columbia.edu/tag/09T3)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

section QuasiInverse

variable (X : Scheme.{u})
  (RQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
    DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
  (RQUnit : (modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q
        (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
    DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ RQ)
  [RQ.IsRightDerivedFunctor RQUnit
    (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))]

include RQUnit in
/-- If the comparison functor of [Stacks, Tag 06VT] is an equivalence, its quasi-inverse is any
total right derived functor of the coherator, restricted to the complexes with quasi-coherent
cohomology. -/
private theorem nonempty_derivedCoherator_isoInv
    (h : (derivedQuasicoherentComparison.{u + 1} X).IsEquivalence) :
    letI := h
    Nonempty ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RQ ≅
      (derivedQuasicoherentComparison.{u + 1} X).inv) :=
  let := h
  ⟨derivedCoherator_isoInv X RQ RQUnit⟩

end QuasiInverse

section Separated

/-- The comparison functor of [Stacks, Tag 06VT] is an equivalence on a quasi-compact separated
scheme. -/
theorem derivedQuasicoherentComparison_isEquivalence_of_isSeparated (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [IsSeparated (terminal.from X)] :
    (derivedQuasicoherentComparison.{u + 1} X).IsEquivalence :=
  derivedQuasicoherentComparison_isEquivalence_of_affineOpenCompatible X
    (affineOpenPushforwardCompatible_of_isSeparated.{u + 1} X)

/-- On a quasi-compact separated scheme the quasi-inverse of the comparison functor of
[Stacks, Tag 06VT] is any total right derived functor of the coherator, restricted to the complexes
with quasi-coherent cohomology. -/
theorem derivedCoherator_isoInv_of_isSeparated (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [IsSeparated (terminal.from X)]
    (RQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (RQUnit : (modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q
          (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))] :
    letI := derivedQuasicoherentComparison_isEquivalence_of_isSeparated X
    Nonempty ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RQ ≅
      (derivedQuasicoherentComparison.{u + 1} X).inv) :=
  nonempty_derivedCoherator_isoInv X RQ RQUnit
    (derivedQuasicoherentComparison_isEquivalence_of_isSeparated X)

end Separated

section Noetherian

/-- On a Noetherian scheme the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of
[Stacks, Tag 06VT] is an equivalence. -/
@[stacks 09T4 "equivalence"]
theorem derivedQuasicoherentComparison_isEquivalence_of_isNoetherian (X : Scheme.{u})
    [IsNoetherian X] : (derivedQuasicoherentComparison.{u + 1} X).IsEquivalence :=
  derivedQuasicoherentComparison_isEquivalence_of_affineOpenCompatible X
    (noetherianAffineOpenPushforwardCompatible X)

/-- On a Noetherian scheme the quasi-inverse of the comparison functor of [Stacks, Tag 06VT] is
`RQ_X`: any total right derived functor of the coherator `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` of
[Stacks, Tag 077P], restricted to the complexes with quasi-coherent cohomology. -/
@[stacks 09T4 "identification of the quasi-inverse"]
theorem derivedCoherator_isoInv_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    (RQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (RQUnit : (modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q
          (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))] :
    letI := derivedQuasicoherentComparison_isEquivalence_of_isNoetherian X
    Nonempty ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RQ ≅
      (derivedQuasicoherentComparison.{u + 1} X).inv) :=
  nonempty_derivedCoherator_isoInv X RQ RQUnit
    (derivedQuasicoherentComparison_isEquivalence_of_isNoetherian X)

/-- On a Noetherian scheme the quasi-inverse of the comparison functor of [Stacks, Tag 06VT] is
the restriction of the total right derived functor `Stacks.DerivedQCoh.schemeDerivedCoherator` of
the coherator to the complexes with quasi-coherent cohomology. -/
@[stacks 09T4 "identification of the quasi-inverse"]
theorem derivedCoherator_isoInv_of_isNoetherian' (X : Scheme.{u}) [IsNoetherian X] :
    letI := derivedQuasicoherentComparison_isEquivalence_of_isNoetherian X
    Nonempty ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ schemeDerivedCoherator.{u + 1} X ≅
      (derivedQuasicoherentComparison.{u + 1} X).inv) :=
  derivedCoherator_isoInv_of_isNoetherian X (schemeDerivedCoherator.{u + 1} X)
    (schemeDerivedCoheratorUnit.{u + 1} X)

end Noetherian

end Stacks.DerivedQCoh

end
