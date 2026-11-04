module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence

/-!
# The comparison `D(QCoh(T_étale, 𝒪)) ⥤ D_QCoh(T_étale, 𝒪)` for an affine scheme

Let `T` be an affine scheme.  The comparison functor from the derived category of quasi-coherent
`𝒪`-modules on the small étale site of `T` to the complexes of `𝒪`-modules with quasi-coherent
cohomology is an equivalence.  This is the small étale counterpart of Stacks 06Z0, deduced from it
and from Stacks 071Q: the comparison square
`AlgebraicGeometry.SmallEtale.derivedQuasicoherentComparisonSquare` identifies it with the Zariski
comparison of `T` through the derived functors of `ε^*`, all three of which are equivalences.

## Main results

* `AlgebraicGeometry.SmallEtale.isEquivalence_derivedQcohOnSiteComparison_of_isAffine`.

## Implementation notes

This is kept apart from the algebraic-spaces file that consumes it: importing the small étale
site of algebraic spaces brings a low-priority sheafification instance under which the instance
search for the abelian structure on the modules of the small étale site of a scheme diverges.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

/-! ### The small étale site of an affine scheme -/

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)

/-- The modules on the small étale site of `T` are abelian at the universe of `T`.  This is
`SheafOfModules.instAbelian`, named so that it can be installed as a local instance of high
priority: with the 06Z0 transport file imported, a competing instance makes the search diverge on
a universe constraint. -/
abbrev abelianSheafOfModulesStructureSheaf :
    Abelian (SheafOfModules.{u} (structureSheaf B T hT)) :=
  SheafOfModules.instAbelian _

attribute [local instance high] abelianSheafOfModulesStructureSheaf

variable [_root_.AlgebraicGeometry.IsAffine T]
  [HasDerivedCategory.{w} (SheafOfModules.{u} T.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B T hT))]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (qcohOnSite B T hT).FullSubcategory]

/-- **The comparison `D(QCoh(T_étale, 𝒪)) ⥤ D_QCoh(T_étale, 𝒪)` is an equivalence for an affine
scheme `T`**, at any model of the four derived categories involved.  It is intertwined, by
`derivedQuasicoherentComparisonSquare`, with the Zariski comparison of `T` (an equivalence by
Stacks 06Z0) through the derived functors of `ε^*` on `D(QCoh)` (Stacks 03DX (2), derived) and on
`D_QCoh` (Stacks 071Q), both equivalences. -/
theorem isEquivalence_derivedQcohOnSiteComparison_of_isAffine :
    (derivedQcohOnSiteComparison.{w} B T hT).IsEquivalence := by
  have hsurj := quasicoherentIsEssImageAssociatedModule B T hT
  have := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel.{w} T
  have := derivedAssociatedModule_isEquivalence.{w} B T hT
  have := isEquivalence_associatedModuleDerivedQcoh.{w} B T hT hsurj
  have : (associatedModuleDerivedQcoh.{w} B T hT hsurj ⋙
      derivedQcohOnSiteComparison.{w} B T hT).IsEquivalence :=
    Functor.isEquivalence_of_iso (derivedQuasicoherentComparisonSquare.{w} B T hT hsurj)
  exact Functor.isEquivalence_of_comp_left (associatedModuleDerivedQcoh.{w} B T hT hsurj)
    (derivedQcohOnSiteComparison.{w} B T hT)

end AlgebraicGeometry.SmallEtale

end
