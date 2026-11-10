module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSectionsSliceTesting
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SliceTestingFamily
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence
public import StacksFrontier.Homology.DerivedComplete.PseudoCoherentComplete

/-!
# Derived completeness read off the cohomology sheaves, on a slice testing family

`StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteCohomology` proves that on a small site
with
enough weakly contractible objects a complex of sheaves of modules, in the universe `max u v` of
the site, is derived complete along a sheaf of ideals exactly when all of its cohomology sheaves
are. This file proves the same on a site that is not assumed small, for sheaves of modules in an
arbitrary universe `max u v w` containing the site, with the weakly contractible objects a
`Stacks.WeaklyContractible.SliceTestingFamily` at that universe: derived completeness is tested
on derived sections over the members of the family
(`AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_sliceTestingFamily`),
where `DerivedCompleteRecurrence.isDerivedCompleteAt_mapDerivedCategory_iff` reads it off the
cohomology objects. On a small site a covering collection of weakly contractible objects is such
a family by `Stacks.WeaklyContractible.SliceTestingFamily.ofIsWeaklyContractible`; the small
pro-étale site of a scheme, which is not essentially small, carries one in every universe.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff_homology_of_sliceTestingFamily`: a complex
  of sheaves of modules is derived complete along a sheaf of ideals exactly when all of its
  cohomology sheaves are.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- A complex is derived complete precisely when each cohomology sheaf is. -/
@[stacks 099Q "cohomology_criterion"]
theorem isDerivedComplete_iff_homology_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (K : DerivedCategory
      (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I K ↔
      ∀ p : ℤ, AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            p).obj K)) := by
  rw [isDerivedComplete_iff_derivedSections_of_sliceTestingFamily X h I K]
  simp_rw [isDerivedComplete_iff_derivedSections_of_sliceTestingFamily X h I]
  constructor
  · intro hK p U hU
    obtain ⟨hAdd, hLim, hColim, hProd, hComplete⟩ := hK U hU
    exact ⟨hAdd, hLim, hColim, hProd, fun f hf =>
      (DerivedCompleteRecurrence.isDerivedCompleteAt_mapDerivedCategory_iff _ K f).mp
        (hComplete f hf) p⟩
  · intro hKp U hU
    obtain ⟨hAdd, hLim, hColim, hProd, _⟩ := hKp 0 U hU
    exact ⟨hAdd, hLim, hColim, hProd, fun f hf =>
      (DerivedCompleteRecurrence.isDerivedCompleteAt_mapDerivedCategory_iff _ K f).mpr
        fun p => (hKp p U hU).2.2.2.2 f hf⟩

end AlgebraicGeometry.RingedSite

end
