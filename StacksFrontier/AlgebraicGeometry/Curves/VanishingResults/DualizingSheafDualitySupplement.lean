module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheaf
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexLowerVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent

/-!
# Further results on `DualizingSheafDuality`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality` that need
imports beyond those of that module.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CategoryTheory.Triangulated

universe u

namespace Stacks.Duality

/-! ### A module placed in degree zero -/

/-- **The cohomology sheaves of a quasi-coherent module placed in degree zero are
quasi-coherent**: in degree zero it is the module itself and in every other degree it
vanishes. -/
theorem isQuasicoherent_homology_singleFunctor_obj {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsQuasicoherent := by
  rcases lt_trichotomy i 0 with h | h | h
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 i h)
  · subst h
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app F).symm hF
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 i h)

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

end Stacks.Duality

end
