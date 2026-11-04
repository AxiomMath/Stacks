module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering

/-!
# Restriction of scalars commutes with homology

An additive functor between preadditive categories which preserves homology commutes with the
homology of a homological complex: in each degree `q`, the short complex computing the homology
of the image complex is the image of the short complex computing the homology of the complex, so
`CategoryTheory.ShortComplex.mapHomologyIso` gives the comparison.

Applied to `ModuleCat.restrictScalars φ` for a ring homomorphism `φ : R →+* S`, which preserves
homology because it is exact, this says that the homology of a cochain complex of `S`-modules,
read as a complex of `R`-modules, is the homology computed over `S` read as an `R`-module.

## Main definitions

* `Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso`: an additive functor
  preserving homology commutes with the homology of a homological complex.
* `Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso`: **restriction of scalars commutes
  with the homology of a cochain complex of modules.**
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Homology.RestrictScalars

/-- **An additive functor which preserves homology commutes with the homology of a homological
complex.**  The homology in degree `q` is the homology of the short complex
`K.X (c.prev q) ⟶ K.X q ⟶ K.X (c.next q)`, and applying the functor degreewise to the complex
applies it to that short complex, so this is `CategoryTheory.ShortComplex.mapHomologyIso`. -/
def mapHomologicalComplexHomologyIso {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Preadditive C₁] [Preadditive C₂] {ι : Type*} {c : ComplexShape ι} (F : C₁ ⥤ C₂)
    [F.Additive] [F.PreservesHomology] (K : HomologicalComplex C₁ c) (q : ι)
    [K.HasHomology q] [((F.mapHomologicalComplex c).obj K).HasHomology q] :
    ((F.mapHomologicalComplex c).obj K).homology q ≅ F.obj (K.homology q) :=
  ShortComplex.mapHomologyIso (K.sc q) F

/-- Restriction of scalars commutes with homology. -/
def restrictScalarsHomologyIso {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (K : CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q ≅
      (ModuleCat.restrictScalars.{u} φ).obj (K.homology q) :=
  haveI := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars.{u} φ
  mapHomologicalComplexHomologyIso (ModuleCat.restrictScalars.{u} φ) K q

end Stacks.Homology.RestrictScalars

end
