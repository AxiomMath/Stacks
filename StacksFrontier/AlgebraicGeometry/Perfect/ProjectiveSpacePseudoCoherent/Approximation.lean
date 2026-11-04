module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherent.TestFunctors
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangulatedSubcategory
public import StacksFrontier.Homology.PseudoCoherent.TriangulatedSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Modules.FiniteLocallyFreePresentation

/-!
# Approximating an object of `D_QCoh(ℙⁿ_A)` by twists, through its twisted cohomology

Let `A` be a ring, `X = ℙⁿ_A` and `K ∈ D(𝒪_X)` such that `RΓ(X, K(d))` is pseudo-coherent for
`d = 0, …, n`. Then for every `m` there is a distinguished triangle `Y ⟶ K ⟶ Z ⟶ Y[1]` where
`Y` is built from the twists `𝒪_X(-k)`, `0 ≤ k ≤ n`, so that `Y` is quasi-coherent,
pseudo-coherent and has pseudo-coherent twisted cohomology, and `Hʲ(X, Z(d)) = 0` for all
`d = 0, …, n` and `j ≥ m`. This is the cell construction of the proof of [Stacks, Tag 0CSG],
(5) ⟹ (1).

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.exists_distTriang_isZero_homology_testFunctor`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open scoped ZeroObject

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherent

/-- A quasi-coherent module placed in degree zero lies in `D_QCoh(𝒪_X)`. -/
theorem derivedCategoryB_isQuasicoherent_singleFunctor (X : Scheme.{u}) (M : X.Modules)
    (hM : M.IsQuasicoherent) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) := fun i => by
  have hB := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X
  by_cases hi : i = 0
  · subst hi
    exact hB.isClosedUnderIsomorphisms.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm hM
  · refine DerivedCategoryB.zero_mem_of_isWeakSerre _ hB _ ?_
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 i h
        (hX := DerivedCategory.instIsGEObjSingleFunctor M 0)
    · exact DerivedCategory.isZero_of_isLE _ 0 i h
        (hX := DerivedCategory.instIsLEObjSingleFunctor M 0)

variable (A : Type u) [CommRing A] (n : ℕ)

/-- `D_QCoh(𝒪_X)` as a property of the objects of `D(𝒪_X)`. -/
abbrev quasicoherentObject : ObjectProperty (DerivedCategory (Proj (polyGrading A n)).Modules) :=
  DerivedCategoryB.derivedCategoryB (A := (Proj (polyGrading A n)).Modules)
    (SheafOfModules.isQuasicoherent (Proj (polyGrading A n)).ringCatSheaf)

/-- `D_QCoh(𝒪_X)` is closed under isomorphisms. -/
instance : (quasicoherentObject A n).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre _)

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`. -/
instance : (quasicoherentObject A n).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre _)

/-- Objects whose twisted cohomology `RΓ(X, Y(d))`, `0 ≤ d ≤ n`, is pseudo-coherent. -/
def testPseudoCoherent : ObjectProperty (DerivedCategory (Proj (polyGrading A n)).Modules) :=
  fun Y => ∀ d : Fin (n + 1),
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((testFunctor A n d).obj Y)

/-- Having pseudo-coherent twisted cohomology is invariant under isomorphism. -/
instance : (testPseudoCoherent A n).IsClosedUnderIsomorphisms where
  of_iso e h d := (h d).ofIso ((testFunctor A n d).mapIso e)

/-- The objects with pseudo-coherent twisted cohomology form a triangulated subcategory. -/
instance : (testPseudoCoherent A n).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun d =>
    (StacksDraft.PseudoCoherence.pseudoCoherent_of_isZero _
      ((testFunctor A n d).map_isZero (isZero_zero _))).1⟩
  isStableUnderShiftBy a := ⟨fun Y hY d =>
    ((StacksDraft.PseudoCoherence.isPseudoCoherentObject A).le_shift a _ (hY d)).ofIso
      (((testFunctor A n d).commShiftIso a).app Y).symm⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ d =>
    (StacksDraft.PseudoCoherence.isPseudoCoherentObject A).ext_of_isTriangulatedClosed₂ _
      ((testFunctor A n d).map_distinguished T hT) (h₁ d) (h₃ d)

/-- **The cells**: quasi-coherent, pseudo-coherent, with pseudo-coherent twisted cohomology. -/
abbrev cellProperty : ObjectProperty (DerivedCategory (Proj (polyGrading A n)).Modules) :=
  quasicoherentObject A n ⊓ ((Proj (polyGrading A n)).isPseudoCoherentObject ⊓
    testPseudoCoherent A n)

/-- Pseudo-coherent objects with pseudo-coherent twisted cohomology are closed under
isomorphisms. -/
instance : ((Proj (polyGrading A n)).isPseudoCoherentObject ⊓
    testPseudoCoherent A n).IsClosedUnderIsomorphisms := inferInstance

/-- Pseudo-coherent objects with pseudo-coherent twisted cohomology form a triangulated
subcategory. -/
instance : ((Proj (polyGrading A n)).isPseudoCoherentObject ⊓
    testPseudoCoherent A n).IsTriangulated := inferInstance

/-- The cells are closed under isomorphisms. -/
instance : (cellProperty A n).IsClosedUnderIsomorphisms := inferInstance

/-- The cells form a triangulated subcategory of `D(𝒪_X)`. -/
instance : (cellProperty A n).IsTriangulated := inferInstance

/-- The test object `𝒪_X(-k)[0]` lies in `D_QCoh(𝒪_X)`. -/
theorem quasicoherentObject_testObject (k : ℤ) : quasicoherentObject A n (testObject A n k) :=
  (quasicoherentObject A n).prop_of_iso (testObjectIso A n k).symm
    (derivedCategoryB_isQuasicoherent_singleFunctor _ _
      (Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf A n (-k)))

/-- The test object `𝒪_X(-k)[0]` is pseudo-coherent. -/
theorem isPseudoCoherentObject_testObject (k : ℤ) :
    (Proj (polyGrading A n)).isPseudoCoherentObject (testObject A n k) := by
  refine (Proj (polyGrading A n)).isPseudoCoherentObject.prop_of_iso (testObjectIso A n k).symm ?_
  have := Stacks.AlgebraicGeometry.ProjTwistRank.isFiniteLocallyFreeOfRank_twistingSheaf A n (-k)
  exact (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
    (X := (Proj (polyGrading A n)).toRingedSpace) _).1
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
      (X := (Proj (polyGrading A n)).toRingedSpace) _
    (isPerfect_singleFunctor_of_isFiniteLocallyFree (Proj (polyGrading A n))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-k))
      (SheafOfModules.IsFiniteLocallyFree.toFiniteLocallyFree.{u, u, u} _
        (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-k)) 1))))

/-- For `0 ≤ k ≤ n`, the test object `𝒪_X(-k)[0]` has pseudo-coherent twisted cohomology. -/
theorem testPseudoCoherent_testObject (k : Fin (n + 1)) :
    testPseudoCoherent A n (testObject A n k) := fun d =>
  isPseudoCoherent_testFunctor_testObject A n d k (by omega)

/-- The test object `𝒪_X(-k)[0]`, `0 ≤ k ≤ n`, is a cell. -/
theorem cellProperty_testObject (k : Fin (n + 1)) : cellProperty A n (testObject A n k) :=
  ⟨quasicoherentObject_testObject A n k, isPseudoCoherentObject_testObject A n k,
    testPseudoCoherent_testObject A n k⟩

/-- **Cell approximation on `ℙⁿ_A`.** If `RΓ(X, K(d))` is pseudo-coherent for `0 ≤ d ≤ n`, then
for every `m` there is a distinguished triangle `Y ⟶ K ⟶ Z ⟶ Y[1]` with `Y` a cell and
`Hʲ(X, Z(d)) = 0` for `0 ≤ d ≤ n` and `j ≥ m`. -/
theorem exists_distTriang_isZero_homology_testFunctor
    (K : DerivedCategory (Proj (polyGrading A n)).Modules) (hK : testPseudoCoherent A n K)
    (m : ℤ) :
    ∃ (Y Z : DerivedCategory (Proj (polyGrading A n)).Modules) (α : Y ⟶ K) (β : K ⟶ Z)
      (γ : Z ⟶ Y⟦(1 : ℤ)⟧), Triangle.mk α β γ ∈ distTriang _ ∧ cellProperty A n Y ∧
      ∀ (d : Fin (n + 1)) (j : ℤ), m ≤ j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
          ((testFunctor A n d).obj Z)) :=
  StacksDraft.PseudoCoherence.exists_distTriang_isZero_homology_of_isPseudoCoherent
    (fun k : Fin (n + 1) => testObject A n k) (fun d : Fin (n + 1) => testFunctor A n d)
    (cellProperty A n)
    (fun d k => isLE_testFunctor_testObject A n d k (by omega))
    (cellProperty_testObject A n)
    (fun Y hY d => hY.2.2 d)
    (fun d X j y => by
      obtain ⟨x, z, h⟩ := exists_hom_testObject A n d X j y
      exact ⟨d, x, z, h⟩)
    K hK m

end AlgebraicGeometry.ProjectiveSpacePseudoCoherent

end
