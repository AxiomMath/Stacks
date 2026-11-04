module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsHomUnit
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Derived
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.DerivedTwistSections
public import StacksFrontier.Homology.PseudoCoherent.TestFunctorApproximation

/-!
# Twisted global sections as test functors on `ℙⁿ_A`

Let `A` be a ring and `X = ℙⁿ_A`. For `0 ≤ d ≤ n` the functors `K ↦ RΓ(X, K(d))` from `D(𝒪_X)`
to `D(A)` are triangulated, every class in `Hʲ(X, K(d))` comes from a morphism
`𝒪_X(-d)[-j] ⟶ K`, and they take values in `D^{≤ 0}(A)` and pseudo-coherent objects on the
twists `𝒪_X(-k)`, `0 ≤ k ≤ n`. These are the hypotheses of the cell approximation
`StacksDraft.PseudoCoherence.exists_distTriang_isZero_homology_of_isPseudoCoherent`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.testFunctor`: `K ↦ RΓ(X, K(d))`.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.testObject`: `𝒪_X(-k)` in degree zero, as
  the inverse twist of the structure sheaf.

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.exists_hom_testObject`: classes come from
  morphisms out of shifted test objects.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.isLE_testFunctor_testObject`: for
  `-n ≤ d - k`, `RΓ(X, 𝒪_X(-k)(d))` lies in `D^{≤ 0}(A)`.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.isPseudoCoherent_testFunctor_testObject`: for
  `-n ≤ d - k`, `RΓ(X, 𝒪_X(-k)(d))` is pseudo-coherent.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherent.eq_zero_of_isZero_homology_testFunctor`: if
  `Hʲ(X, M(d)) = 0`, every morphism `𝒪_X(-d) ⟶ M[j]` is zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherent

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **The test functors** `K ↦ RΓ(ℙⁿ_A, K(d))`, `D(𝒪_X) ⥤ D(A)`. -/
abbrev testFunctor (d : ℤ) :
    DerivedCategory (Proj (polyGrading A n)).Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (derivedTwist A n d).functor ⋙ derivedGlobalSectionsOver (projToSpecCoeff A n)

/-- The structure sheaf of `ℙⁿ_A` in degree zero, as the image of a cochain complex. -/
abbrev unitObject : DerivedCategory (Proj (polyGrading A n)).Modules :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
    (CorepresentedRightDerived.single₀ (SheafOfModules.unit (Proj (polyGrading A n)).ringCatSheaf)))

/-- **The test objects** `𝒪_X(-k)[0]`, as the inverse twists of the structure sheaf. -/
abbrev testObject (k : ℤ) : DerivedCategory (Proj (polyGrading A n)).Modules :=
  (derivedTwist A n k).inverse.obj (unitObject A n)

/-- The structure sheaf in degree zero. -/
def unitObjectIso :
    unitObject A n ≅ (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (Proj (polyGrading A n)).ringCatSheaf) :=
  (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- `testObject k ≅ 𝒪_X(-k)[0]`. -/
def testObjectIso (k : ℤ) :
    testObject A n k ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-k)) :=
  (derivedTwist A n k).inverse.mapIso (unitObjectIso A n) ≪≫ derivedTwistInverseUnitIso A n k

/-- `RΓ(X, 𝒪_X(-k)(d)) ≅ RΓ(X, 𝒪_X(d - k)[0])`. -/
def testFunctorTestObjectIso (d k : ℤ) :
    (testFunctor A n d).obj (testObject A n k) ≅
      (derivedGlobalSectionsOver (projToSpecCoeff A n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-k + d))) :=
  (derivedGlobalSectionsOver (projToSpecCoeff A n)).mapIso
    ((derivedTwist A n d).functor.mapIso (testObjectIso A n k) ≪≫
      derivedTwistTwistingSheafIso A n (-k) d)

/-- If `-n ≤ d - k`, then `RΓ(X, 𝒪_X(-k)(d))` lies in `D^{≤ 0}(A)`. -/
theorem isLE_testFunctor_testObject (d k : ℤ) (h : -(n : ℤ) ≤ -k + d) :
    ((testFunctor A n d).obj (testObject A n k)).IsLE 0 :=
  have := Stacks.ProjectiveSpace.Cohomology.isLE_derivedGlobalSectionsOver_twistingSheaf A n
    (-k + d) h
  DerivedCategory.TStructure.t.isLE_of_iso (testFunctorTestObjectIso A n d k).symm 0

/-- If `-n ≤ d - k`, then `RΓ(X, 𝒪_X(-k)(d))` is pseudo-coherent. -/
theorem isPseudoCoherent_testFunctor_testObject (d k : ℤ) (h : -(n : ℤ) ≤ -k + d) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((testFunctor A n d).obj (testObject A n k)) :=
  (Stacks.ProjectiveSpace.Cohomology.isPseudoCoherent_derivedGlobalSectionsOver_twistingSheaf A n
    (-k + d) h).ofIso (testFunctorTestObjectIso A n d k).symm

/-- Every class in `H⁰(X, M)` is the image of the class of `1` under a morphism `𝒪_X[0] ⟶ M`. -/
theorem exists_hom_unitObject (M : DerivedCategory (Proj (polyGrading A n)).Modules)
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj M)) :
    ∃ (x : unitObject A n ⟶ M)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj (unitObject A n))),
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((derivedGlobalSectionsOver (projToSpecCoeff A n)).map x)).hom z = y := by
  obtain ⟨x, hx⟩ := (bijective_derivedGlobalSectionsOver_homToHomology (projToSpecCoeff A n) M).2
    (ModuleCat.homOfElement _ y)
  refine ⟨x, (CorepresentedRightDerived.unitDerived (globalSectionsOver (projToSpecCoeff A n))
    (SheafOfModules.unit (Proj (polyGrading A n)).ringCatSheaf)
    (globalSectionsOverOne (projToSpecCoeff A n)) (derivedGlobalSectionsOver (projToSpecCoeff A n))
    (derivedGlobalSectionsOverUnit (projToSpecCoeff A n))).hom 1, ?_⟩
  have := congrArg (fun g => g.hom (1 : A)) hx
  simp only [CorepresentedRightDerived.homToHomology, ModuleCat.hom_comp,
    LinearMap.comp_apply] at this
  exact this.trans ((ModuleCat.homOfElement_apply _ y 1).trans (one_smul A y))

/-- **Classes come from shifted test objects.** Every class in `Hʲ(X, M(d))` is the image of a
class under a morphism `𝒪_X(-d)[-j] ⟶ M`. -/
theorem exists_hom_testObject (d : ℤ) (M : DerivedCategory (Proj (polyGrading A n)).Modules)
    (j : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((testFunctor A n d).obj M)) :
    ∃ (x : (testObject A n d)⟦-j⟧ ⟶ M)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((testFunctor A n d).obj ((testObject A n d)⟦-j⟧))),
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        ((testFunctor A n d).map x)).hom z = y := by
  obtain ⟨k, x, z, h⟩ := StacksDraft.PseudoCoherence.exists_hom_shift_of_exists_hom
    (fun k : Unit => testObject A n d) (fun _ : Unit => testFunctor A n d)
    (fun _ X y => by
      obtain ⟨x, z, h⟩ := StacksDraft.PseudoCoherence.exists_hom_of_equivalence (derivedTwist A n d)
        (derivedGlobalSectionsOver (projToSpecCoeff A n)) (unitObject A n)
        (exists_hom_unitObject A n) X y
      exact ⟨(), x, z, h⟩) () M j y
  exact ⟨x, z, h⟩

/-- **Morphisms out of test objects are detected by the test functors.** If
`Hʲ(X, M(d)) = 0`, then every morphism `𝒪_X(-d) ⟶ M[j]` is zero: through the twist equivalence
it is a morphism `𝒪_X ⟶ M(d)[j]`, and those are the classes in `H⁰(X, M(d)[j]) = Hʲ(X, M(d))`. -/
theorem eq_zero_of_isZero_homology_testFunctor (d : ℤ)
    (M : DerivedCategory (Proj (polyGrading A n)).Modules) (j : ℤ)
    (hM : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((testFunctor A n d).obj M)))
    (x : testObject A n d ⟶ (shiftFunctor _ j).obj M) : x = 0 := by
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let adj := (derivedTwist A n d).symm.toAdjunction
  let x' := adj.homEquiv _ _ x
  have hz : IsZero (H₀.obj ((testFunctor A n d).obj ((shiftFunctor _ j).obj M))) :=
    hM.of_iso (H₀.mapIso (((testFunctor A n d).commShiftIso j).app M) ≪≫
      (H₀.shiftIso j 0 j (add_zero j)).app ((testFunctor A n d).obj M))
  have hx' : x' = 0 :=
    (bijective_derivedGlobalSectionsOver_homToHomology (projToSpecCoeff A n) _).1
      (hz.eq_of_tgt _ _)
  have hx : x = (adj.homEquiv _ _).symm x' := ((adj.homEquiv _ _).symm_apply_apply x).symm
  rw [hx, hx', Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]

end AlgebraicGeometry.ProjectiveSpacePseudoCoherent

end
