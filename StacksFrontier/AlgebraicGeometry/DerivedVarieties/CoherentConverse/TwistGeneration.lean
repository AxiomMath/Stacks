module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.QuasicoherentRepresentative
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.TwistExt
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.CycleLift
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# The negative twists generate `D_QCoh(𝒪_{ℙⁿ_k})`

Let `k` be a field and `X = ℙⁿ_k = Proj k[T₀, …, Tₙ]`. An object `K` of `D_QCoh(𝒪_X)` receiving
only the zero morphism from every shift of every twist `𝒪(-m)`, `m ≥ 0`, is zero. This is the
derived form of [Stacks, Tag 0BQR] for the ample sheaf `𝒪(1)` of [Stacks, Tag 01Q2], which is the
vanishing criterion `hvanish` of
`Stacks.AlgebraicGeometry.ExampleGenerator.isWeakTriangulatedGenerator_twistSum_of_twists`.

## Main results

* `Stacks.AlgebraicGeometry.TwistGeneration.isZero_of_subsingleton_hom_twist`: the statement.

## Implementation notes

The proof is the source's. By [Stacks, Tag 08DB] `K` is a complex `C` of quasi-coherent modules
(`Stacks.AlgebraicGeometry.QuasicoherentRepresentative.exists_iso_Q_obj_quasicoherent`). If
`K ≠ 0` some `H^p(C)` is nonzero; it is a quotient of the quasi-coherent module of cycles `Z^p`,
so `Stacks.AmpleNonvanishing.exists_tensorPow_hom_comp_ne_zero` produces `φ : 𝒪(-N) ⟶ Z^p` with
nonzero image in `H^p(C)`. As a morphism of complexes `𝒪(-N)[-p] ⟶ C` it is nonzero on `H^p`,
hence nonzero in the derived category. The derived category is the locally small model, which is
the one [Stacks, Tag 08DB] is available at.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ZeroObject
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.TwistGeneration

open Stacks.AlgebraicGeometry.ExampleGenerator

variable (k : Type u) [Field k] (n : ℕ)

/-- An object of the derived category with vanishing cohomology sheaves is zero. -/
theorem isZero_of_forall_isZero_homology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C)
    (h : ∀ p : ℤ, IsZero ((DerivedCategory.homologyFunctor C p).obj K)) : IsZero K := by
  have : IsIso (0 : K ⟶ 0) := by
    rw [DerivedCategory.isIso_iff]
    intro p
    exact isIso_of_source_target_iso_zero _ (h p).isoZero
      ((DerivedCategory.homologyFunctor C p).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

/-- The morphism of complexes `A[-p] ⟶ C` given by a morphism `φ` into the cycles of `C` in
degree `p`. -/
noncomputable def homFromSingleOfCycles {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) {A : C} (p : ℤ) (φ : A ⟶ K.cycles p) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) p).obj A ⟶ K :=
  HomologicalComplex.mkHomFromSingle (φ ≫ K.iCycles p) (fun j _ => by simp)

/-- **A morphism of complexes out of a single object which is nonzero on homology is nonzero in
the derived category.** -/
theorem Q_map_homFromSingleOfCycles_ne_zero {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) {A : C} (p : ℤ) (φ : A ⟶ K.cycles p)
    (hφ : φ ≫ K.homologyπ p ≠ 0) :
    DerivedCategory.Q.map (homFromSingleOfCycles K p φ) ≠ 0 := by
  intro h0
  set c := homFromSingleOfCycles K p φ
  have hH : HomologicalComplex.homologyMap c p = 0 := by
    have := DerivedCategory.homologyFunctorFactors_hom_naturality c p
    rw [h0, Functor.map_zero, zero_comp] at this
    exact (cancel_epi ((DerivedCategory.homologyFunctorFactors C p).hom.app _)).1
      (this.symm.trans comp_zero.symm)
  have hcyc : HomologicalComplex.cyclesMap c p =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) p A).hom ≫ φ := by
    rw [← cancel_mono (K.iCycles p), HomologicalComplex.cyclesMap_i, Category.assoc,
      HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
    simp [c, homFromSingleOfCycles]
  apply hφ
  have hπ := HomologicalComplex.homologyπ_naturality c p
  rw [hH, comp_zero, hcyc, Category.assoc] at hπ
  exact (cancel_epi (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) p A).hom).1
    (hπ.symm.trans comp_zero.symm)

/-- `𝒪(1)` on `ℙⁿ_k` is invertible, in the spelling the ample theory uses. -/
local instance isInvertibleModule_twistingSheaf_one :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj (polyGrading k n))
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) 1) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertibleModule_twistingSheaf _
    (Stacks.PicardUFD.degreeOneCover k n) 1

/-- **The negative twists generate `D_QCoh(𝒪_{ℙⁿ_k})`.** An object `K` of the derived category of
`𝒪_{ℙⁿ_k}`-modules with quasi-coherent cohomology sheaves which receives only the zero morphism
from every `𝒪(-m)[-p]`, `m ≥ 0`, `p ∈ ℤ`, is zero. -/
theorem isZero_of_subsingleton_hom_twist
    (K : DerivedCategory
      (SheafOfModules.{u} (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf) K)
    (h : ∀ (m : ℕ) (p : ℤ), Subsingleton ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf) p).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) (-(m : ℤ))) ⟶ K)) :
    IsZero K := by
  obtain ⟨F, ⟨e⟩⟩ :=
    Stacks.AlgebraicGeometry.QuasicoherentRepresentative.exists_iso_Q_obj_quasicoherent
    (AlgebraicGeometry.Proj (polyGrading k n)) K hK
  set G := ((SheafOfModules.isQuasicoherent
    (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf).ι.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F
  refine isZero_of_forall_isZero_homology K fun p => ?_
  by_contra hp
  let eH : (DerivedCategory.homologyFunctor _ p).obj K ≅ G.homology p :=
    (DerivedCategory.homologyFunctor _ p).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ p).app G
  have : (G.homology p : (AlgebraicGeometry.Proj (polyGrading k n)).Modules).IsQuasicoherent :=
    ObjectProperty.prop_of_iso
      (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf)
      eH (hK p)
  have : ∀ q, (G.X q : (AlgebraicGeometry.Proj (polyGrading k n)).Modules).IsQuasicoherent :=
    fun q => (F.X q).property
  have : (G.cycles p : (AlgebraicGeometry.Proj (polyGrading k n)).Modules).IsQuasicoherent :=
    ObjectProperty.prop_of_iso
      (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf)
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel (G.d p (p + 1)))
        (G.cyclesIsKernel p (p + 1) (by simp)))
      (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel
        (X := AlgebraicGeometry.Proj (polyGrading k n)) (G.d p (p + 1)))
  have hH : ¬ IsZero (G.homology p : (AlgebraicGeometry.Proj (polyGrading k n)).Modules) :=
    fun h0 => hp (h0.of_iso eH)
  have : Epi (C := (AlgebraicGeometry.Proj (polyGrading k n)).Modules) (G.homologyπ p) :=
    ⟨fun g h hgh => (cancel_epi (G.homologyπ p)).1 hgh⟩
  obtain ⟨N, φ, hφ⟩ := Stacks.AmpleNonvanishing.exists_tensorPow_hom_comp_ne_zero
    (X := AlgebraicGeometry.Proj (polyGrading k n))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) 1)
    (Stacks.ProjectiveSpace.isAmple_twistingSheaf_one k n) (G.homologyπ p) hH
  obtain ⟨ι⟩ :=
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.nonempty_tensorPowModule_iso_twistingSheaf
    (polyGrading k n) (Stacks.PicardUFD.degreeOneCover k n) (-(N : ℤ))
  let A : SheafOfModules (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf :=
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) (-(N : ℤ))
  let ψ : (A : (AlgebraicGeometry.Proj (polyGrading k n)).Modules) ⟶ G.cycles p := ι.inv ≫ φ
  have hψ : ψ ≫ G.homologyπ p ≠ 0 := fun h0 => hφ <|
    ((congrArg (· ≫ G.homologyπ p) (Iso.hom_inv_id_assoc ι φ).symm).trans
      (Category.assoc _ _ _)).trans ((congrArg (ι.hom ≫ ·) h0).trans comp_zero)
  let ψ' : A ⟶ G.cycles p := ψ
  apply Q_map_homFromSingleOfCycles_ne_zero G p ψ' hψ
  rw [← cancel_epi ((DerivedCategory.singleFunctorIsoCompQ _ p).hom.app A), ← cancel_mono e.inv]
  simp only [Category.assoc, comp_zero, zero_comp]
  exact (h N p).elim _ _

end Stacks.AlgebraicGeometry.TwistGeneration

end
