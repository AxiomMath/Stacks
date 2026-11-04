module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDiagonalEquivalence

/-!
# A complex with quasi-coherent cohomology is a complex of quasi-coherent modules

Let `X` be a quasi-compact scheme with affine diagonal. By [Stacks, Tag 08DB] the comparison
functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` is an equivalence. In particular every object of `D(𝒪_X)`
with quasi-coherent cohomology sheaves is isomorphic to a complex of quasi-coherent
`𝒪_X`-modules. This file records that consequence, in the locally small model.

## Main results

* `Stacks.AlgebraicGeometry.QuasicoherentRepresentative.exists_iso_Q_obj_quasicoherent`: the
  representative.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.QuasicoherentRepresentative

variable (X : Scheme.{u}) [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **An object of `D_QCoh(𝒪_X)` is a complex of quasi-coherent modules**, on a quasi-compact
scheme with affine diagonal: there is a complex `F` of quasi-coherent `𝒪_X`-modules whose image
in `D(𝒪_X)` is isomorphic to `K`. -/
theorem exists_iso_Q_obj_quasicoherent (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) :
    ∃ F : CochainComplex (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ℤ,
      Nonempty (K ≅ DerivedCategory.Q.obj
        (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)) := by
  have := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal X
  let C := Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison.{u} X
  obtain ⟨K', ⟨e⟩⟩ : ∃ K', Nonempty (C.obj K' ≅ ⟨K, hK⟩) := ⟨_, ⟨C.objObjPreimageIso ⟨K, hK⟩⟩⟩
  obtain ⟨F, ⟨f⟩⟩ : ∃ F, Nonempty (DerivedCategory.Q.obj F ≅ K') :=
    ⟨_, ⟨(DerivedCategory.Q).objObjPreimageIso K'⟩⟩
  refine ⟨F, ⟨?_⟩⟩
  exact (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.mapIso (e.symm ≪≫ C.mapIso f.symm) ≪≫
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategoryFactors.app F)

end Stacks.AlgebraicGeometry.QuasicoherentRepresentative

end
