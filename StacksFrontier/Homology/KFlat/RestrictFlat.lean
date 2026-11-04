module

public import StacksFrontier.Homology.KFlat.AcyclicModule
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Restriction of scalars along a flat ring map preserves K-flatness

Let `φ : R → S` be a flat homomorphism of commutative rings and `P` a K-flat complex of
`S`-modules.  For an acyclic complex `N` of `R`-modules the projection formula identifies the
underlying complex of `R`-modules of `P ⊗_S (S ⊗_R N)` with `P ⊗_R N`; the base change `S ⊗_R N`
is acyclic because `S` is flat, so `P ⊗_R N` is acyclic.  Hence `P`, read over `R`, is K-flat.

## Main results

* `CochainComplex.KFlat.kFlat_of_kFlatLeft`: K-flatness in the left variable of the tensor
  product implies K-flatness.
* `CochainComplex.KFlat.kFlat_restrictScalarsLarge_of_flat`: the restriction statement.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CochainComplex.KFlat

universe u

section SameRing

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct ModuleCat.liftedModuleMonoidal
  ModuleCat.liftedModuleMonoidalPreadditive ModuleCat.liftedModuleSymmetric

variable {R : Type u} [CommRing R]

/-- **K-flatness in the left variable of the tensor product implies K-flatness.** -/
theorem kFlat_of_kFlatLeft {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : CochainComplex.KFlatBifunctor.KFlatLeft (curriedTensor (ModuleCat.{u} R)) K) :
    CochainComplex.KFlat.{u, u} K :=
  CochainComplex.KFlatBifunctor.kFlat_of_natIso _ _
    (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)).symm
    ((CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ K).1 hK)

end SameRing

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Restriction of scalars along a flat ring map preserves K-flatness.** -/
theorem kFlat_restrictScalarsLarge_of_flat (φ : R →+* S) (hφ : φ.Flat)
    {P : CochainComplex (ModuleCat.{u} S) ℤ} (hP : CochainComplex.KFlat.{u, u} P) :
    CochainComplex.KFlat.{u, u} ((CochainComplex.restrictScalarsLarge.{u} φ).obj P) := by
  let : MonoidalCategoryStruct (ModuleCat.{u} R) := ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.liftedModuleMonoidal.{u, u}
  let : MonoidalPreadditive (ModuleCat.{u} R) := ModuleCat.liftedModuleMonoidalPreadditive.{u, u}
  let : MonoidalCategoryStruct (ModuleCat.{u} S) := ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} S) := ModuleCat.liftedModuleMonoidal.{u, u}
  let : MonoidalPreadditive (ModuleCat.{u} S) := ModuleCat.liftedModuleMonoidalPreadditive.{u, u}
  refine kFlat_of_kFlatLeft fun N hN => ?_
  have hE : ((CochainComplex.extendScalarsLarge.{u, u, u} φ).obj N).Acyclic :=
    acyclic_extendScalarsComplex_of_flat.{u, u} φ hφ N hN
  have hT := kFlatLeft_of_kFlat.{u, u} hP _ hE
  refine HomologicalComplex.Acyclic.of_iso
    (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{u, u, u} φ N P)
    ((CochainComplex.restrictScalarsLarge_acyclic_iff.{u} φ _).2 hT)

end CochainComplex.KFlat
