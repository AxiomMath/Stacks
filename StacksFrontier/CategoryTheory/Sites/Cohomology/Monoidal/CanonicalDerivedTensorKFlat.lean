module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
public import StacksFrontier.Homology.DerivedCategory.Monoidal.DerivedTensorIsoComparison

/-!
# The canonical derived tensor product on K-flat complexes

On a pair of K-flat complexes `K`, `L` of `O`-modules, the comparison
`Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso` between the tensor product of
the monoidal derived category of [Stacks, Tag 0FPT] and the canonical derived tensor product of
[Stacks, Tag 06YU] is the comparison `QK ⊗ QL ≅ Q(K ⊗ L)` of the monoidal structure followed by
the inverse of the K-flat comparison of the canonical derived tensor product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **The comparison of the tensor product of Tag 0FPT with the derived tensor product of Tag 06YU,
on a pair of K-flat complexes**: it is `CochainComplex.KFlatMonoidal.derivedTensorIso` followed by
the inverse of the K-flat comparison of the canonical derived tensor product. -/
theorem monoidalTensorCanonicalIso_hom_app_app (K L : Complexes R)
    (hK : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L) :
    letI := derivedMonoidal R
    ((monoidalTensorCanonicalIso R).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R)
          hK hL).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison K L
          hK hL).inv := by
  have h := derivedBifunctorTensorIso_hom_app_app R
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R) K L hK hL
  have h' := CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso_hom_app_app_comp_comparisonRight
    (Mod R) (exists_kFlat_resolution R) hK hL
  refine (congrArg (_ ≫ ·) h).trans ?_
  exact (reassoc_of% h') _

/-- The inverse of `monoidalTensorCanonicalIso_hom_app_app`: on a pair of K-flat complexes the
inverse comparison is the K-flat comparison of the canonical derived tensor product followed by
the inverse of `CochainComplex.KFlatMonoidal.derivedTensorIso`. -/
theorem monoidalTensorCanonicalIso_inv_app_app (K L : Complexes R)
    (hK : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L) :
    letI := derivedMonoidal R
    ((monoidalTensorCanonicalIso R).inv.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison K L
          hK hL).hom ≫
        (CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R)
          hK hL).inv := by
  let := derivedMonoidal R
  refine Iso.inv_ext (f := ((monoidalTensorCanonicalIso R).app (DerivedCategory.Q.obj K)).app
    (DerivedCategory.Q.obj L)) ?_
  exact (congrArg (· ≫ _) (monoidalTensorCanonicalIso_hom_app_app R K L hK hL)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)).trans
      (Iso.hom_inv_id _)))

end Stacks.SheafOfModules.DerivedMonoidal
