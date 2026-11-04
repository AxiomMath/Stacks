module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormulaAffineSmooth
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.GlobalCupProductAffine
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CanonicalOnePointComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles

/-!
# The de Rham Künneth map built from the cup product of Section 0FKU is invertible

[Stacks, Tag 0FMB] is proved in the library for the de Rham Künneth map
`Stacks.Cohomology.BoxKunneth.deRhamGlobalKunnethMap` at the global cup product
`Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical` on the base
(`Stacks.Cohomology.BoxKunneth.isIso_deRhamGlobalKunnethMap_canonical`). The cup product of
relative de Rham cohomology is built from the global cup product
`Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace`, the one of the canonical one-point
comparison. This file proves Tag 0FMB for the Künneth map at that cup product.

Both cup products are built, by the construction of [Stacks, Section 0FKU], from a left adjoint of
derived global sections `RΓ(S, -)` together with a comparison of tensor products. Over an affine
base the unit of the adjunction is invertible and its counit is invertible on complexes with
quasi-coherent cohomology; two left adjoints of the same functor are uniquely isomorphic, so these
invertibility statements pass from one adjunction to the other, and the comparison of the
canonical one-point comparison is invertible. So the cup product is invertible at the pair of
derived direct images of the two de Rham complexes, and the argument of
`Stacks.Cohomology.BoxKunneth.isIso_deRhamGlobalKunnethMap_of_isIso_relative` applies.

## Main results

* `Stacks.WeilDeRham.isIso_cupProductOnSpace_app`: the global cup product
  `cupProductOnSpace` over an affine scheme is invertible at every pair of complexes with
  quasi-coherent cohomology.
* `Stacks.WeilDeRham.isIso_deRhamGlobalKunnethMap_cupProductOnSpace`: **[Stacks, Tag 0FMB] for
  the de Rham Künneth map built from `cupProductOnSpace`.**

## References

* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.BoxKunneth
open Stacks.DeRhamDirectImage

universe u


namespace Stacks.WeilDeRham

section Affine

variable (S : Scheme.{u}) [IsAffine S]

/-- The unit of the adjunction of the canonical one-point comparison is invertible over an affine
scheme. -/
theorem isIso_canonicalOnePointComparison_unit_app
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (ModuleCat.{u} (baseRing S.toRingedSpace))) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    IsIso ((canonicalOnePointComparison S.toRingedSpace).adjunction.unit.app x) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have := AlgebraicGeometry.FlatKunneth.isIso_derivedBaseAdjunction_unit_app S x
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (derivedBaseAdjunction S.toRingedSpace)
    (canonicalOnePointComparison S.toRingedSpace).adjunction x]
  infer_instance

/-- The counit of the adjunction of the canonical one-point comparison is invertible over an
affine scheme on complexes with quasi-coherent cohomology. -/
theorem isIso_canonicalOnePointComparison_counit_app
    (U : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hU : letI := @HasDerivedCategory.standard.{u, u + 1};
        ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj U).IsQuasicoherent) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    IsIso ((canonicalOnePointComparison S.toRingedSpace).adjunction.counit.app U) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have := AlgebraicGeometry.FlatKunneth.isIso_derivedBaseAdjunction_counit_app S U hU
  have h := Adjunction.leftAdjointUniq_hom_app_counit (derivedBaseAdjunction S.toRingedSpace)
    (canonicalOnePointComparison S.toRingedSpace).adjunction U
  rw [← h] at this
  exact IsIso.of_isIso_comp_left
    ((Adjunction.leftAdjointUniq (derivedBaseAdjunction S.toRingedSpace)
      (canonicalOnePointComparison S.toRingedSpace).adjunction).hom.app
        ((baseSections S.toRingedSpace).obj U)) _

/-- **The global cup product `cupProductOnSpace` of Section 0FKU is invertible over an affine
base**, at every pair of complexes with quasi-coherent cohomology. -/
theorem isIso_cupProductOnSpace_app
    (U V : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hU : letI := @HasDerivedCategory.standard.{u, u + 1};
        ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj U).IsQuasicoherent)
    (hV : letI := @HasDerivedCategory.standard.{u, u + 1};
        ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj V).IsQuasicoherent) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    IsIso ((cupProductOnSpace S.toRingedSpace).app (U, V)) :=
  let := @HasDerivedCategory.standard.{u, u + 1}
  isIso_globalCupProduct_app (canonicalOnePointComparison S.toRingedSpace) U V
    (isIso_canonicalOnePointComparison_unit_app S _) (NatIso.isIso_app_of_isIso _ _)
    (isIso_canonicalOnePointComparison_counit_app S U hU)
    (isIso_canonicalOnePointComparison_counit_app S V hV)

end Affine

section DeRham

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **[Stacks, Tag 0FMB] for the Künneth map built from `cupProductOnSpace`.** Let `S` be affine
and let `a : X ⟶ S`, `b : Y ⟶ S` be smooth and quasi-compact with affine diagonal. Then the de
Rham Künneth map `RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`,
built from the global cup product of the canonical one-point comparison, is an isomorphism. -/
theorem isIso_deRhamGlobalKunnethMap_cupProductOnSpace [IsAffine S]
    [AlgebraicGeometry.Smooth a] [AlgebraicGeometry.Smooth b] [QuasiCompact a] [QuasiCompact b]
    [IsAffineHom (pullback.diagonal a)] [IsAffineHom (pullback.diagonal b)] :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    IsIso (deRhamGlobalKunnethMap a b (cupProductOnSpace S.toRingedSpace)) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have : QuasiSeparated a := (quasiSeparated_iff a).2 inferInstance
  have : QuasiSeparated b := (quasiSeparated_iff b).2 inferInstance
  have h := isIso_deRhamRelativeKunnethMap_of_smooth a b
  let E := DerivedCategory.Q.mapIso
    (((AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.toInverseImageModules
      (pullback.fst a b ≫ a)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (deRhamBoxTotalKunnethIso a b))
  have hrel : IsIso (relativeBoxKunnethMap a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
      (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _
      ((derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map E.hom)
      ((derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).mapIso
        E).isIso_hom h
  have hκ := isIso_cupProductOnSpace_app S _ _
    (isQuasicoherent_homology_derivedPushforward_leftComplex a)
    (isQuasicoherent_homology_derivedPushforward_leftComplex b)
  have hmap := isIso_globalBoxKunnethMap_of_isIso_relative a b
    (Scheme.Hom.deRhamDiffOpCochainComplex a) (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0 _ hκ
    hrel
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hmap
    ((sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).mapIso E).isIso_hom

end DeRham

end Stacks.WeilDeRham

end
