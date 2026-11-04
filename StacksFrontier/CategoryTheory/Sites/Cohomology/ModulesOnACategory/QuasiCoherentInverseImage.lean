module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules

/-!
# Restriction along a functor preserves cartesian derived sections

Let `F : C' ⥤ C` be a functor between categories viewed as sites with the chaotic topology and
let `O` be a presheaf of rings on `C`. The inverse image of presheaves of modules along `F`,
`dInverseImage F O : D(O) ⥤ D(F⁻¹O)`, carries an object with cartesian derived sections
(Stacks 0GYV) to an object with cartesian derived sections: the derived sections of `F⁻¹K` over
`U'` are those of `K` over `F U'`, compatibly with the restriction maps
(`Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.restrictionMap_dInverseImage`), so the
comparison map of `F⁻¹K` along an arrow `a'` is the comparison map of `K` along `F a'`, up to the
canonical isomorphism of the two derived base changes along the same ring map.

This is Stacks 0GZ1 for the morphism of topoi of a functor whose structure map is the identity.

## Main results

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.comparison_dInverseImage`: the
  comparison identity.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.isQC_dInverseImage`: the
  preservation of cartesian derived sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe r v u v' u'

namespace Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  (O : Cᵒᵖ ⥤ RingCat.{r})

/-- **The comparison map of an inverse image.** For an arrow `a'` of `C'ᵒᵖ`, the comparison map
of `F⁻¹K` along `a'` is the comparison map of `K` along `F a'`, conjugated by the identification
of derived sections of the inverse image and the canonical isomorphism of the two derived base
changes. -/
theorem comparison_dInverseImage (bc : BaseChangeData.{max u' v'} O)
    (bc' : BaseChangeData.{max u v} (F.op ⋙ O)) (K : DMod.{max u' v'} O)
    {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    (bc'.baseChange a').map ((dInverseImageCompRGamma.{r, v, u, v', u'} F O V').hom.app K) ≫
        (Adjunction.leftAdjointUniq (bc.baseChangeAdj (F.op.map a'))
          (bc'.baseChangeAdj a')).inv.app _ ≫ comparison bc (F.op.map a') K ≫
        (dInverseImageCompRGamma.{r, v, u, v', u'} F O U').inv.app K =
      comparison bc' a' ((dInverseImage.{r, v, u, v', u'} F O).obj K) := by
  let adj₁ : bc'.baseChange a' ⊣ DRestrict.{max u' v'} O (F.op.map a') := bc'.baseChangeAdj a'
  let α := Adjunction.leftAdjointUniq (bc.baseChangeAdj (F.op.map a')) adj₁
  have hα : ∀ X, adj₁.unit.app X ≫ (DRestrict.{max u' v'} O (F.op.map a')).map (α.inv.app X) =
      (bc.baseChangeAdj (F.op.map a')).unit.app X := fun X ↦ by
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact Adjunction.unit_leftAdjointUniq_hom_app adj₁ (bc.baseChangeAdj (F.op.map a')) X
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  calc (dInverseImageCompRGamma.{r, v, u, v', u'} F O V').hom.app K ≫ adj₁.homEquiv _ _
        (α.inv.app _ ≫ comparison bc (F.op.map a') K ≫
          (dInverseImageCompRGamma.{r, v, u, v', u'} F O U').inv.app K) =
      (dInverseImageCompRGamma.{r, v, u, v', u'} F O V').hom.app K ≫
        ((adj₁.unit.app _ ≫ (DRestrict.{max u' v'} O (F.op.map a')).map (α.inv.app _)) ≫
          (DRestrict.{max u' v'} O (F.op.map a')).map (comparison bc (F.op.map a') K) ≫
          (DRestrict.{max u' v'} O (F.op.map a')).map
            ((dInverseImageCompRGamma.{r, v, u, v', u'} F O U').inv.app K)) := by
        simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    _ = (dInverseImageCompRGamma.{r, v, u, v', u'} F O V').hom.app K ≫
        ((bc.baseChangeAdj (F.op.map a')).unit.app _ ≫
          (DRestrict.{max u' v'} O (F.op.map a')).map (comparison bc (F.op.map a') K) ≫
          (DRestrict.{max u' v'} O (F.op.map a')).map
            ((dInverseImageCompRGamma.{r, v, u, v', u'} F O U').inv.app K)) := by
        rw [hα]
    _ = (dInverseImageCompRGamma.{r, v, u, v', u'} F O V').hom.app K ≫
        (restrictionMap.{max u' v'} O (F.op.map a') K ≫
          (DRestrict.{max u' v'} O (F.op.map a')).map
            ((dInverseImageCompRGamma.{r, v, u, v', u'} F O U').inv.app K)) := by
        have ht : (bc.baseChangeAdj (F.op.map a')).homEquiv _ _
            (comparison bc (F.op.map a') K) = restrictionMap.{max u' v'} O (F.op.map a') K :=
          Equiv.apply_symm_apply _ _
        rw [← ht, Adjunction.homEquiv_unit, Category.assoc]
    _ = restrictionMap.{max u v} (F.op ⋙ O) a' ((dInverseImage.{r, v, u, v', u'} F O).obj K) :=
        (Category.assoc _ _ _).symm.trans
          ((Iso.comp_inv_eq ((DRestrict.{max u' v'} O (F.op.map a')).mapIso
            ((dInverseImageCompRGamma.{r, v, u, v', u'} F O U').app K))).mpr
            (restrictionMap_dInverseImage F O a' K).symm)
    _ = adj₁.homEquiv _ _ (comparison bc' a' ((dInverseImage.{r, v, u, v', u'} F O).obj K)) :=
        (Equiv.apply_symm_apply _ _).symm

/-- **Stacks 0GZ1 for a functor with identity structure map.** The inverse image along `F` of a
derived module with cartesian derived sections has cartesian derived sections. -/
theorem isQC_dInverseImage (bc : BaseChangeData.{max u' v'} O)
    (bc' : BaseChangeData.{max u v} (F.op ⋙ O)) (K : DMod.{max u' v'} O)
    (hK : IsQC.{max u' v'} bc K) :
    IsQC.{max u v} bc' ((dInverseImage.{r, v, u, v', u'} F O).obj K) := by
  intro U' V' a'
  rw [← comparison_dInverseImage F O bc bc' K a']
  have := hK (F.op.map a')
  infer_instance

end Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

end
