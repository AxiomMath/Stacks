module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionDerived
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorUnitMiddle

/-!
# The augmentation identity of Stacks 0D9K, against the derived tensor product

Let `S` be a simplicial-site situation and `K` an object of the unbounded derived category of
abelian sheaves on its total site. The comparison map of Stacks 0D9E in degree zero, followed by
the derived tensor product of `K` with the augmentation `g_{0!}ℤ ⟶ ℤ` of the integral resolution
of Stacks 09WI and the unit identification `ℤ ⊗^L_ℤ K ≅ K`, is the counit of the adjunction
`g_{0!} ⊣ g_0^{-1}` at `K`. This is the second of the two computations the proof of Stacks 0D9K
omits, stated for the term `X₀ = g_{0!}ℤ ⊗^L_ℤ K` of the Postnikov system of Stacks 0D9I.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main results

* `integerProjection_comp_derivedTensorAugmentation`: the comparison of Stacks 0D9E in degree
  zero, followed by the derived tensor product with the augmentation of the integral resolution
  and the unit identification `ℤ ⊗^L_ℤ K ≅ K`, is the counit of the derived adjunction
  `g_{0!} ⊣ g_0^{-1}` at `K`.

## References

* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor
open Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- **The comparison of Stacks 0D9E in degree zero, followed by the derived tensor product with
the augmentation of the integral resolution and the unit identification `ℤ ⊗^L_ℤ K ≅ K`, is the
counit of the derived adjunction `g_{0!} ⊣ g_0^{-1}` at `K`.** This is the second of the two
computations the proof of Stacks 0D9K omits: the structural map `X₀ ⟶ K` of the Postnikov system
of Stacks 0D9I is the derived tensor product of `K` with the augmentation `g_{0!}ℤ ⟶ ℤ` read
through `ℤ ⊗^L_ℤ K ≅ K`, and under the identification `X₀ = g_{0!}K₀` of Stacks 0D9E it is the
counit. -/
theorem integerProjection_comp_derivedTensorAugmentation
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    S.integerProjection K ⦋0⦌ ≫
        ((derivedTensor S.totalTopology).map
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
            (integerAugmentation S))).app K ≫
        (constantSheafLeftUnitIso S.totalTopology K).hom =
      (S.componentLowerShriekDerivedAdjunction ⦋0⦌).counit.app K := by
  have hsplit : derivedNatTrans (integerTensorAb S ⦋0⦌)
        (𝟭 (Sheaf S.totalTopology Ab.{u})) (integerTensorAugmentation S) =
      derivedNatTrans (integerTensorAb S ⦋0⦌) (unitIntegerTensorAb S)
          (Functor.whiskerLeft (moduleEquivalence S.totalTopology).inverse
            (Functor.whiskerRight
              ((sheafTensor (intRingSheaf S.totalTopology)).map
                ((moduleEquivalence S.totalTopology).inverse.map (integerAugmentation S)))
              (moduleEquivalence S.totalTopology).functor)) ≫
        derivedNatTrans (unitIntegerTensorAb S) (𝟭 (Sheaf S.totalTopology Ab.{u}))
          (unitTensorIso S).hom :=
    derivedNatTrans_comp _ _ _ _ _
  have hnat := NatTrans.congr_app (integerTensorAbDerivedIso_naturality_augmentation S) K
  simp only [NatTrans.comp_app] at hnat
  have hkey : (derivedNatTrans (integerTensorAb S ⦋0⦌) (𝟭 (Sheaf S.totalTopology Ab.{u}))
          (integerTensorAugmentation S)).app K ≫
        (derivedIdIso (A := Sheaf S.totalTopology Ab.{u})).hom.app K =
      (integerTensorAbDerivedIso S ⦋0⦌).hom.app K ≫
        ((derivedTensor S.totalTopology).map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerAugmentation S))).app K ≫
          (constantSheafLeftUnitIso S.totalTopology K).hom := by
    rw [hsplit, NatTrans.comp_app]
    exact (Category.assoc _ _ _).trans
      ((whisker_eq _ (derivedNatTrans_unitTensorIso_app_eq_constantSheafLeftUnitIso S K)).trans
        (((Category.assoc _ _ _).symm.trans
            (eq_whisker hnat (constantSheafLeftUnitIso S.totalTopology K).hom)).trans
          (Category.assoc _ _ _)))
  rw [← integerProjection_comp_derivedAugmentation S K, hkey, Iso.inv_hom_id_app_assoc]

end CategoryTheory.SimplicialSiteSituation

end
