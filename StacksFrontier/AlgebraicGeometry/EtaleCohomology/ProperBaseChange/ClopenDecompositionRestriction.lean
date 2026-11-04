module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSurjectiveCoverRestriction

/-!
# Restriction to a scalar extension across a decomposition into two clopen pieces

Let `Y` be a scheme over a field `k`, and let `i : Z ⟶ Y` and `j : U ⟶ Y` be immersions which
are both open and closed, onto complementary subsets. For an abelian sheaf `A` on `Y_étale`,
surjectivity of restriction to `Y_{k'}` in degree `q` follows from surjectivity on `i^{-1} A`
over `Z_{k'}` and on `j^{-1} A` over `U_{k'}`, given injectivity in degree `q + 1` on
`j_! j^{-1} A`.

The proof feeds the sequence `0 → j_! j^{-1} A → A → i_* i^{-1} A → 0` of Stacks Project Tag
095L to the four lemma. The third term is a finite direct image. So is the first: `j` being a
closed immersion as well, the unit `j_! j^{-1} A ⟶ j_* j^{-1}(j_! j^{-1} A)` is an isomorphism, as
both inverse images to `Z` vanish and the inverse image to `U` of the unit is split by the
invertible counit of the fully faithful `j_*`.

This is the step of the dévissage of Stacks Project Tag 03SC part (7) that splits a smooth
proper curve into its connected components.

## Main results

* `Stacks.EtaleCohomology.isIso_unit_extensionByZero_of_isClosedImmersion`: for a clopen `j`,
  `j_! B ≅ j_* j^{-1} j_! B` through the unit.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_clopen`: the transfer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

variable {Z U Y : Scheme.{u}} (i : Z ⟶ Y) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsClosedImmersion i] [IsOpenImmersion j] [IsClosedImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

omit [IsOpenImmersion i] [IsClosedImmersion i] [IsOpenImmersion j] [IsClosedImmersion j] in
include hij in
/-- The range of `i` is the complement of the range of `j`. -/
lemma range_i_eq_compl_range_j : Set.range i.base = (Set.range j.base)ᶜ := by
  rw [hij, compl_compl]

omit [IsClosedImmersion i] in
include hij in
/-- **For a clopen immersion `j`, extension by zero is a direct image.** The unit
`j_! B ⟶ j_* j^{-1}(j_! B)` is an isomorphism. -/
theorem isIso_unit_extensionByZero_of_isClosedImmersion
    (B : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} j).unit.app
      ((extensionByZero.{u, 0} j).obj B)) := by
  let C := (extensionByZero.{u, 0} j).obj B
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} j
  -- inverse image to `U`: split by the invertible counit
  have hε : IsIso (adj.counit.app ((etaleAbelianInverseImage.{u, 0} j).obj C)) := by
    have : (etaleAbelianDirectImage.{u, 0} j).Full :=
      (etaleAbelianDirectImageFullyFaithful.{u, 0} j).full
    have : (etaleAbelianDirectImage.{u, 0} j).Faithful :=
      (etaleAbelianDirectImageFullyFaithful.{u, 0} j).faithful
    infer_instance
  have hj : IsIso ((etaleAbelianInverseImage.{u, 0} j).map (adj.unit.app C)) := by
    have : IsIso ((etaleAbelianInverseImage.{u, 0} j).map (adj.unit.app C) ≫
        adj.counit.app ((etaleAbelianInverseImage.{u, 0} j).obj C)) := by
      rw [adj.left_triangle_components C]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  -- inverse image to `Z`: both sides vanish
  have h2 : IsZero ((etaleAbelianInverseImage.{u, 0} i).obj
      ((etaleAbelianDirectImage.{u, 0} j).obj ((etaleAbelianInverseImage.{u, 0} j).obj C))) :=
    IsZero.of_iso
      (isZero_etaleRestriction_etaleAbelianDirectImage.{u, 0} j i
        (range_i_eq_compl_range_j i j hij) _)
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} i).app _)
  have hi : IsIso ((etaleAbelianInverseImage.{u, 0} i).map (adj.unit.app C)) :=
    ⟨⟨0, (isZero_etaleAbelianInverseImage_extensionByZero.{u, 0} i j hij B).eq_of_src _ _,
      h2.eq_of_src _ _⟩⟩
  exact isIso_of_isIso_etaleAbelianInverseImage.{u, 0} i j hij (adj.unit.app C)

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (π : Y ⟶ Spec (.of k))
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' (i ≫ π)).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' (j ≫ π)).smallEtaleTopology AddCommGrpCat.{u + 1})]

include hij in
/-- **Surjectivity of restriction across a clopen decomposition.** -/
theorem surjective_etaleCohomologyRestrictionMap_of_clopen
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hZ : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' (i ≫ π)) ((etaleAbelianInverseImage.{u, 0} i).obj A) q))
    (hU : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' (j ≫ π)) ((etaleAbelianInverseImage.{u, 0} j).obj A) q))
    (hinj : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' π)
      ((extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj A)) (q + 1))) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
      A q) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} i j hij A
  refine surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_injective.{u, 0, w} _ hS q
    ?_ ?_ hinj
  · -- the first term is a direct image along the closed immersion `j`
    let C := (extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj A)
    have := isIso_unit_extensionByZero_of_isClosedImmersion i j hij
      ((etaleRestriction.{u, 0} j).obj A)
    refine surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, w} _
      (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} j).unit.app C)).symm q ?_
    refine (etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, w} j _ _ _
      (isPullback_scalarExtension_closed k k' π j) _ q).mpr ?_
    -- `j^{-1} j_! j^{-1} A ≅ j^{-1} A`
    let e : (etaleAbelianInverseImage.{u, 0} j).obj C ≅
        (etaleAbelianInverseImage.{u, 0} j).obj A :=
      (etaleAbelianInverseImageRestrictionIso.{u, 0} j).app C ≪≫
        (asIso ((extensionByZeroAdj.{u, 0} j).unit.app
          ((etaleRestriction.{u, 0} j).obj A))).symm ≪≫
        ((etaleAbelianInverseImageRestrictionIso.{u, 0} j).app A).symm
    exact surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, w} _ e.symm q hU
  · exact (etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, w} i _ _ _
      (isPullback_scalarExtension_closed k k' π i) _ q).mpr hZ

end Stacks.EtaleCohomology

end
