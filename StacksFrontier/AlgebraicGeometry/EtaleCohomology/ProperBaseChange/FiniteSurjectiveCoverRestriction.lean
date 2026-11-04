module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ZeroDimensionalComplementRestriction

/-!
# Restriction to a scalar extension along a finite surjective cover

Let `k ⊆ k'` be fields, `p : Y ⟶ Spec k` a scheme over `k` and `ν : Ỹ ⟶ Y` a finite surjective
morphism. For an abelian sheaf `A` on `Y_étale` the unit `A ⟶ ν_* ν^{-1} A` is a monomorphism,
so surjectivity of restriction to `Y_{k'}` in degree `q` on `A` follows from surjectivity on
`ν_* ν^{-1} A` — which, `ν` being finite, is surjectivity on `ν^{-1} A` over `Ỹ_{k'}` — together
with injectivity in degree `q` and surjectivity in degree `q - 1` on the cokernel of the unit.

This is how the dévissage of Stacks Project Tag 03SC part (7) passes from a curve to its
normalization (the step of Tag 0A3Q) without comparing `ν_* j^ν_! ℤ/ℓ` with `j_! ℤ/ℓ` on a dense
open: the discrepancy is the cokernel, handled one degree lower.

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse`:
  surjectivity is invariant under isomorphism of the sheaf.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_finite_surjective`: the
  passage along a finite surjective cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

/-- **Surjectivity of restriction only depends on the sheaf up to isomorphism.** -/
theorem surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse {X Y : Scheme.{u}}
    (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
    (h : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i F q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i G q) := by
  intro y
  obtain ⟨x, hx⟩ := h (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map e.inv))
    (add_zero q))
  refine ⟨x.comp (Ext.mk₀ e.hom) (add_zero q), ?_⟩
  rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, w} i e.hom q x, hx,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id, Ext.comp_mk₀_id]

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']
  {Y Yt : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (ν : Yt ⟶ Y) [IsFinite ν] [Surjective ν]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Yt.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' p).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' (ν ≫ p)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Passage along a finite surjective cover.** If restriction to `Ỹ_{k'}` is surjective in
degree `q` on `ν^{-1} A`, and restriction to `Y_{k'}` is injective in degree `q` and (for
`q = m + 1`) surjective in degree `m` on the cokernel of the unit `A ⟶ ν_* ν^{-1} A`, then
restriction to `Y_{k'}` is surjective in degree `q` on `A`. -/
theorem surjective_etaleCohomologyRestrictionMap_of_finite_surjective
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hup : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' (ν ≫ p)) ((etaleAbelianInverseImage.{u, 0} ν).obj A) q))
    (hinj : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' p)
      (cokernel ((etaleAbelianInverseImageDirectImageAdj.{u, 0} ν).unit.app A)) q))
    (hsurj : ∀ m, q = m + 1 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' p)
      (cokernel ((etaleAbelianInverseImageDirectImageAdj.{u, 0} ν).unit.app A)) m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' p)
      A q) := by
  have := mono_etaleAbelianUnit_of_surjective ν A
  refine surjective_etaleCohomologyRestrictionMap_of_mono.{u, 0, w} _
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} ν).unit.app A) q ?_ hinj hsurj
  exact (etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, w} ν _ _ _
    (isPullback_scalarExtension_closed k k' p ν) _ q).mpr hup

end Stacks.EtaleCohomology

end
