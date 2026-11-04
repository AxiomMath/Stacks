module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSurjectiveCoverRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionKernelCokernel

/-!
# Restriction for sheaves supported on a complement finite over the base field

Let `k ⊆ k'` be separably closed fields, `π : X ⟶ Spec k`, `i : Z ⟶ X` a closed immersion with
`Z` finite over `k`, and `j : W ⟶ X` an open immersion onto the complement. An abelian sheaf `K`
on `X_étale` whose inverse image to `W` vanishes is the direct image of its inverse image to `Z`,
by the sequence of Stacks Project Tag 095L, so restriction to `X_{k'}` is bijective on its
cohomology in every degree.

This applies to the kernel of the unit `F ⟶ j_* j^{-1} F` of any sheaf `F`, whose inverse image
to `W` vanishes because the inverse image of the unit is split by the counit.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_iso`
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_isZero_inverseImage`
* `Stacks.EtaleCohomology.isZero_inverseImage_kernel_unit`
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_unit_directImage`:
  surjectivity for `F` from surjectivity for `j_* j^{-1} F`, the discrepancy being handled one
  degree lower.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

/-- **Injectivity of restriction only depends on the sheaf up to isomorphism.** -/
theorem injective_etaleCohomologyRestrictionMap_of_iso {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
    (h : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w} i F q)) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w} i G q) := by
  intro x y hxy
  have key : ∀ z : Sheaf.H.{w} G q,
      (z.comp (Ext.mk₀ e.inv) (add_zero q)).comp (Ext.mk₀ e.hom) (add_zero q) = z := by
    intro z
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.comp_mk₀_id]
  have h2 : x.comp (Ext.mk₀ e.inv) (add_zero q) = y.comp (Ext.mk₀ e.inv) (add_zero q) := by
    apply h
    rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, w} i e.inv q x,
      etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, w} i e.inv q y, hxy]
  rw [← key x, ← key y, h2]

/-- **Bijectivity of restriction only depends on the sheaf up to isomorphism.** -/
theorem bijective_etaleCohomologyRestrictionMap_of_iso {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
    (h : Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} i F q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} i G q) :=
  ⟨injective_etaleCohomologyRestrictionMap_of_iso.{u, w} i e q h.1,
    surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, w} i e q h.2⟩

/-- **The kernel of a unit dies under the left adjoint.** For an adjunction `L ⊣ R` with `L`
left exact, `L` kills the kernel of the unit `F ⟶ R L F`: the image of the unit under `L` is a
split monomorphism, split by the counit. -/
theorem isZero_inverseImage_kernel_unit {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [PreservesFiniteLimits L] (F : C) :
    IsZero (L.obj (kernel (adj.unit.app F))) := by
  have : Mono (L.map (adj.unit.app F)) := by
    have : IsSplitMono (L.map (adj.unit.app F)) :=
      ⟨⟨⟨adj.counit.app (L.obj F), adj.left_triangle_components F⟩⟩⟩
    infer_instance
  exact IsZero.of_iso (isZero_kernel_of_mono _) (PreservesKernel.iso L (adj.unit.app F))

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k] [IsSepClosed k']
  {X Z W : Scheme.{u}} (π : X ⟶ Spec (.of k)) (i : Z ⟶ X) [IsClosedImmersion i]
  [IsFinite (i ≫ π)] (j : W ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' (i ≫ π)).smallEtaleTopology AddCommGrpCat.{u + 1})]

include hij in
/-- **Sheaves supported on a complement finite over `k`.** If the inverse image to `W` of `K`
vanishes, restriction to `X_{k'}` is bijective on its cohomology in every degree. -/
theorem bijective_etaleCohomologyRestrictionMap_of_isZero_inverseImage
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hK : IsZero ((etaleAbelianInverseImage.{u, 0} j).obj K)) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
      K q) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} i j hij K
  have h0 : IsZero ((extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj K)) :=
    Functor.map_isZero _ (IsZero.of_iso hK ((etaleAbelianInverseImageRestrictionIso.{u, 0} j).app
      K).symm)
  have : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app K) :=
    hS.isIso_g_iff.mpr h0
  exact bijective_etaleCohomologyRestrictionMap_of_iso.{u, w} _
    (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app K)).symm q
    (etaleCohomologyRestrictionMap_bijective_directImage_of_isFinite_comp k k' π i _ q)

include hij in
/-- **Passage from `j_* j^{-1} F` to `F`.** Restriction to `X_{k'}` is surjective in degree `q`
on `F` if it is on `j_* j^{-1} F` and, writing `C` for the cokernel of the monomorphism from the
coimage of the unit `F ⟶ j_* j^{-1} F`, it is injective in degree `q` and (for `q = m + 1`)
surjective in degree `m` on `C`. The kernel of the unit is supported on `Z`. -/
theorem surjective_etaleCohomologyRestrictionMap_of_unit_directImage
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hP : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' π) ((etaleAbelianDirectImage.{u, 0} j).obj
        ((etaleAbelianInverseImage.{u, 0} j).obj F)) q))
    (hC : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' π) (cokernel (Abelian.factorThruCoimage
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} j).unit.app F))) q))
    (hC' : ∀ m, q = m + 1 → Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
      (scalarExtensionFst k k' π) (cokernel (Abelian.factorThruCoimage
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} j).unit.app F))) m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
      F q) := by
  have hb := bijective_etaleCohomologyRestrictionMap_of_isZero_inverseImage k k' π i j hij _
    (isZero_inverseImage_kernel_unit (etaleAbelianInverseImageDirectImageAdj.{u, 0} j) F)
  exact surjective_etaleCohomologyRestrictionMap_source.{u, 0, w} _ _ q (hb q).2 (hb (q + 1)).1
    hP hC hC'

end Stacks.EtaleCohomology

end
