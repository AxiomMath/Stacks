module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualityComparisonMap
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap

/-!
# The duality formula of [Stacks, Tag 0AU2] and the change of compactification

Let `f : X ⟶ Y` be a morphism of `FTS_S` and `j₁`, `j₂` two compactifications of `X` over `Y`.
The isomorphism `f^!_{j₁} ≅ f^!_{j₂}` on `D⁺_QCoh` of [Stacks, Tag 0AA0], computed through the
dominating compactification, carries the isomorphism `f^!M ≅ R𝓗om(Lf^* D_Y(M), f^!K)` of
[Stacks, Tag 0AU2] for `j₁` to the one for `j₂`, followed by the isomorphism at `K`.

## Main results

* `Stacks.Duality.UpperShriekDuality.upperShriekDualityIso_upperShriekPlusIso`.

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.UpperShriekDuality

open Stacks.Duality.TwistedInverseImageDuality

/-- An isomorphism of a full subcategory, read through a functor on the ambient category. -/
theorem map_inv_hom_comp_map_hom_hom {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    {P : ObjectProperty 𝒞} (G : 𝒞 ⥤ 𝒟) {a b : P.FullSubcategory} (e : a ≅ b) :
    G.map e.inv.hom ≫ G.map e.hom.hom = 𝟙 _ := by
  rw [← G.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id,
    ObjectProperty.FullSubcategory.id_hom, G.map_id]

/-- An isomorphism of a full subcategory, read through a functor on the ambient category. -/
theorem map_hom_hom_comp_map_inv_hom {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    {P : ObjectProperty 𝒞} (G : 𝒞 ⥤ 𝒟) {a b : P.FullSubcategory} (e : a ≅ b) :
    G.map e.hom.hom ≫ G.map e.inv.hom = 𝟙 _ := by
  rw [← G.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, e.hom_inv_id,
    ObjectProperty.FullSubcategory.id_hom, G.map_id]

/-- The chase behind `upperShriekDualityIso_upperShriekPlusIso`. -/
theorem upperShriekDualityIso_upperShriekPlusIso_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (G : 𝒟 ⥤ 𝒞) {a1 a2 z : 𝒞} {e0 e1 e2 : 𝒟} (i₁ : a1 ⟶ z) (sm₁ : z ⟶ a1)
    (sm₂ : z ⟶ a2) (uZ : z ⟶ G.obj e0) (u₁ : a1 ⟶ G.obj e1) (u₂ : a2 ⟶ G.obj e2)
    (d₁ : e0 ⟶ e1) (d₂ : e0 ⟶ e2) (k₁ : e1 ⟶ e0)
    (hi : i₁ ≫ sm₁ = 𝟙 _) (hd : d₁ ≫ k₁ = 𝟙 _) (B₁ : sm₁ ≫ u₁ = uZ ≫ G.map d₁)
    (B₂ : sm₂ ≫ u₂ = uZ ≫ G.map d₂) : (i₁ ≫ sm₂) ≫ u₂ = u₁ ≫ G.map (k₁ ≫ d₂) := by
  have h : i₁ ≫ uZ = u₁ ≫ G.map k₁ := by
    rw [← Category.comp_id uZ, ← G.map_id, ← hd, G.map_comp, reassoc_of% B₁.symm,
      reassoc_of% hi]
  rw [Category.assoc, B₂, reassoc_of% h, G.map_comp]

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j₁ j₂ : CompactificationOf (Over.mk f.left)) {K : Std Y.left} (hK : IsDualizing K)

/-- **The isomorphism of [Stacks, Tag 0AU2] is compatible with the isomorphism of
[Stacks, Tag 0AA0] between two compactifications.** -/
theorem upperShriekDualityIso_upperShriekPlusIso (M : (plusCoh Y.left).FullSubcategory)
    (hM : DerivedCategoryB.IsBoundedBelow (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩).obj)
    (hKb : DerivedCategoryB.IsBoundedBelow (dualizingQCoh hK).obj) :
    (comparison X.left).inverse.map
        ((DominatingCompactification.upperShriekPlusIso f j₁ j₂).hom.app
          ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩).hom.hom ≫
      (upperShriekDualityIso f j₂ hK).hom.app M =
    (upperShriekDualityIso f j₁ hK).hom.app M ≫
      ((sheafHom X.left).obj (op ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj
        K)))).map ((comparison X.left).inverse.map
          ((DominatingCompactification.upperShriekPlusIso f j₁ j₂).hom.app
            ⟨dualizingQCoh hK, hKb⟩).hom.hom) := by
  have : IsProper (X := (DominatingCompactification.compactification f j₁ j₂).space)
      (DominatingCompactification.fst f j₁ j₂) :=
    (inferInstance : IsProper (DominatingCompactification.fst f j₁ j₂))
  have : IsProper (X := (DominatingCompactification.compactification f j₁ j₂).space)
      (DominatingCompactification.snd f j₁ j₂) :=
    (inferInstance : IsProper (DominatingCompactification.snd f j₁ j₂))
  have B₁ := upperShriekDualityIso_compactificationMap_app f
    (DominatingCompactification.compactification f j₁ j₂) j₁
    (DominatingCompactification.fst f j₁ j₂) rfl (DominatingCompactification.isPullback_fst f j₁ j₂)
    hK M
  have B₂ := upperShriekDualityIso_compactificationMap_app f
    (DominatingCompactification.compactification f j₁ j₂) j₂
    (DominatingCompactification.snd f j₁ j₂)
    (DominatingCompactification.fst_comp_toBase f j₁ j₂).symm
    (DominatingCompactification.isPullback_snd f j₁ j₂) hK M
  have hi := map_inv_hom_comp_map_hom_hom (ObjectProperty.ι _ ⋙ (comparison X.left).inverse)
    ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₁
      (DominatingCompactification.fst f j₁ j₂) rfl
      (DominatingCompactification.isPullback_fst f j₁ j₂)).app
        ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩)
  have hd := map_hom_hom_comp_map_inv_hom (ObjectProperty.ι _ ⋙ (comparison X.left).inverse)
    ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₁
      (DominatingCompactification.fst f j₁ j₂) rfl
      (DominatingCompactification.isPullback_fst f j₁ j₂)).app ⟨dualizingQCoh hK, hKb⟩)
  have hi' : (comparison X.left).inverse.map
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₁
        (DominatingCompactification.fst f j₁ j₂) rfl
        (DominatingCompactification.isPullback_fst f j₁ j₂)).inv.app
          ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩).hom.hom ≫
      (upperShriekStdMap f (DominatingCompactification.compactification f j₁ j₂) j₁
        (DominatingCompactification.fst f j₁ j₂) rfl
        (DominatingCompactification.isPullback_fst f j₁ j₂)).app M = 𝟙 _ := hi
  have hd' : upperShriekDualizingMap f (DominatingCompactification.compactification f j₁ j₂) j₁
        (DominatingCompactification.fst f j₁ j₂) rfl
        (DominatingCompactification.isPullback_fst f j₁ j₂) hK ≫
      (comparison X.left).inverse.map
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₁
        (DominatingCompactification.fst f j₁ j₂) rfl
        (DominatingCompactification.isPullback_fst f j₁ j₂)).inv.app
          ⟨dualizingQCoh hK, hKb⟩).hom.hom = 𝟙 _ := hd
  have h := upperShriekDualityIso_upperShriekPlusIso_chase
    ((sheafHom X.left).obj (op ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))))
    _ _ _ _ _ _ _ _ _ hi' hd' B₁ B₂
  have e₂ : (comparison X.left).inverse.map
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₂
        (DominatingCompactification.snd f j₁ j₂)
        (DominatingCompactification.fst_comp_toBase f j₁ j₂).symm
        (DominatingCompactification.isPullback_snd f j₁ j₂)).hom.app
          ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩).hom.hom =
      (upperShriekStdMap f (DominatingCompactification.compactification f j₁ j₂) j₂
        (DominatingCompactification.snd f j₁ j₂)
        (DominatingCompactification.fst_comp_toBase f j₁ j₂).symm
        (DominatingCompactification.isPullback_snd f j₁ j₂)).app M := by
    simp only [upperShriekCompactificationIso, upperShriekPlusIsoOfNatTrans,
      Functor.whiskerLeft_app]
    rfl
  have e₃ : (comparison X.left).inverse.map
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₂
        (DominatingCompactification.snd f j₁ j₂)
        (DominatingCompactification.fst_comp_toBase f j₁ j₂).symm
        (DominatingCompactification.isPullback_snd f j₁ j₂)).hom.app
          ⟨dualizingQCoh hK, hKb⟩).hom.hom =
      upperShriekDualizingMap f (DominatingCompactification.compactification f j₁ j₂) j₂
        (DominatingCompactification.snd f j₁ j₂)
        (DominatingCompactification.fst_comp_toBase f j₁ j₂).symm
        (DominatingCompactification.isPullback_snd f j₁ j₂) hK := by
    simp only [upperShriekCompactificationIso, upperShriekPlusIsoOfNatTrans]
    rfl
  have p₁ : ((DominatingCompactification.upperShriekPlusIso f j₁ j₂).hom.app
        ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩).hom.hom =
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₁
        (DominatingCompactification.fst f j₁ j₂) rfl
        (DominatingCompactification.isPullback_fst f j₁ j₂)).inv.app
          ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩).hom.hom ≫
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₂
        (DominatingCompactification.snd f j₁ j₂)
        (DominatingCompactification.fst_comp_toBase f j₁ j₂).symm
        (DominatingCompactification.isPullback_snd f j₁ j₂)).hom.app
          ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩).hom.hom := rfl
  have p₂ : ((DominatingCompactification.upperShriekPlusIso f j₁ j₂).hom.app
        ⟨dualizingQCoh hK, hKb⟩).hom.hom =
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₁
        (DominatingCompactification.fst f j₁ j₂) rfl
        (DominatingCompactification.isPullback_fst f j₁ j₂)).inv.app
          ⟨dualizingQCoh hK, hKb⟩).hom.hom ≫
      ((upperShriekCompactificationIso f (DominatingCompactification.compactification f j₁ j₂) j₂
        (DominatingCompactification.snd f j₁ j₂)
        (DominatingCompactification.fst_comp_toBase f j₁ j₂).symm
        (DominatingCompactification.isPullback_snd f j₁ j₂)).hom.app
          ⟨dualizingQCoh hK, hKb⟩).hom.hom := rfl
  have L := (congrArg (comparison X.left).inverse.map p₁).trans
    (((comparison X.left).inverse.map_comp _ _).trans (congrArg (_ ≫ ·) e₂))
  have R := (congrArg (comparison X.left).inverse.map p₂).trans
    (((comparison X.left).inverse.map_comp _ _).trans (congrArg (_ ≫ ·) e₃))
  rw [L]
  exact h.trans (congrArg (fun φ => (upperShriekDualityIso f j₁ hK).hom.app M ≫
    ((sheafHom X.left).obj (op ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj
      K)))).map φ) R.symm)

end Stacks.Duality.UpperShriekDuality
