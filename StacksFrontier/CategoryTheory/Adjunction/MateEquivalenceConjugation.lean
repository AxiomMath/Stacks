module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence

/-!
# Mates of 2-cells conjugated by equivalences

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions, `G`, `H` functors forming a square
with them, and let each of the four corners be identified with another category by an
equivalence. Conjugating all functors by the equivalences, and composing the two adjunctions
with the adjunctions of the equivalences, gives adjunctions between the conjugated functors.
This file records that taking mates commutes with this conjugation:
`CategoryTheory.Equivalence.mateEquiv_twoSquareConjLeft`. It is what transports a
Beck–Chevalley statement proved for a square of categories to a square of equivalent (for
instance essentially small) models of them.

## Main definitions

* `CategoryTheory.Equivalence.twoSquareConjLeft`, `CategoryTheory.Equivalence.twoSquareConjRight`:
  the conjugates of a 2-cell between left, respectively right, adjoints.

## Main results

* `CategoryTheory.Equivalence.mateEquiv_twoSquareConjLeft`: the mate of the conjugate is the
  conjugate of the mate.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Equivalence

variable {C D C' D' Cm Dm Cm' Dm' : Type*} [Category* C] [Category* D] [Category* C']
  [Category* D'] [Category* Cm] [Category* Dm] [Category* Cm'] [Category* Dm']
  (eC : C ≌ Cm) (eD : D ≌ Dm) (eC' : C' ≌ Cm') (eD' : D' ≌ Dm')
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C' ⥤ D'} {R₂ : D' ⥤ C'} {G : C ⥤ C'} {H : D ⥤ D'}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **The conjugate of a 2-cell by equivalences on the left-adjoint side.** Given a 2-cell
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` and equivalences of the four corners with other categories, the 2-cell
between the conjugated functors `eC⁻¹ ⋙ G ⋙ eC'`, `eC⁻¹ ⋙ L₁ ⋙ eD`, `eC'⁻¹ ⋙ L₂ ⋙ eD'` and
`eD⁻¹ ⋙ H ⋙ eD'` obtained by inserting the units of the equivalences. -/
def twoSquareConjLeft (α : TwoSquare G L₁ L₂ H) :
    TwoSquare (eC.inverse ⋙ G ⋙ eC'.functor) (eC.inverse ⋙ L₁ ⋙ eD.functor)
      (eC'.inverse ⋙ L₂ ⋙ eD'.functor) (eD.inverse ⋙ H ⋙ eD'.functor) :=
  .mk _ _ _ _ <| {
    app := fun U => eD'.functor.map (L₂.map (eC'.unitIso.inv.app (G.obj (eC.inverse.obj U))) ≫
      α.app (eC.inverse.obj U) ≫ H.map (eD.unitIso.hom.app (L₁.obj (eC.inverse.obj U))))
    naturality := by
      intro U V f
      simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, Category.assoc]
      congr 1
      have h1 := eC'.unitIso.inv.naturality (G.map (eC.inverse.map f))
      have h2 := α.naturality (eC.inverse.map f)
      have h3 := eD.unitIso.hom.naturality (L₁.map (eC.inverse.map f))
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h1 h2 h3
      rw [← L₂.map_comp_assoc, h1, L₂.map_comp_assoc, reassoc_of% h2, ← H.map_comp, ← h3,
        H.map_comp] }

/-- **The conjugate of a 2-cell by equivalences on the right-adjoint side.** Given a 2-cell
`β : R₁ ⋙ G ⟶ H ⋙ R₂` and equivalences of the four corners with other categories, the 2-cell
between the conjugated functors obtained by inserting the units of the equivalences. -/
def twoSquareConjRight (β : TwoSquare R₁ H G R₂) :
    TwoSquare (eD.inverse ⋙ R₁ ⋙ eC.functor) (eD.inverse ⋙ H ⋙ eD'.functor)
      (eC.inverse ⋙ G ⋙ eC'.functor) (eD'.inverse ⋙ R₂ ⋙ eC'.functor) :=
  .mk _ _ _ _ <| {
    app := fun V => eC'.functor.map (G.map (eC.unitIso.inv.app (R₁.obj (eD.inverse.obj V))) ≫
      β.app (eD.inverse.obj V) ≫ R₂.map (eD'.unitIso.hom.app (H.obj (eD.inverse.obj V))))
    naturality := by
      intro U V f
      simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, Category.assoc]
      congr 1
      have h1 := eC.unitIso.inv.naturality (R₁.map (eD.inverse.map f))
      have h2 := β.naturality (eD.inverse.map f)
      have h3 := eD'.unitIso.hom.naturality (H.map (eD.inverse.map f))
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h1 h2 h3
      rw [← G.map_comp_assoc, h1, G.map_comp_assoc, reassoc_of% h2, ← R₂.map_comp, ← h3,
        R₂.map_comp] }

/-- **Taking mates commutes with conjugation by equivalences.** If the left adjoints are
conjugated by equivalences and the adjunctions are composed with the adjunctions of the
equivalences, the mate of the conjugated 2-cell is the conjugate of the mate. -/
theorem mateEquiv_twoSquareConjLeft (α : TwoSquare G L₁ L₂ H) :
    mateEquiv (eC.symm.toAdjunction.comp (adj₁.comp eD.toAdjunction))
        (eC'.symm.toAdjunction.comp (adj₂.comp eD'.toAdjunction))
        (twoSquareConjLeft eC eD eC' eD' α) =
      twoSquareConjRight eC eD eC' eD' (mateEquiv adj₁ adj₂ α) := by
  ext V
  simp only [symm_inverse, comp_obj, symm_functor, Adjunction.comp, toAdjunction_unit,
    whiskerRight_comp, Category.assoc, toAdjunction_counit, symm_unit, Adjunction.mk'_unit,
    whiskerLeft_comp, symm_counit, Adjunction.mk'_counit, twoSquareConjLeft, id_obj, map_comp,
    mateEquiv_apply, whiskerRight_twice, Iso.inv_hom_id_assoc, NatTrans.comp_app,
    rightUnitor_inv_app, whiskerLeft_app, counitInv_app_functor, whiskerRight_app, map_id,
    associator_inv_app, associator_hom_app, Functor.comp_map, inv_fun_map,
    Iso.hom_inv_id_app_assoc, rightUnitor_hom_app, leftUnitor_hom_app, Category.comp_id,
    Category.id_comp, twoSquareConjRight]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
  congr 1
  have hH : ∀ (Z : D) {T : D'} (k : H.obj Z ⟶ T),
      H.map (eD.unitIso.hom.app Z) ≫ H.map (eD.unitIso.inv.app Z) ≫ k = k := fun Z _ k => by
    rw [← H.map_comp_assoc, Iso.hom_inv_id_app, H.map_id, Category.id_comp]
  simp only [Equivalence.unit, Equivalence.unitInv, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc, hH]
  have h1 : R₂.map (H.map (eD.unitIso.hom.app (eD.inverse.obj V))) ≫
      R₂.map (H.map (eD.inverse.map (eD.counit.app V))) = 𝟙 _ := by
    rw [← R₂.map_comp, ← H.map_comp]; simp
  have h2 := adj₂.unit.naturality
    (eC'.unitIso.inv.app (G.obj (eC.inverse.obj (eC.functor.obj (R₁.obj (eD.inverse.obj V))))))
  have h3 := adj₂.unit.naturality (G.map (eC.unitIso.inv.app (R₁.obj (eD.inverse.obj V))))
  have h4 := congr_arg R₂.map
    (α.naturality (eC.unitIso.inv.app (R₁.obj (eD.inverse.obj V))))
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
    Functor.map_comp] at h2 h3 h4
  rw [← reassoc_of% h2, Iso.hom_inv_id_app_assoc, reassoc_of% h3, reassoc_of% h4,
    reassoc_of% h1]

/-- The conjugate of an invertible 2-cell is invertible. -/
instance isIso_twoSquareConjLeft (α : TwoSquare G L₁ L₂ H) [IsIso α] :
    IsIso (twoSquareConjLeft eC eD eC' eD' α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  dsimp [twoSquareConjLeft]
  infer_instance

end CategoryTheory.Equivalence
