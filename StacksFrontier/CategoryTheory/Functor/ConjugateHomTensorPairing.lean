module

public import StacksFrontier.CategoryTheory.Functor.ConjugateHom

/-!
# Conjugation commutes with the tensor pairing

Let `P : C ⥤ D` be a functor between categories with tensor bifunctors, equipped with
comparisons `μ : P(M ⊗ N) ≅ P M ⊗ P N`.  Given `ℓ : Pm ⟶ O ⊗ Pm` and `ev : R ⊗ Pm ⟶ G` in `C`, a
morphism `α : P O ⟶ P R` gives the *tensor pairing*

`P Pm ⟶ P(O ⊗ Pm) ≅ P O ⊗ P Pm ⟶ P R ⊗ P Pm ≅ P(R ⊗ Pm) ⟶ P G`.

## Main definitions

* `CategoryTheory.Functor.tensorPairing`: the tensor pairing of `α`.

## Main results

* `CategoryTheory.Functor.tensorPairing_conjHom`: when `P₂ ≅ P₁ ⋙ L` and the comparisons of `P₂`,
  `P₁` and `L` are compatible, the tensor pairing for `P₂` of the conjugate of `α` is the
  conjugate of the tensor pairing of `α` for `P₁`.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C : Type*} {D : Type*} {D₁ : Type*} {D₂ : Type*}
  [Category* C] [Category* D] [Category* D₁] [Category* D₂]

/-- The tensor pairing: for `ℓ : Pm ⟶ O ⊗ Pm` and `ev : R ⊗ Pm ⟶ G`, a morphism
`α : P O ⟶ P R` gives `P Pm ⟶ P(O ⊗ Pm) ≅ P O ⊗ P Pm ⟶ P R ⊗ P Pm ≅ P(R ⊗ Pm) ⟶ P G`. -/
def tensorPairing (T : C ⥤ C ⥤ C) (P : C ⥤ D) (TD : D ⥤ D ⥤ D)
    (μ : ∀ M N : C, P.obj ((T.obj M).obj N) ≅ (TD.obj (P.obj M)).obj (P.obj N))
    {O Pm R G : C} (ℓ : Pm ⟶ (T.obj O).obj Pm) (ev : (T.obj R).obj Pm ⟶ G)
    (α : P.obj O ⟶ P.obj R) : P.obj Pm ⟶ P.obj G :=
  P.map ℓ ≫ (μ O Pm).hom ≫ (TD.map α).app (P.obj Pm) ≫ (μ R Pm).inv ≫ P.map ev

/-- Let `e : P₂ ≅ P₁ ⋙ L`, and let the comparisons `μ₂` of `P₂`, `μ₁` of `P₁` and `ν` of `L` be
compatible: `μ₂ ≫ (e ⊗ e) = e ≫ L μ₁ ≫ ν`. Then the tensor pairing for `P₂` of the conjugate of
`α` is the conjugate of the tensor pairing for `P₁` of `α`. -/
theorem tensorPairing_conjHom (T : C ⥤ C ⥤ C) (T₁ : D₁ ⥤ D₁ ⥤ D₁) (T₂ : D₂ ⥤ D₂ ⥤ D₂)
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L)
    (μ₁ : ∀ M N : C, P₁.obj ((T.obj M).obj N) ≅ (T₁.obj (P₁.obj M)).obj (P₁.obj N))
    (μ₂ : ∀ M N : C, P₂.obj ((T.obj M).obj N) ≅ (T₂.obj (P₂.obj M)).obj (P₂.obj N))
    (ν : ∀ A B : D₁, L.obj ((T₁.obj A).obj B) ≅ (T₂.obj (L.obj A)).obj (L.obj B))
    (hν : ∀ {A A' : D₁} (u : A ⟶ A') (B : D₁),
      L.map ((T₁.map u).app B) ≫ (ν A' B).hom = (ν A B).hom ≫ (T₂.map (L.map u)).app (L.obj B))
    (hcomp : ∀ M N : C,
      (μ₂ M N).hom ≫ (T₂.map (e.hom.app M)).app (P₂.obj N) ≫
          (T₂.obj ((P₁ ⋙ L).obj M)).map (e.hom.app N) =
        e.hom.app ((T.obj M).obj N) ≫ L.map (μ₁ M N).hom ≫ (ν (P₁.obj M) (P₁.obj N)).hom)
    {O Pm R G : C} (ℓ : Pm ⟶ (T.obj O).obj Pm) (ev : (T.obj R).obj Pm ⟶ G)
    (α : P₁.obj O ⟶ P₁.obj R) :
    tensorPairing T P₂ T₂ μ₂ ℓ ev (conjHom e α) =
      conjHom e (tensorPairing T P₁ T₁ μ₁ ℓ ev α) := by
  have h₂ (M N : C) : (μ₂ M N).hom =
      e.hom.app _ ≫ L.map (μ₁ M N).hom ≫ (ν _ _).hom ≫
        (T₂.obj ((P₁ ⋙ L).obj M)).map (e.inv.app N) ≫ (T₂.map (e.inv.app M)).app (P₂.obj N) := by
    rw [← reassoc_of% (hcomp M N)]
    simp [← Functor.map_comp, ← NatTrans.comp_app]
  have h₂' (M N : C) : (μ₂ M N).inv =
      (T₂.map (e.hom.app M)).app (P₂.obj N) ≫ (T₂.obj ((P₁ ⋙ L).obj M)).map (e.hom.app N) ≫
        (ν _ _).inv ≫ L.map (μ₁ M N).inv ≫ e.inv.app _ := by
    rw [← cancel_epi (μ₂ M N).hom, Iso.hom_inv_id, h₂]
    simp only [Category.assoc, Functor.comp_obj, ← NatTrans.comp_app_assoc,
      ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Iso.hom_inv_id_app,
      Iso.hom_inv_id, Functor.map_id, NatTrans.id_app, Category.id_comp, Iso.hom_inv_id_assoc]
  have h1 : (T₂.map (e.inv.app O)).app (P₂.obj Pm) ≫
      (T₂.map (e.hom.app O) ≫ T₂.map (L.map α) ≫ T₂.map (e.inv.app R)).app (P₂.obj Pm) ≫
        (T₂.map (e.hom.app R)).app (P₂.obj Pm) = (T₂.map (L.map α)).app (P₂.obj Pm) := by
    simp only [← NatTrans.comp_app, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
      Category.comp_id, Functor.comp_obj, Iso.inv_hom_id, NatTrans.id_app]
  have hmid : (T₂.obj (L.obj (P₁.obj O))).map (e.inv.app Pm) ≫
      (T₂.map (e.inv.app O)).app (P₂.obj Pm) ≫
      (T₂.map (e.hom.app O) ≫ T₂.map (L.map α) ≫ T₂.map (e.inv.app R)).app (P₂.obj Pm) ≫
        (T₂.map (e.hom.app R)).app (P₂.obj Pm) ≫ (T₂.obj (L.obj (P₁.obj R))).map (e.hom.app Pm) =
      (T₂.map (L.map α)).app (L.obj (P₁.obj Pm)) := by
    rw [reassoc_of% h1, NatTrans.naturality_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Category.comp_id]
    rfl
  simp only [tensorPairing, conjHom, h₂, h₂', Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [reassoc_of% hmid, ← reassoc_of% (hν α (P₁.obj Pm)), Iso.hom_inv_id_assoc,
    ← reassoc_of% (e.hom.naturality ℓ), ← e.inv.naturality ev]
  rfl

end CategoryTheory.Functor
