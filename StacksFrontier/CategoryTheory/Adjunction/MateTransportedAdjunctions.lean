module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer

/-!
# Conjugates and mates across transported adjunctions

Two facts of adjunction calculus, used to compare base change maps built from different, but
isomorphic, adjunctions.

* The conjugate of the inverse of the comparison `CategoryTheory.Adjunction.leftAdjointUniq` of two
  left adjoints of isomorphic functors is the isomorphism of the right adjoints it was built from
  (the companion of `Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`).
* Mates commute with transporting the adjunctions along isomorphisms of their left and right
  adjoints: the mate of a 2-cell across transported adjunctions is the mate across the original
  adjunctions of the transported 2-cell, whiskered by the transporting isomorphisms.

## Main results

* `CategoryTheory.Adjunction.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv`.
* `CategoryTheory.Adjunction.mateEquiv_symm_ofNatIsoLeft_ofNatIsoRight`,
  `CategoryTheory.Adjunction.mateEquiv_symm_whisker` and
  `CategoryTheory.Adjunction.isIso_mateEquiv_symm_of_transport`: inverse mates across transported
  adjunctions and side functors.
* `CategoryTheory.Adjunction.isIso_mateEquiv_symm_natTrans_of_isIso`: an inverse mate is
  invertible as soon as the mate across the other pair of adjunctions of the square is.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Conjugate

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- The conjugate of the inverse of the comparison of two left adjoints of isomorphic functors is
the isomorphism of the right adjoints. -/
theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (θ : R₁ ≅ R₂) :
    conjugateEquiv adj₁ adj₂ (leftAdjointUniq (adj₁.ofNatIsoRight θ) adj₂).inv = θ.hom := by
  have h : conjugateEquiv (adj₁.ofNatIsoRight θ) adj₂
      (leftAdjointUniq (adj₁.ofNatIsoRight θ) adj₂).inv = 𝟙 _ := by
    simp [leftAdjointUniq]
  rw [Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_left] at h
  rw [← cancel_epi θ.inv, h, Iso.inv_hom_id]

end Conjugate

section Mate

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ R₂' : F ⥤ E}

/-- **Mates across transported adjunctions.**  Transport `L₁ ⊣ R₁` and `L₂ ⊣ R₂` along
isomorphisms `i₁ : L₁ ≅ L₁'`, `j₁ : R₁ ≅ R₁'`, `i₂ : L₂ ≅ L₂'`, `j₂ : R₂ ≅ R₂'`.  The inverse mate
across the transported adjunctions of a 2-cell `β : R₁' ⋙ G ⟶ H ⋙ R₂'` is the inverse mate across
the original adjunctions of the transported 2-cell, whiskered by `i₂` and `i₁`. -/
theorem mateEquiv_symm_ofNatIsoLeft_ofNatIsoRight (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (i₁ : L₁ ≅ L₁') (j₁ : R₁ ≅ R₁') (i₂ : L₂ ≅ L₂') (j₂ : R₂ ≅ R₂')
    (β : R₁' ⋙ G ⟶ H ⋙ R₂') :
    ((mateEquiv ((adj₁.ofNatIsoLeft i₁).ofNatIsoRight j₁)
      ((adj₂.ofNatIsoLeft i₂).ofNatIsoRight j₂)).symm (TwoSquare.mk _ _ _ _ β)) =
      whiskerLeft G i₂.inv ≫
        ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _
          (whiskerRight j₁.hom G ≫ β ≫ whiskerLeft H j₂.inv))) ≫
        whiskerRight i₁.hom H := by
  ext X
  have h₁ : G.map (R₁'.map (i₁.hom.app X)) ≫ β.app (L₁'.obj X) =
      β.app (L₁.obj X) ≫ R₂'.map (H.map (i₁.hom.app X)) := β.naturality (i₁.hom.app X)
  have h₂ : R₂'.map (H.map (i₁.hom.app X)) ≫ j₂.inv.app (H.obj (L₁'.obj X)) =
      j₂.inv.app (H.obj (L₁.obj X)) ≫ R₂.map (H.map (i₁.hom.app X)) :=
    j₂.inv.naturality (H.map (i₁.hom.app X))
  have h₃ : L₂.map (R₂.map (H.map (i₁.hom.app X))) ≫ adj₂.counit.app (H.obj (L₁'.obj X)) =
      adj₂.counit.app (H.obj (L₁.obj X)) ≫ H.map (i₁.hom.app X) :=
    adj₂.counit.naturality (H.map (i₁.hom.app X))
  simp [mateEquiv_symm_apply, ofNatIsoLeft, ofNatIsoRight, -Functor.map_comp,
    ← Functor.map_comp_assoc]
  have h₂' : L₂.map (R₂'.map (H.map (i₁.hom.app X))) ≫ L₂.map (j₂.inv.app (H.obj (L₁'.obj X))) ≫
      adj₂.counit.app (H.obj (L₁'.obj X)) = L₂.map (j₂.inv.app (H.obj (L₁.obj X))) ≫
        adj₂.counit.app (H.obj (L₁.obj X)) ≫ H.map (i₁.hom.app X) := by
    rw [← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc, h₃]
  simp only [Functor.map_comp, assoc, reassoc_of% h₁, h₂']

/-- **Inverse mates are natural in the side functors**: replacing `G` and `H` by isomorphic
functors changes the inverse mate by whiskering with the isomorphisms. -/
theorem mateEquiv_symm_whisker {G' : C ⥤ E} {H' : D ⥤ F} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (g : G ≅ G') (k : H ≅ H') (β : R₁ ⋙ G ⟶ H ⋙ R₂) :
    ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _
      (whiskerLeft R₁ g.inv ≫ β ≫ whiskerRight k.hom R₂))) =
      whiskerRight g.inv L₂ ≫ ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β)) ≫
        whiskerLeft L₁ k.hom := by
  ext X
  have h₁ : G'.map (adj₁.unit.app X) ≫ g.inv.app (R₁.obj (L₁.obj X)) =
      g.inv.app X ≫ G.map (adj₁.unit.app X) := g.inv.naturality (adj₁.unit.app X)
  have h₂ : L₂.map (R₂.map (k.hom.app (L₁.obj X))) ≫ adj₂.counit.app (H'.obj (L₁.obj X)) =
      adj₂.counit.app (H.obj (L₁.obj X)) ≫ k.hom.app (L₁.obj X) :=
    adj₂.counit.naturality (k.hom.app (L₁.obj X))
  dsimp [mateEquiv]
  simp only [Functor.map_comp, assoc, Functor.map_id, id_comp, comp_id]
  rw [← Functor.map_comp_assoc L₂ (G'.map (adj₁.unit.app X)), h₁, Functor.map_comp_assoc, h₂]

/-- **Invertibility transfers across transported adjunctions.**  If the inverse mate of `β'`
across `(adj₁.ofNatIsoLeft i₁).ofNatIsoRight j₁` and `(adj₂.ofNatIsoLeft i₂).ofNatIsoRight j₂`
is invertible, and `β` corresponds to `β'` under `j₁`, `j₂` and isomorphisms `g : G ≅ G'`,
`k : H ≅ H'` of the side functors, then the inverse mate of `β` across `adj₁` and `adj₂` is
invertible. -/
theorem isIso_mateEquiv_symm_of_transport {G' : C ⥤ E} {H' : D ⥤ F} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (i₁ : L₁ ≅ L₁') (j₁ : R₁ ≅ R₁') (i₂ : L₂ ≅ L₂') (j₂ : R₂ ≅ R₂')
    (g : G ≅ G') (k : H ≅ H') (β : R₁ ⋙ G ⟶ H ⋙ R₂) (β' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (hβ : β = whiskerLeft R₁ g.hom ≫ whiskerRight j₁.hom G' ≫ β' ≫ whiskerLeft H' j₂.inv ≫
      whiskerRight k.inv R₂)
    [IsIso ((mateEquiv ((adj₁.ofNatIsoLeft i₁).ofNatIsoRight j₁)
      ((adj₂.ofNatIsoLeft i₂).ofNatIsoRight j₂)).symm (TwoSquare.mk _ _ _ _ β'))] :
    IsIso ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β)) := by
  have e₁ := mateEquiv_symm_ofNatIsoLeft_ofNatIsoRight adj₁ adj₂ i₁ j₁ i₂ j₂ β'
  have e₂ := mateEquiv_symm_whisker adj₁ adj₂ g.symm k.symm
    (whiskerRight j₁.hom G' ≫ β' ≫ whiskerLeft H' j₂.inv)
  have hβ' : whiskerLeft R₁ g.symm.inv ≫ (whiskerRight j₁.hom G' ≫ β' ≫ whiskerLeft H' j₂.inv) ≫
      whiskerRight k.symm.hom R₂ = β := by
    rw [hβ, Iso.symm_inv, Iso.symm_hom]
    simp only [assoc]
  rw [hβ'] at e₂
  have : IsIso ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _
      (whiskerRight j₁.hom G' ≫ β' ≫ whiskerLeft H' j₂.inv))) := by
    have hM : ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _
        (whiskerRight j₁.hom G' ≫ β' ≫ whiskerLeft H' j₂.inv))) =
        whiskerLeft G' i₂.hom ≫ ((mateEquiv ((adj₁.ofNatIsoLeft i₁).ofNatIsoRight j₁)
          ((adj₂.ofNatIsoLeft i₂).ofNatIsoRight j₂)).symm (TwoSquare.mk _ _ _ _ β')) ≫
          whiskerRight i₁.inv H' := by
      rw [e₁]
      ext X
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, assoc,
        Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
      exact (comp_id _).symm
    rw [hM]
    infer_instance
  rw [e₂]
  infer_instance

end Mate

section Iterated

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {Eu : C ⥤ D} {Ru : D ⥤ C} {Eu' : E ⥤ F} {Ru' : F ⥤ E} {Pt' : C ⥤ E} {Ft' : E ⥤ C}
  {Pt : D ⥤ F} {Ft : F ⥤ D}

/-- **An inverse mate is invertible as soon as the mate across the other pair of adjunctions
is.**  For a square of four left adjoints `Eu`, `Eu'`, `Pt`, `Pt'` and a 2-cell
`σ : Ru ⋙ Pt' ⟶ Pt ⋙ Ru'`, the inverse mate `Pt' ⋙ Eu' ⟶ Eu ⋙ Pt` of `σ` across `Eu ⊣ Ru`,
`Eu' ⊣ Ru'` has as conjugate the mate `Ft ⋙ Ru ⟶ Ru' ⋙ Ft'` of `σ` across `Pt ⊣ Ft`,
`Pt' ⊣ Ft'`, so it is invertible if that is. -/
theorem isIso_mateEquiv_symm_natTrans_of_isIso (adjU : Eu ⊣ Ru) (adjU' : Eu' ⊣ Ru')
    (adjT : Pt ⊣ Ft) (adjT' : Pt' ⊣ Ft') (σ : TwoSquare Ru Pt Pt' Ru')
    [IsIso (mateEquiv adjT adjT' σ)] :
    IsIso ((mateEquiv adjU adjU').symm σ) := by
  have h := iterated_mateEquiv_conjugateEquiv adjU adjU' adjT' adjT ((mateEquiv adjU adjU').symm σ)
  rw [Equiv.apply_symm_apply] at h
  have : IsIso (conjugateEquiv (adjU.comp adjT) (adjT'.comp adjU')
      ((mateEquiv adjU adjU').symm σ)) := by
    rw [← h]
    infer_instance
  exact conjugateEquiv_of_iso (adjU.comp adjT) (adjT'.comp adjU') _

end Iterated

end CategoryTheory.Adjunction
