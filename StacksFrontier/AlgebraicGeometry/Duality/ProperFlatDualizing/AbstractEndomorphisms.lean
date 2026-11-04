module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.AbstractTensorDual

/-!
# `Hom(E ⊗ ω, ω) ≃ Hom(E, 𝟙)` naturally in a dualizable `E`, abstractly

In the setting of `CategoryTheory.MonoidalCategory.RelativeDuality` (an adjunction `L ⊣ R`, a
right adjoint `a` of the restriction of `R`, and `ω = a(𝟙)`), let `E` be an object of `C` with a
right dual `E^∨` such that `R(E^∨)` has a right dual. The chain of bijections of the third
paragraph of the proof of [Stacks, Tag 0E4L],

  `Hom(E ⊗ ω, ω) = Hom(R(E ⊗ ω), 𝟙) = Hom(R(E^∨)^∨, 𝟙) = Hom(𝟙, R(E^∨)) = Hom(L𝟙, E^∨)`
  `             = Hom(𝟙, E^∨) = Hom(E, 𝟙)`,

is natural in `E`: for `g : E ⟶ E'` it carries `g ▷ ω ≫ y` to `g ≫ (the image of y)`. Naturality
is checked step by step through the right adjoint mates `gᘁ : E'ᘁ ⟶ Eᘁ`.

## Main results

* `CategoryTheory.MonoidalCategory.RelativeDuality.endHomEquiv` — the chain of bijections.
* `CategoryTheory.MonoidalCategory.RelativeDuality.endHomEquiv_naturality` — its naturality.
-/

@[expose] public noncomputable section

namespace CategoryTheory.MonoidalCategory

universe v₁ v₂ u₁ u₂

/-- `fullyFaithfulι.homEquiv.symm` turns precomposition with `f` into precomposition with
`homMk f`. -/
private theorem fullyFaithfulι_homEquiv_symm_comp {C : Type u₁} [Category.{v₁} C]
    {QC : ObjectProperty C} {X X' Y : QC.FullSubcategory}
    (f : X.obj ⟶ X'.obj) (y : X'.obj ⟶ Y.obj) :
    QC.fullyFaithfulι.homEquiv.symm (f ≫ y) =
      ObjectProperty.homMk f ≫ QC.fullyFaithfulι.homEquiv.symm y := rfl

section Mates

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- `tensorLeftHomEquiv` intertwines precomposition with `gᘁ ▷ X` and postcomposition with
`g ▷ Z`. -/
theorem tensorLeftHomEquiv_comp_whiskerRight {E E' : C} [HasRightDual E] [HasRightDual E']
    (g : E ⟶ E') (X Z : C) (t : Eᘁ ⊗ X ⟶ Z) :
    tensorLeftHomEquiv X E Eᘁ Z t ≫ g ▷ Z = tensorLeftHomEquiv X E' E'ᘁ Z (gᘁ ▷ X ≫ t) := by
  dsimp [tensorLeftHomEquiv]
  simp only [Category.assoc]
  calc (λ_ X).inv ≫ η_ E Eᘁ ▷ X ≫ (α_ E Eᘁ X).hom ≫ E ◁ t ≫ g ▷ Z
      = (λ_ X).inv ≫ η_ E Eᘁ ▷ X ≫ (α_ E Eᘁ X).hom ≫ g ▷ (Eᘁ ⊗ X) ≫ E' ◁ t := by
        rw [whisker_exchange]
    _ = (λ_ X).inv ≫ (η_ E Eᘁ ≫ g ▷ Eᘁ) ▷ X ≫ (α_ E' Eᘁ X).hom ≫ E' ◁ t := by
        rw [comp_whiskerRight, Category.assoc, associator_naturality_left_assoc]
    _ = (λ_ X).inv ≫ (η_ E' E'ᘁ ≫ E' ◁ gᘁ) ▷ X ≫ (α_ E' Eᘁ X).hom ≫ E' ◁ t := by
        rw [coevaluation_comp_rightAdjointMate]
    _ = (λ_ X).inv ≫ η_ E' E'ᘁ ▷ X ≫ (α_ E' E'ᘁ X).hom ≫ E' ◁ (gᘁ ▷ X ≫ t) := by
        rw [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
          MonoidalCategory.whiskerLeft_comp]

/-- Precomposing with `gᘁ ▷ X` under `tensorLeftHomEquiv` is postcomposing with `g ▷ Z`. -/
theorem tensorLeftHomEquiv_symm_comp_whiskerRight {E E' : C} [HasRightDual E] [HasRightDual E']
    (g : E ⟶ E') (X Z : C) (y : X ⟶ E ⊗ Z) :
    (tensorLeftHomEquiv X E' E'ᘁ Z).symm (y ≫ g ▷ Z) =
      gᘁ ▷ X ≫ (tensorLeftHomEquiv X E Eᘁ Z).symm y := by
  rw [Equiv.symm_apply_eq, ← tensorLeftHomEquiv_comp_whiskerRight, Equiv.apply_symm_apply]

/-- `tensorRightHomEquiv` intertwines precomposition with `M ◁ h` and postcomposition with
`Z ◁ hᘁ`. -/
theorem tensorRightHomEquiv_whiskerLeft_comp {P P' : C} [HasRightDual P] [HasRightDual P']
    (h : P' ⟶ P) (M Z : C) (s : M ⊗ P ⟶ Z) :
    tensorRightHomEquiv M P' P'ᘁ Z (M ◁ h ≫ s) =
      tensorRightHomEquiv M P Pᘁ Z s ≫ Z ◁ hᘁ := by
  dsimp [tensorRightHomEquiv]
  simp only [Category.assoc]
  calc (ρ_ M).inv ≫ M ◁ η_ P' P'ᘁ ≫ (α_ M P' P'ᘁ).inv ≫ (M ◁ h ≫ s) ▷ P'ᘁ
      = (ρ_ M).inv ≫ M ◁ (η_ P' P'ᘁ ≫ h ▷ P'ᘁ) ≫ (α_ M P P'ᘁ).inv ≫ s ▷ P'ᘁ := by
        rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
          ← associator_inv_naturality_middle_assoc]
    _ = (ρ_ M).inv ≫ M ◁ (η_ P Pᘁ ≫ P ◁ hᘁ) ≫ (α_ M P P'ᘁ).inv ≫ s ▷ P'ᘁ := by
        rw [coevaluation_comp_rightAdjointMate]
    _ = (ρ_ M).inv ≫ M ◁ η_ P Pᘁ ≫ (α_ M P Pᘁ).inv ≫ s ▷ Pᘁ ≫ Z ◁ hᘁ := by
        rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
          associator_inv_naturality_right_assoc, whisker_exchange]

/-- `Hom(P^∨, 𝟙) ≃ Hom(𝟙, P)` for an object `P` with a right dual. -/
def unitDualHomEquiv (P : C) [HasRightDual P] : (Pᘁ ⟶ 𝟙_ C) ≃ (𝟙_ C ⟶ P) :=
  (Iso.homCongr (ρ_ Pᘁ).symm (Iso.refl _)).trans <|
  (tensorLeftHomEquiv (𝟙_ C) P Pᘁ (𝟙_ C)).trans (Iso.homCongr (Iso.refl _) (ρ_ P))

/-- `unitDualHomEquiv` is natural: for `h : P' ⟶ P`, precomposition with `hᘁ` corresponds to
postcomposition with `h`. -/
theorem unitDualHomEquiv_naturality {P P' : C} [HasRightDual P] [HasRightDual P'] (h : P' ⟶ P)
    (z : P'ᘁ ⟶ 𝟙_ C) : unitDualHomEquiv P (hᘁ ≫ z) = unitDualHomEquiv P' z ≫ h := by
  simp only [unitDualHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom,
    Iso.refl_inv, Category.comp_id, Category.id_comp]
  rw [← rightUnitor_naturality_assoc, ← tensorLeftHomEquiv_comp_whiskerRight, Category.assoc,
    rightUnitor_naturality, Category.assoc]

/-- `Hom(𝟙, E^∨) ≃ Hom(E, 𝟙)` for an object `E` with a right dual. -/
def dualUnitHomEquiv (E : C) [HasRightDual E] : (𝟙_ C ⟶ Eᘁ) ≃ (E ⟶ 𝟙_ C) :=
  (Iso.homCongr (Iso.refl _) (λ_ Eᘁ).symm).trans <|
  (tensorRightHomEquiv (𝟙_ C) E Eᘁ (𝟙_ C)).symm.trans (Iso.homCongr (λ_ E) (Iso.refl _))

/-- `dualUnitHomEquiv` is natural: for `g : E ⟶ E'`, postcomposition with `gᘁ` corresponds to
precomposition with `g`. -/
theorem dualUnitHomEquiv_naturality {E E' : C} [HasRightDual E] [HasRightDual E'] (g : E ⟶ E')
    (w : 𝟙_ C ⟶ E'ᘁ) : dualUnitHomEquiv E (w ≫ gᘁ) = g ≫ dualUnitHomEquiv E' w := by
  simp only [dualUnitHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Category.id_comp, Iso.symm_hom]
  have h := tensorRightHomEquiv_whiskerLeft_comp g (𝟙_ C) (𝟙_ C)
    ((tensorRightHomEquiv (𝟙_ C) E' E'ᘁ (𝟙_ C)).symm (w ≫ (λ_ E'ᘁ).inv))
  rw [Equiv.apply_symm_apply] at h
  rw [Category.assoc, leftUnitor_inv_naturality (rightAdjointMate g), ← Category.assoc w, ← h,
    Equiv.symm_apply_apply, ← leftUnitor_inv_naturality_assoc]

end Mates

namespace RelativeDuality

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [MonoidalCategory C]
  [MonoidalCategory D] [BraidedCategory D]
  {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
  {QC : ObjectProperty C} {QD : ObjectProperty D}
  (hR : ∀ K : QC.FullSubcategory, QD (R.obj K.obj))
  {a : QD.FullSubcategory ⥤ QC.FullSubcategory}
  (adjA : QD.lift (QC.ι ⋙ R) hR ⊣ a)
  (O : QD.FullSubcategory) (eO : O.obj ≅ 𝟙_ D)

section Naturality

variable {E E' : C} [HasRightDual E] [HasRightDual E'] [HasRightDual (R.obj Eᘁ)]
  [HasRightDual (R.obj E'ᘁ)] (g : E ⟶ E')
  (hK : ∀ M : D, QD M → QC (Eᘁ ⊗ L.obj M))
  (hK' : ∀ M : D, QD M → QC (E'ᘁ ⊗ L.obj M))
  (π : ∀ (M : D) (_ : QD M), R.obj Eᘁ ⊗ M ≅ R.obj (Eᘁ ⊗ L.obj M))
  (π' : ∀ (M : D) (_ : QD M), R.obj E'ᘁ ⊗ M ≅ R.obj (E'ᘁ ⊗ L.obj M))
  (hπg : ∀ (M : D) (hM : QD M),
    R.map (rightAdjointMate g) ▷ M ≫ (π M hM).hom =
      (π' M hM).hom ≫ R.map (rightAdjointMate g ▷ L.obj M))

include hπg in
/-- **The chain of bijections is natural in the dualizable object.** -/
theorem homEquiv_naturality_dual (M : D) (hM : QD M) (x : M ⟶ R.obj (E ⊗ (a.obj O).obj)) :
    homEquiv adj hR adjA O eO E' E'ᘁ (R.obj E'ᘁ)ᘁ hK' π' M hM (x ≫ R.map (g ▷ (a.obj O).obj)) =
      homEquiv adj hR adjA O eO E Eᘁ (R.obj Eᘁ)ᘁ hK π M hM x ≫
        rightAdjointMate (R.map (rightAdjointMate g)) := by
  simp only [homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right_symm,
    tensorLeftHomEquiv_symm_comp_whiskerRight]
  rw [fullyFaithfulι_homEquiv_symm_comp (X' := ⟨Eᘁ ⊗ L.obj M, hK M hM⟩),
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.FullyFaithful.homEquiv_apply, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift_map, Functor.comp_map,
    ObjectProperty.homMk_hom, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_inv, Category.id_comp,
    Category.assoc]
  rw [← reassoc_of% (hπg M hM), ← BraidedCategory.braiding_inv_naturality_right_assoc,
    tensorRightHomEquiv_whiskerLeft_comp]
  simp only [Iso.refl_hom, Category.assoc, leftUnitor_naturality]

variable (hπ : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
    R.obj Eᘁ ◁ g ≫ (π M hM).hom = (π M' hM').hom ≫ R.map (Eᘁ ◁ L.map g))
  (hπ' : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
    R.obj E'ᘁ ◁ g ≫ (π' M hM).hom = (π' M' hM').hom ≫ R.map (E'ᘁ ◁ L.map g))
  (hA : QD (R.obj (E ⊗ (a.obj O).obj))) (hA' : QD (R.obj (E' ⊗ (a.obj O).obj)))
  (hB : QD (R.obj Eᘁ)ᘁ) (hB' : QD (R.obj E'ᘁ)ᘁ)

include hπg in
/-- **The isomorphism `R(E ⊗ ω) ≅ R(E^∨)^∨` is natural in the dualizable object.** -/
theorem tensorDualIso_naturality :
    R.map (g ▷ (a.obj O).obj) ≫
        (tensorDualIso adj hR adjA O eO E' E'ᘁ (R.obj E'ᘁ)ᘁ hK' π' hπ' hA' hB').hom =
      (tensorDualIso adj hR adjA O eO E Eᘁ (R.obj Eᘁ)ᘁ hK π hπ hA hB).hom ≫
        rightAdjointMate (R.map (rightAdjointMate g)) := by
  simp only [tensorDualIso, isoOfHomEquiv_hom]
  rw [← homEquiv_naturality adj hR adjA O eO E' E'ᘁ (R.obj E'ᘁ)ᘁ hK' π' hπ' _ _ hA' hA,
    Category.comp_id, ← Category.id_comp (R.map (g ▷ (a.obj O).obj)),
    homEquiv_naturality_dual adj hR adjA O eO g hK hK' π π' hπg]

end Naturality

section EndHomEquiv

variable (εL : L.obj (𝟙_ D) ≅ 𝟙_ C)
  (E : C) [HasRightDual E] [HasRightDual (R.obj Eᘁ)]
  (hK : ∀ M : D, QD M → QC (Eᘁ ⊗ L.obj M))
  (π : ∀ (M : D) (_ : QD M), R.obj Eᘁ ⊗ M ≅ R.obj (Eᘁ ⊗ L.obj M))
  (hπ : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
    R.obj Eᘁ ◁ g ≫ (π M hM).hom = (π M' hM').hom ≫ R.map (Eᘁ ◁ L.map g))
  (hA : QD (R.obj (E ⊗ (a.obj O).obj))) (hB : QD (R.obj Eᘁ)ᘁ)
  (hEω : QC (E ⊗ (a.obj O).obj))

/-- **`Hom(E ⊗ ω, ω) ≃ Hom(E, 𝟙)`**, the chain of bijections of the third paragraph of the proof
of [Stacks, Tag 0E4L]. -/
def endHomEquiv : (E ⊗ (a.obj O).obj ⟶ (a.obj O).obj) ≃ (E ⟶ 𝟙_ C) :=
  (QC.fullyFaithfulι.homEquiv (X := ⟨E ⊗ (a.obj O).obj, hEω⟩) (Y := a.obj O)).symm.trans <|
  (adjA.homEquiv ⟨E ⊗ (a.obj O).obj, hEω⟩ O).symm.trans <|
  QD.fullyFaithfulι.homEquiv.trans <|
  (Iso.homCongr (Iso.refl _) eO).trans <|
  (Iso.homCongr (tensorDualIso adj hR adjA O eO E Eᘁ (R.obj Eᘁ)ᘁ hK π hπ hA hB)
    (Iso.refl _)).trans <|
  (unitDualHomEquiv (R.obj Eᘁ)).trans <|
  (adj.homEquiv (𝟙_ D) Eᘁ).symm.trans <|
  (Iso.homCongr εL (Iso.refl _)).trans (dualUnitHomEquiv E)

end EndHomEquiv

section EndHomEquivNaturality

variable (εL : L.obj (𝟙_ D) ≅ 𝟙_ C)
  {E E' : C} [HasRightDual E] [HasRightDual E'] [HasRightDual (R.obj Eᘁ)]
  [HasRightDual (R.obj E'ᘁ)] (g : E ⟶ E')
  (hK : ∀ M : D, QD M → QC (Eᘁ ⊗ L.obj M))
  (hK' : ∀ M : D, QD M → QC (E'ᘁ ⊗ L.obj M))
  (π : ∀ (M : D) (_ : QD M), R.obj Eᘁ ⊗ M ≅ R.obj (Eᘁ ⊗ L.obj M))
  (π' : ∀ (M : D) (_ : QD M), R.obj E'ᘁ ⊗ M ≅ R.obj (E'ᘁ ⊗ L.obj M))
  (hπg : ∀ (M : D) (hM : QD M),
    R.map (rightAdjointMate g) ▷ M ≫ (π M hM).hom =
      (π' M hM).hom ≫ R.map (rightAdjointMate g ▷ L.obj M))
  (hπ : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
    R.obj Eᘁ ◁ g ≫ (π M hM).hom = (π M' hM').hom ≫ R.map (Eᘁ ◁ L.map g))
  (hπ' : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
    R.obj E'ᘁ ◁ g ≫ (π' M hM).hom = (π' M' hM').hom ≫ R.map (E'ᘁ ◁ L.map g))
  (hA : QD (R.obj (E ⊗ (a.obj O).obj))) (hA' : QD (R.obj (E' ⊗ (a.obj O).obj)))
  (hB : QD (R.obj Eᘁ)ᘁ) (hB' : QD (R.obj E'ᘁ)ᘁ)
  (hEω : QC (E ⊗ (a.obj O).obj)) (hEω' : QC (E' ⊗ (a.obj O).obj))

include hπg in
/-- **`Hom(E ⊗ ω, ω) ≃ Hom(E, 𝟙)` is natural in the dualizable object.** -/
theorem endHomEquiv_naturality (y : E' ⊗ (a.obj O).obj ⟶ (a.obj O).obj) :
    endHomEquiv adj hR adjA O eO εL E hK π hπ hA hB hEω (g ▷ (a.obj O).obj ≫ y) =
      g ≫ endHomEquiv adj hR adjA O eO εL E' hK' π' hπ' hA' hB' hEω' y := by
  have hκ := tensorDualIso_naturality adj hR adjA O eO g hK hK' π π' hπg hπ hπ' hA hA' hB hB'
  have hκ' : (tensorDualIso adj hR adjA O eO E Eᘁ (R.obj Eᘁ)ᘁ hK π hπ hA hB).inv ≫
      R.map (g ▷ (a.obj O).obj) = rightAdjointMate (R.map (rightAdjointMate g)) ≫
        (tensorDualIso adj hR adjA O eO E' E'ᘁ (R.obj E'ᘁ)ᘁ hK' π' hπ' hA' hB').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hκ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [endHomEquiv, Equiv.trans_apply]
  rw [fullyFaithfulι_homEquiv_symm_comp (X' := ⟨E' ⊗ (a.obj O).obj, hEω'⟩),
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.FullyFaithful.homEquiv_apply, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift_map, Functor.comp_map,
    ObjectProperty.homMk_hom, Iso.homCongr_apply, Iso.refl_inv, Iso.refl_hom, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [reassoc_of% hκ', unitDualHomEquiv_naturality, Adjunction.homEquiv_naturality_right_symm,
    ← Category.assoc, dualUnitHomEquiv_naturality]

end EndHomEquivNaturality

section OfEq

variable (εL : L.obj (𝟙_ D) ≅ 𝟙_ C)
  {TC : C ⥤ C ⥤ C} (hTC : curriedTensor C = TC) {TD : D ⥤ D ⥤ D} (hTD : curriedTensor D = TD)

/-- `endHomEquiv` with the projection formula read through bifunctors `TC`, `TD` equal to the
tensor products. -/
def endHomEquivOfEq (E : C) [HasRightDual E] [HasRightDual (R.obj Eᘁ)]
    (hK : ∀ M : D, QD M → QC ((TC.obj Eᘁ).obj (L.obj M)))
    (π : ∀ (M : D) (_ : QD M), (TD.obj (R.obj Eᘁ)).obj M ≅ R.obj ((TC.obj Eᘁ).obj (L.obj M)))
    (hπ : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
      (TD.obj (R.obj Eᘁ)).map g ≫ (π M hM).hom =
        (π M' hM').hom ≫ R.map ((TC.obj Eᘁ).map (L.map g)))
    (hA : QD (R.obj (E ⊗ (a.obj O).obj))) (hB : QD (R.obj Eᘁ)ᘁ)
    (hEω : QC (E ⊗ (a.obj O).obj)) :
    (E ⊗ (a.obj O).obj ⟶ (a.obj O).obj) ≃ (E ⟶ 𝟙_ C) := by
  subst hTC hTD
  exact endHomEquiv adj hR adjA O eO εL E hK π hπ hA hB hEω

/-- `endHomEquivOfEq` is natural in the dualizable object: for `g : E ⟶ E'`, precomposition
with `g ▷ ω` corresponds to precomposition with `g`. -/
theorem endHomEquivOfEq_naturality {E E' : C} [HasRightDual E] [HasRightDual E']
    [HasRightDual (R.obj Eᘁ)] [HasRightDual (R.obj E'ᘁ)] (g : E ⟶ E')
    (hK : ∀ M : D, QD M → QC ((TC.obj Eᘁ).obj (L.obj M)))
    (hK' : ∀ M : D, QD M → QC ((TC.obj E'ᘁ).obj (L.obj M)))
    (π : ∀ (M : D) (_ : QD M), (TD.obj (R.obj Eᘁ)).obj M ≅ R.obj ((TC.obj Eᘁ).obj (L.obj M)))
    (π' : ∀ (M : D) (_ : QD M),
      (TD.obj (R.obj E'ᘁ)).obj M ≅ R.obj ((TC.obj E'ᘁ).obj (L.obj M)))
    (hπg : ∀ (M : D) (hM : QD M),
      (TD.map (R.map (rightAdjointMate g))).app M ≫ (π M hM).hom =
        (π' M hM).hom ≫ R.map ((TC.map (rightAdjointMate g)).app (L.obj M)))
    (hπ : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
      (TD.obj (R.obj Eᘁ)).map g ≫ (π M hM).hom =
        (π M' hM').hom ≫ R.map ((TC.obj Eᘁ).map (L.map g)))
    (hπ' : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
      (TD.obj (R.obj E'ᘁ)).map g ≫ (π' M hM).hom =
        (π' M' hM').hom ≫ R.map ((TC.obj E'ᘁ).map (L.map g)))
    (hA : QD (R.obj (E ⊗ (a.obj O).obj))) (hA' : QD (R.obj (E' ⊗ (a.obj O).obj)))
    (hB : QD (R.obj Eᘁ)ᘁ) (hB' : QD (R.obj E'ᘁ)ᘁ)
    (hEω : QC (E ⊗ (a.obj O).obj)) (hEω' : QC (E' ⊗ (a.obj O).obj))
    (y : E' ⊗ (a.obj O).obj ⟶ (a.obj O).obj) :
    endHomEquivOfEq adj hR adjA O eO εL hTC hTD E hK π hπ hA hB hEω (g ▷ (a.obj O).obj ≫ y) =
      g ≫ endHomEquivOfEq adj hR adjA O eO εL hTC hTD E' hK' π' hπ' hA' hB' hEω' y := by
  subst hTC hTD
  exact endHomEquiv_naturality adj hR adjA O eO εL g hK hK' π π' hπg hπ hπ' hA hA' hB hB' hEω
    hEω' y

end OfEq

end RelativeDuality

end CategoryTheory.MonoidalCategory

end
