module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualNaturality

/-!
# Mates under a monoidal functor and a change of dual

Let `F : C ⥤ D` be a monoidal functor, `pA`, `pB` exact pairings exhibiting `A'`, `B'` as duals of
`A`, `B` in `C`, and `qA`, `qB` exact pairings exhibiting `A''`, `B''` as duals of `F A`, `F B` in
`D`. The image under `F` of the mate `B' ⟶ A'` of `f : A ⟶ B`, read through the comparison
isomorphisms `F A' ≅ A''` and `F B' ≅ B''` of `CategoryTheory.rightDualIso`, is the mate of
`F f`.

For the derived pullback and the derived duals of perfect objects this is the naturality of the
identification `Lg^*(K^∨) ≅ (Lg^*K)^∨` of `Stacks.SheafOfModules.derivedPullbackDerivedDualIso`,
which the base change of [Stacks, Tag 0DJS] carries along the transition maps of the perfect
approximations of [Stacks, Tag 08IF] (B).

## Main results

* `CategoryTheory.ExactPairing.mate_comp_rightDualIso`: the comparison of two choices of duals is
  natural for mates.
* `CategoryTheory.ExactPairing.map_mate_comp_rightDualIso`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.ExactPairing

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- The mate of an identity between two choices of dual of one object is the comparison
isomorphism `CategoryTheory.rightDualIso`. -/
theorem mate_id_eq_rightDualIso_hom {A A₁ A₂ : C} (p₁ : ExactPairing A A₁)
    (p₂ : ExactPairing A A₂) :
    mate p₂ p₁ (𝟙 A) = (rightDualIso p₁ p₂).hom :=
  rfl

/-- The mate of a composite is the composite of the mates, for arbitrary choices of duals. -/
theorem mate_comp {A B E A' B' E' : C} (pA : ExactPairing A A') (pB : ExactPairing B B')
    (pE : ExactPairing E E') (f : A ⟶ B) (g : B ⟶ E) :
    mate pA pE (f ≫ g) = mate pB pE g ≫ mate pA pB f :=
  @comp_rightAdjointMate C _ _ A B E (hasRightDual pA) (hasRightDual pB) (hasRightDual pE) f g

/-- **The comparison of two choices of duals is natural for mates.** For `f : A ⟶ B` and two
pairings of each of `A` and `B`, the two mates of `f` differ by the comparison isomorphisms. -/
theorem mate_comp_rightDualIso {A B A₁ A₂ B₁ B₂ : C} (pA₁ : ExactPairing A A₁)
    (pA₂ : ExactPairing A A₂) (pB₁ : ExactPairing B B₁) (pB₂ : ExactPairing B B₂) (f : A ⟶ B) :
    mate pA₁ pB₁ f ≫ (rightDualIso pA₁ pA₂).hom =
      (rightDualIso pB₁ pB₂).hom ≫ mate pA₂ pB₂ f := by
  rw [← mate_id_eq_rightDualIso_hom, ← mate_id_eq_rightDualIso_hom, ← mate_comp, ← mate_comp,
    Category.id_comp, Category.comp_id]

/-- **A monoidal functor carries mates to mates, through the comparison of duals.** For `f : A ⟶ B`
with pairings `pA`, `pB` in `C` and pairings `qA`, `qB` of `F A`, `F B` in `D`,
`F(mate f) ≫ (F A' ≅ A'') = (F B' ≅ B'') ≫ mate (F f)`. -/
theorem map_mate_comp_rightDualIso (F : C ⥤ D) [F.Monoidal] {A B A' B' : C} {A'' B'' : D}
    (pA : ExactPairing A A') (pB : ExactPairing B B')
    (qA : ExactPairing (F.obj A) A'') (qB : ExactPairing (F.obj B) B'') (f : A ⟶ B) :
    F.map (mate pA pB f) ≫
        (rightDualIso (@ExactPairing.map C D _ _ _ _ F _ A A' pA) qA).hom =
      (rightDualIso (@ExactPairing.map C D _ _ _ _ F _ B B' pB) qB).hom ≫
        mate qA qB (F.map f) := by
  rw [map_mate F pA pB f, mate_comp_rightDualIso]

/-- **Frobenius reciprocity on the left is natural for mates.** For `g : Y₁ ⟶ Y₂` with pairings
`p₁`, `p₂` and `f : Y₁' ⊗ X ⟶ Z`, transposing `mate g ▷ X ≫ f` across `p₂` is transposing `f`
across `p₁` followed by `g ▷ Z`. -/
theorem tensorLeftHomEquiv_mate_whiskerRight {X Y₁ Y₂ Y₁' Y₂' Z : C} (p₁ : ExactPairing Y₁ Y₁')
    (p₂ : ExactPairing Y₂ Y₂') (g : Y₁ ⟶ Y₂) (f : Y₁' ⊗ X ⟶ Z) :
    @tensorLeftHomEquiv C _ _ X Y₂ Y₂' Z p₂ (mate p₁ p₂ g ▷ X ≫ f) =
      @tensorLeftHomEquiv C _ _ X Y₁ Y₁' Z p₁ f ≫ g ▷ Z := by
  have h := coevaluation_comp_mate p₁ p₂ g
  simp only [tensorLeftHomEquiv, Equiv.coe_fn_mk, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [← MonoidalCategory.associator_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc]
  show _ ≫ (p₂.coevaluation' ≫ Y₂ ◁ mate p₁ p₂ g) ▷ X ≫ _ = _
  rw [h, MonoidalCategory.comp_whiskerRight_assoc,
    MonoidalCategory.associator_naturality_left_assoc, MonoidalCategory.whisker_exchange]
  rfl

/-- **Frobenius reciprocity on the right is natural for mates.** For `g : Y₁ ⟶ Y₂` with pairings
`p₁`, `p₂` and `f : X ⊗ Y₂ ⟶ Z`, transposing `X ◁ g ≫ f` across `p₁` is transposing `f` across
`p₂` followed by `Z ◁ mate g`. -/
theorem tensorRightHomEquiv_whiskerLeft_mate {X Y₁ Y₂ Y₁' Y₂' Z : C} (p₁ : ExactPairing Y₁ Y₁')
    (p₂ : ExactPairing Y₂ Y₂') (g : Y₁ ⟶ Y₂) (f : X ⊗ Y₂ ⟶ Z) :
    @tensorRightHomEquiv C _ _ X Y₁ Y₁' Z p₁ (X ◁ g ≫ f) =
      @tensorRightHomEquiv C _ _ X Y₂ Y₂' Z p₂ f ≫ Z ◁ mate p₁ p₂ g := by
  have h := coevaluation_comp_mate p₁ p₂ g
  simp only [tensorRightHomEquiv, Equiv.coe_fn_mk, MonoidalCategory.comp_whiskerRight,
    Category.assoc]
  rw [← MonoidalCategory.associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  show _ ≫ X ◁ (p₁.coevaluation' ≫ g ▷ Y₁') ≫ _ = _
  rw [← h, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.associator_inv_naturality_right_assoc, ← MonoidalCategory.whisker_exchange]
  rfl

end CategoryTheory.ExactPairing

end
