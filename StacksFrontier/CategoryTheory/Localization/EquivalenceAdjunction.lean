module

public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# The adjunction of an equivalence of localized categories

Given an equivalence `E : C₁ ≌ C₂` and localization functors `L₁ : C₁ ⥤ D₁`, `L₂ : C₂ ⥤ D₂`, this
file identifies the adjunction of the equivalence `D₁ ≌ D₂` built by
`CategoryTheory.Localization.equivalence` from lifts of `E.functor ⋙ L₂` and `E.inverse ⋙ L₁` with
the localization `CategoryTheory.Adjunction.localization` of `E.toAdjunction`.

## Main definitions

* `Stacks.Localization.betaOfEquivalence`: the isomorphism `(E.inverse ⋙ L₁) ⋙ G' ≅ L₂` built from
  a square `L₁ ⋙ G' ≅ E.functor ⋙ L₂` and the counit of `E`.
* `Stacks.Localization.adjunctionOfSquares`: `CategoryTheory.Adjunction.localization` of
  `CategoryTheory.Equivalence.toAdjunction`, with the two 2-commutative squares given as
  isomorphisms rather than as `CatCommSq` instances.

## Main results

* `Stacks.Localization.adjunctionOfSquares_unit_app` and
  `Stacks.Localization.adjunctionOfSquares_counit_app`: the unit and counit at an object in the
  image of the localization functor, in terms of the two squares and the unit resp. counit of `E`.
* `Stacks.Localization.equivalence_toAdjunction`: the adjunction of the equivalence built by
  `CategoryTheory.Localization.equivalence` is `Stacks.Localization.adjunctionOfSquares`, for any
  choice of `α`.
* `Stacks.Localization.adjunctionOfSquares_unit_comp_symm_counit`: the unit of the localized
  adjunction of `E` and the counit of the localized adjunction of `E.symm` compose to the identity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Localization

namespace Stacks.Localization

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]

/-- The isomorphism an equivalence `E : C₁ ≌ C₂` of the source categories supplies for the `β`
argument of `CategoryTheory.Localization.equivalence`: the lifted square `cG` whiskered into
`E.inverse`, followed by the counit of `E`. -/
def betaOfEquivalence (E : C₁ ≌ C₂) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (G' : D₁ ⥤ D₂)
    (cG : L₁ ⋙ G' ≅ E.functor ⋙ L₂) :
    (E.inverse ⋙ L₁) ⋙ G' ≅ L₂ :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft E.inverse cG ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight E.counitIso L₂ ≪≫ Functor.leftUnitor L₂

variable (E : C₁ ≌ C₂)
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)
  (cG : L₁ ⋙ G' ≅ E.functor ⋙ L₂) (cF : L₂ ⋙ F' ≅ E.inverse ⋙ L₁)

/-- The localization of the adjunction of an equivalence `E : C₁ ≌ C₂`, with the two
2-commutative squares passed as the isomorphisms `cG` and `cF` instead of as `CatCommSq`
instances. -/
noncomputable def adjunctionOfSquares : G' ⊣ F' :=
  letI : CatCommSq E.functor L₁ L₂ G' := ⟨cG.symm⟩
  letI : CatCommSq E.inverse L₂ L₁ F' := ⟨cF.symm⟩
  E.toAdjunction.localization L₁ W₁ L₂ W₂ G' F'

/-- The unit of `Stacks.Localization.adjunctionOfSquares` at an object in the image of `L₁`: the
unit of `E` localized, read through the two squares. -/
theorem adjunctionOfSquares_unit_app (X : C₁) :
    (adjunctionOfSquares E L₁ W₁ L₂ W₂ G' F' cG cF).unit.app (L₁.obj X) =
      L₁.map (E.unitIso.hom.app X) ≫ cF.inv.app (E.functor.obj X) ≫ F'.map (cG.inv.app X) := by
  let : CatCommSq E.functor L₁ L₂ G' := ⟨cG.symm⟩
  let : CatCommSq E.inverse L₂ L₁ F' := ⟨cF.symm⟩
  exact Adjunction.localization_unit_app _ _ _ _ _ _ _ X

/-- The counit of `Stacks.Localization.adjunctionOfSquares` at an object in the image of `L₂`: the
counit of `E` localized, read through the two squares. -/
theorem adjunctionOfSquares_counit_app (X : C₂) :
    (adjunctionOfSquares E L₁ W₁ L₂ W₂ G' F' cG cF).counit.app (L₂.obj X) =
      G'.map (cF.hom.app X) ≫ cG.hom.app (E.inverse.obj X) ≫
        L₂.map (E.counitIso.hom.app X) := by
  let : CatCommSq E.functor L₁ L₂ G' := ⟨cG.symm⟩
  let : CatCommSq E.inverse L₂ L₁ F' := ⟨cF.symm⟩
  exact Adjunction.localization_counit_app _ _ _ _ _ _ _ X

/-- The adjunction of the equivalence of localized categories that
`CategoryTheory.Localization.equivalence` builds from an equivalence `E` of the source categories
is the localization of `E.toAdjunction`, whatever the isomorphism `α`. -/
theorem equivalence_toAdjunction :
    letI : Lifting L₁ W₁ (E.functor ⋙ L₂) G' := ⟨cG⟩
    letI : Lifting L₂ W₂ (E.inverse ⋙ L₁) F' := ⟨cF⟩
    ∀ (α : (E.functor ⋙ L₂) ⋙ F' ≅ L₁),
    (CategoryTheory.Localization.equivalence L₁ W₁ L₂ W₂ (E.functor ⋙ L₂) G'
          (E.inverse ⋙ L₁) F' α (betaOfEquivalence E L₁ L₂ G' cG)).toAdjunction =
      adjunctionOfSquares E L₁ W₁ L₂ W₂ G' F' cG cF := by
  let : Lifting L₁ W₁ (E.functor ⋙ L₂) G' := ⟨cG⟩
  let : Lifting L₂ W₂ (E.inverse ⋙ L₁) F' := ⟨cF⟩
  intro α
  refine Adjunction.ext_counit (natTrans_ext L₂ W₂ fun X => ?_)
  rw [adjunctionOfSquares_counit_app]
  exact (congrArg Iso.hom (CategoryTheory.Localization.equivalence_counitIso_app L₁ W₁ L₂ W₂
    (E.functor ⋙ L₂) G' (E.inverse ⋙ L₁) F' α (betaOfEquivalence E L₁ L₂ G' cG) X)).trans
    (by simp [betaOfEquivalence, Localization.Lifting.iso]; rfl)

/-- The unit of the localized adjunction of `E` and the counit of the localized adjunction of
`E.symm` compose to the identity. -/
theorem adjunctionOfSquares_unit_comp_symm_counit :
    (adjunctionOfSquares E L₁ W₁ L₂ W₂ G' F' cG cF).unit ≫
        (adjunctionOfSquares E.symm L₂ W₂ L₁ W₁ F' G' cF cG).counit = 𝟙 (𝟭 D₁) :=
  natTrans_ext L₁ W₁ fun X => by
    simp [adjunctionOfSquares_unit_app, adjunctionOfSquares_counit_app, ← F'.map_comp_assoc,
      ← L₁.map_comp]

end Stacks.Localization
