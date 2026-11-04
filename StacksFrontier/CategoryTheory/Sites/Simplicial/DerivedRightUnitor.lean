module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoCoherence
import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization

/-!
# The derived functor of a right unitor

`CategoryTheory.derivedIdIso` identifies the derived functor of the identity functor with the
identity functor of the derived category. This file does the same for the composite `F ⋙ 𝟭`: the
derived functor of `(CategoryTheory.Functor.rightUnitor F).hom` is the compositor of `F` and the
identity, followed by `derivedIdIso` whiskered with the derived functor of `F`, followed by the
right unitor of that derived functor.

## Main definitions

* `CategoryTheory.derivedRightUnitorIso`: the comparison
  `(F ⋙ 𝟭).mapDerivedCategory ≅ F.mapDerivedCategory`.

## Main results

* `CategoryTheory.derivedNatTrans_rightUnitor`: the derived functor of the right unitor of `F` is
  `CategoryTheory.derivedRightUnitorIso F`.
* `CategoryTheory.derivedNatTrans_whiskerLeft_comp_rightUnitor`: the derived functor of the
  transformation `E ⋙ G ⟶ E` obtained by whiskering `α : G ⟶ 𝟭` on the left by `E` and composing
  with the right unitor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

section RightUnitor

variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The comparison of the derived functor of `F ⋙ 𝟭` with the derived functor of `F`: the
compositor of `F` and the identity functor, followed by `CategoryTheory.derivedIdIso` in the outer
position and the right unitor of the derived functor of `F`. -/
def derivedRightUnitorIso : (F ⋙ 𝟭 B).mapDerivedCategory ≅ F.mapDerivedCategory :=
  derivedCompIso F (𝟭 B) (F ⋙ 𝟭 B) (Iso.refl _) ≪≫
    Functor.isoWhiskerLeft F.mapDerivedCategory (derivedIdIso (A := B)) ≪≫
      Functor.rightUnitor F.mapDerivedCategory

/-- The derived functor of the right unitor of `F` is `CategoryTheory.derivedRightUnitorIso F`. -/
theorem derivedNatTrans_rightUnitor :
    derivedNatTrans (F ⋙ 𝟭 B) F (Functor.rightUnitor F).hom = (derivedRightUnitorIso F).hom := by
  have key := derivedCompIso_unit_right F (𝟭 B) (F ⋙ 𝟭 B) (Iso.refl _) (Iso.refl _)
    (Functor.rightUnitor F).hom
    (derivedNatTrans (F ⋙ 𝟭 B) F (Functor.rightUnitor F).hom)
    (fun X => derivedNatTrans_app_Q (F ⋙ 𝟭 B) F (Functor.rightUnitor F).hom X)
    (fun X => by simp)
  have hrefl : (derivedNatIso (𝟭 B) (𝟭 B) (Iso.refl (𝟭 B))).hom = 𝟙 _ := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) fun X => ?_
    have hid : (NatIso.mapHomologicalComplex (Iso.refl (𝟭 B)) (ComplexShape.up ℤ)).hom.app X
        = 𝟙 _ := HomologicalComplex.hom_ext _ _ fun _ => rfl
    rw [derivedNatIso_hom_app_Q, hid, CategoryTheory.Functor.map_id]
    simp
  have hru : (Functor.rightUnitor F.mapDerivedCategory).hom = 𝟙 _ := rfl
  rw [← key, derivedRightUnitorIso]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, hrefl, Category.id_comp, hru,
    Category.comp_id]

end RightUnitor

section WhiskerLeftId

variable (E : A ⥤ B) (G : B ⥤ B) [E.Additive] [G.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- For `α : G ⟶ 𝟭`, the derived functor of `Functor.whiskerLeft E α` followed by the right unitor
of `E` is the compositor of `E` and `G`, followed by the derived functor of `α` and
`CategoryTheory.derivedIdIso` in the outer position, followed by the right unitor of the derived
functor of `E`. -/
theorem derivedNatTrans_whiskerLeft_comp_rightUnitor (α : G ⟶ 𝟭 B) :
    derivedNatTrans (E ⋙ G) E
        (Functor.whiskerLeft E α ≫ (Functor.rightUnitor E).hom) =
      (derivedCompIso E G (E ⋙ G) (Iso.refl _)).hom ≫
        Functor.whiskerLeft E.mapDerivedCategory
            (derivedNatTrans G (𝟭 B) α ≫ (derivedIdIso (A := B)).hom) ≫
          (Functor.rightUnitor E.mapDerivedCategory).hom := by
  rw [derivedNatTrans_comp, derivedNatTrans_rightUnitor, derivedRightUnitorIso, Iso.trans_hom,
    ← Category.assoc, derivedCompIso_refl_hom_whiskerLeft, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp]
  simp only [Category.assoc]

end WhiskerLeftId

end CategoryTheory

end
