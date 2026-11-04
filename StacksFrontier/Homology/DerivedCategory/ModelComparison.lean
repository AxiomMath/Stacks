module

public import StacksFrontier.Homology.Perfect.Characterizing

@[expose] public noncomputable section

/-!
# Comparing two chosen models of the derived category

`HasDerivedCategory.{w} C` is the assumption that a localization of `CochainComplex C ℤ` at the
quasi-isomorphisms has been *chosen*, with morphisms in `Type w`. Two such choices give two
categories `DerivedCategory C`, and a statement proved for one says nothing about the other until
it is transported. `StacksDraft.Perfect.derivedEquivalence` already compares them: it takes both
`HasDerivedCategory` instances as explicit arguments and is therefore model-generic even though it
lives in a file that pins `HasDerivedCategory.standard`.

This file packages that comparison with the three further pieces a transport needs: the comparison
read on the localizations of *cochain complexes* rather than of the homotopy category, the same in
the other direction, and additivity.

The two directions are deliberately asymmetric. `modelCompQIso` is the comparison itself, lifted
from the homotopy category. Its companion `modelInverseCompQIso` is *defined* as the inverse of
`modelCompQIso` corrected by the unit of the equivalence, which is what makes
`modelInverseCompQIso_fac` hold by construction; that single equation is what a coherence chase
over a transport of normalized derived-functor data reduces to.

## Main definitions

* `StacksDraft.DerivedModel.modelEquiv` — the comparison equivalence of two chosen models.
* `StacksDraft.DerivedModel.modelCompQIso` — it identifies the two localization functors out of
  cochain complexes.
* `StacksDraft.DerivedModel.modelInverseCompQIso` — the comparison in the other direction.

## Main results

* `StacksDraft.DerivedModel.modelInverseCompQIso_fac` — the unit of the equivalence, the inverse
  image of the forward comparison and the backward comparison compose to the identity.
* `StacksDraft.DerivedModel.modelEquiv_functor_additive` — the comparison is additive.
-/

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u v w z

namespace StacksDraft.DerivedModel

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The comparison equivalence between two chosen derived categories of `C`. -/
abbrev modelEquiv (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C) :
    @DerivedCategory C _ _ h₁ ≌ @DerivedCategory C _ _ h₂ :=
  StacksDraft.Perfect.derivedEquivalence h₁ h₂

/-- The comparison equivalence identifies the two localizations of cochain complexes: it is a
lifting of the comparison of the two localizations of the homotopy category. -/
def modelCompQIso (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C) :
    @DerivedCategory.Q C _ _ h₁ ⋙ (modelEquiv h₁ h₂).functor ≅ @DerivedCategory.Q C _ _ h₂ :=
  Functor.isoWhiskerRight (@DerivedCategory.quotientCompQhIso C _ _ h₁).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _) ≪≫
    @DerivedCategory.quotientCompQhIso C _ _ h₂

/-- The comparison in the other direction: the inverse of the equivalence also identifies the two
localizations, by inverting `modelCompQIso` and cancelling the unit. -/
def modelInverseCompQIso (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C) :
    @DerivedCategory.Q C _ _ h₂ ⋙ (modelEquiv h₁ h₂).inverse ≅ @DerivedCategory.Q C _ _ h₁ :=
  Functor.isoWhiskerRight (modelCompQIso h₁ h₂).symm (modelEquiv h₁ h₂).inverse ≪≫
    Functor.isoWhiskerLeft (@DerivedCategory.Q C _ _ h₁) (modelEquiv h₁ h₂).unitIso.symm ≪≫
    (@DerivedCategory.Q C _ _ h₁).rightUnitor

/-- **The one equation a transport coherence reduces to.** Composing the unit of the comparison
equivalence with the inverse image of the forward comparison and then the backward comparison
gives the identity. -/
@[simp]
theorem modelInverseCompQIso_fac (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (X : CochainComplex C ℤ) :
    (modelEquiv h₁ h₂).unitIso.hom.app ((@DerivedCategory.Q C _ _ h₁).obj X) ≫
        (modelEquiv h₁ h₂).inverse.map ((modelCompQIso h₁ h₂).hom.app X) ≫
        (modelInverseCompQIso h₁ h₂).hom.app X = 𝟙 _ := by
  have h : (modelEquiv h₁ h₂).inverse.map ((modelCompQIso h₁ h₂).hom.app X) ≫
      (modelInverseCompQIso h₁ h₂).hom.app X =
      (modelEquiv h₁ h₂).unitIso.inv.app ((@DerivedCategory.Q C _ _ h₁).obj X) := by
    dsimp only [modelInverseCompQIso]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Iso.symm_hom]
    rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_app]
    simp
  rw [h, Iso.hom_inv_id_app]

/-- The comparison equivalence is additive: a functor out of a localization of the homotopy
category is additive as soon as its composite with the localization is, and that composite is the
other localization functor. -/
theorem modelEquiv_functor_additive (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) : (modelEquiv h₁ h₂).functor.Additive := by
  let := h₁
  let := h₂
  rw [Localization.functor_additive_iff (@DerivedCategory.Qh C _ _ h₁)
    (HomotopyCategory.subcategoryAcyclic C).trW]
  exact Functor.additive_of_iso (Localization.compUniqFunctor _ _ _).symm

end StacksDraft.DerivedModel

end
