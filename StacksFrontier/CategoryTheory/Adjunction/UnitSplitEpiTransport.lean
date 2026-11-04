module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Splitting the unit of an adjunction is a property of the left adjoint

Whether the unit `x ⟶ R.obj (L.obj x)` of an adjunction `L ⊣ R` is a split epimorphism does not
depend on which right adjoint of `L` is used, nor on replacing `L` by an isomorphic functor: in
both cases the unit changes by composition with an isomorphism.

## Main results

* `Stacks.Adjunction.splitEpiOfCompIsIso`: a morphism whose composite with an isomorphism is a
  split epimorphism is a split epimorphism.
* `Stacks.Adjunction.splitEpiUnitOfSplitEpiUnit`: a splitting of the unit of one adjunction with
  left adjoint `L` splits the unit of any other.
* `Stacks.Adjunction.splitEpiUnitOfNatIsoLeft`: a splitting of the unit of the transport of an
  adjunction along an isomorphism of left adjoints splits the original unit.
* `Stacks.Adjunction.splitEpiUnitOfSplitEpiUnitOfIsoLeft`: a splitting of the unit of an
  adjunction whose left adjoint is isomorphic to `L` splits the unit of an adjunction with left
  adjoint `L`.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A morphism whose composite with an isomorphism is a split epimorphism is itself one.**
The section is the isomorphism followed by the given section. -/
noncomputable def splitEpiOfCompIsIso {A A' A'' : C} (u : A ⟶ A') (θ : A' ⟶ A'') [IsIso θ]
    (h : SplitEpi (u ≫ θ)) : SplitEpi u where
  section_ := θ ≫ h.section_
  id := by
    rw [← cancel_mono θ, Category.id_comp, Category.assoc, Category.assoc, h.id, Category.comp_id]

/-- **Whether the unit of an adjunction is a split epimorphism does not depend on the chosen
right adjoint.**  The section is the inverse of the comparison
`CategoryTheory.Adjunction.rightAdjointUniq` of the two right adjoints followed by the given
section. -/
noncomputable def splitEpiUnitOfSplitEpiUnit {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R)
    (adj' : L ⊣ R') (x : C) (h : SplitEpi (adj.unit.app x)) : SplitEpi (adj'.unit.app x) where
  section_ := (CategoryTheory.Adjunction.rightAdjointUniq adj adj').inv.app (L.obj x) ≫
    h.section_
  id := by
    rw [← CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app adj adj' x, Category.assoc,
      ← Category.assoc h.section_, h.id, Category.id_comp, Iso.inv_hom_id_app]
    rfl

/-- **Transporting an adjunction along an isomorphism of left adjoints does not change whether
its unit is a split epimorphism.** -/
noncomputable def splitEpiUnitOfNatIsoLeft {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (iso : L ≅ L') (x : C)
    (h : SplitEpi ((CategoryTheory.Adjunction.ofNatIsoLeft adj iso).unit.app x)) :
    SplitEpi (adj.unit.app x) :=
  splitEpiOfCompIsIso (adj.unit.app x) (R.map (iso.hom.app x)) h

/-- **A splitting of the unit of any adjunction whose left adjoint is isomorphic to `L` splits
the unit of an adjunction with left adjoint `L`.** -/
noncomputable def splitEpiUnitOfSplitEpiUnitOfIsoLeft {L L' : C ⥤ D} {R R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (iso : L ≅ L') (x : C)
    (h : SplitEpi (adj'.unit.app x)) : SplitEpi (adj.unit.app x) :=
  splitEpiUnitOfNatIsoLeft adj iso x
    (splitEpiUnitOfSplitEpiUnit adj' (CategoryTheory.Adjunction.ofNatIsoLeft adj iso) x h)

end Stacks.Adjunction

end
