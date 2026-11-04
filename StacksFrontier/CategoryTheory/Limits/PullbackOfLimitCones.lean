module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# A pullback of limit cones is a limit cone

Let `F₁ ⟶ F₃ ⟵ F₂` be natural transformations of diagrams `J ⥤ C`, and let `P` be a diagram with
projections to `F₁` and `F₂` whose squares are pullback squares at every index. If `c₁`, `c₂`,
`c₃` are limit cones over `F₁`, `F₂`, `F₃`, compatibly with the transformations, then a cone over
`P` whose cone point is the pullback of the cone points of `c₁` and `c₂` over that of `c₃` is a
limit cone. This is the elementary instance of the commutation of limits with limits which is
used to see that fibre products of cofiltered systems of schemes have the expected limit.

## Main results

* `CategoryTheory.Limits.isLimitOfIsPullbackOfIsLimit`: the statement above.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u v' u'

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]
  {F₁ F₂ F₃ P : J ⥤ C} {α : F₁ ⟶ F₃} {β : F₂ ⟶ F₃} {π₁ : P ⟶ F₁} {π₂ : P ⟶ F₂}
  {c₁ : Cone F₁} {c₂ : Cone F₂} {c₃ : Cone F₃} {d : Cone P}
  {z₁ : d.pt ⟶ c₁.pt} {z₂ : d.pt ⟶ c₂.pt} {g₁ : c₁.pt ⟶ c₃.pt} {g₂ : c₂.pt ⟶ c₃.pt}

/-- **A pullback of limit cones is a limit cone.** Given a diagram `P` whose squares over the
cospans `F₁ j ⟶ F₃ j ⟵ F₂ j` are pullbacks, and a cone `d` over `P` whose cone point is the
pullback of the cone points of limit cones `c₁`, `c₂` over that of a limit cone `c₃`, compatibly
with all the maps, `d` is a limit cone. -/
noncomputable def isLimitOfIsPullbackOfIsLimit
    (hP : ∀ j, IsPullback (π₁.app j) (π₂.app j) (α.app j) (β.app j))
    (hc₁ : IsLimit c₁) (hc₂ : IsLimit c₂) (hc₃ : IsLimit c₃)
    (hz : IsPullback z₁ z₂ g₁ g₂)
    (h₁ : ∀ j, d.π.app j ≫ π₁.app j = z₁ ≫ c₁.π.app j)
    (h₂ : ∀ j, d.π.app j ≫ π₂.app j = z₂ ≫ c₂.π.app j)
    (hg₁ : ∀ j, c₁.π.app j ≫ α.app j = g₁ ≫ c₃.π.app j)
    (hg₂ : ∀ j, c₂.π.app j ≫ β.app j = g₂ ≫ c₃.π.app j) :
    IsLimit d := by
  have hw : ∀ s : Cone P, hc₁.lift (Cone.mk s.pt (s.π ≫ π₁)) ≫ g₁ =
      hc₂.lift (Cone.mk s.pt (s.π ≫ π₂)) ≫ g₂ := fun s =>
    hc₃.hom_ext fun j => by
      rw [Category.assoc, Category.assoc, ← hg₁, ← hg₂, hc₁.fac_assoc, hc₂.fac_assoc]
      simp only [NatTrans.comp_app, Category.assoc]
      rw [(hP j).w]
  refine
    { lift := fun s => hz.lift (hc₁.lift (Cone.mk s.pt (s.π ≫ π₁)))
        (hc₂.lift (Cone.mk s.pt (s.π ≫ π₂))) (hw s)
      fac := fun s j => ?_
      uniq := fun s m hm => ?_ }
  · refine (hP j).hom_ext ?_ ?_
    · rw [Category.assoc, h₁, IsPullback.lift_fst_assoc, hc₁.fac]
      rfl
    · rw [Category.assoc, h₂, IsPullback.lift_snd_assoc, hc₂.fac]
      rfl
  · refine hz.hom_ext ?_ ?_
    · rw [IsPullback.lift_fst]
      refine hc₁.hom_ext fun j => ?_
      rw [hc₁.fac, Category.assoc, ← h₁, ← Category.assoc, hm]
      rfl
    · rw [IsPullback.lift_snd]
      refine hc₂.hom_ext fun j => ?_
      rw [hc₂.fac, Category.assoc, ← h₂, ← Category.assoc, hm]
      rfl

end CategoryTheory.Limits

end
