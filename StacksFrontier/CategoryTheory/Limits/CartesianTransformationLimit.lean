module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Limits along a cartesian natural transformation

Let `α : E ⟶ D` be a natural transformation between cofiltered diagrams all of whose naturality
squares are cartesian, and let `cD` be a limit cone of `D`. A cone `cE` on `E` with a map of
vertices `β : cE.pt ⟶ cD.pt` making every square `cE.pt ⟶ E j` over `cD.pt ⟶ D j` cartesian is a
limit cone: `lim E = E j ×_{D j} lim D`.

This is used in the proof of Stacks 07SU to compute the limit of the relations `Rᵢ` and of the
charts `Vᵢ` over a system of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Limits

section Cone

variable {J : Type w} [Category J] [IsCofiltered J] {C : Type u} [Category.{v} C]
  {D E : J ⥤ C} (α : E ⟶ D)
  (hα : ∀ {a b : J} (g : a ⟶ b), IsPullback (E.map g) (α.app a) (α.app b) (D.map g))
  {cD : Cone D} (hD : IsLimit cD) (cE : Cone E) (β : cE.pt ⟶ cD.pt)
  (hcart : ∀ j, IsPullback (cE.π.app j) β (α.app j) (cD.π.app j))

include hα hD hcart in
/-- **A cone over a cartesian natural transformation, cartesian over a limit cone, is a limit
cone.** -/
noncomputable def isLimitOfCartesian : IsLimit cE := by
  classical
  let j₀ : J := (IsCofiltered.nonempty (C := J)).some
  -- the cone on `D` induced by a cone on `E`
  let sD (s : Cone E) : Cone D :=
    ⟨s.pt, { app := fun j => s.π.app j ≫ α.app j
             naturality := fun a b g => by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                 Category.assoc, ← α.naturality]
               rw [← Category.assoc, s.w g] }⟩
  let lift (s : Cone E) : s.pt ⟶ cE.pt :=
    (hcart j₀).lift (s.π.app j₀) (hD.lift (sD s)) (by rw [hD.fac])
  have lift₀ (s : Cone E) : lift s ≫ cE.π.app j₀ = s.π.app j₀ := (hcart j₀).lift_fst _ _ _
  have liftβ (s : Cone E) : lift s ≫ β = hD.lift (sD s) := (hcart j₀).lift_snd _ _ _
  have hβ (j : J) : cE.π.app j ≫ α.app j = β ≫ cD.π.app j := (hcart j).w
  refine
    { lift := lift
      fac := fun s j => ?_
      uniq := fun s m hm => ?_ }
  · let k := IsCofiltered.min j j₀
    let gkj : k ⟶ j := IsCofiltered.minToLeft j j₀
    let gk₀ : k ⟶ j₀ := IsCofiltered.minToRight j j₀
    have key : lift s ≫ cE.π.app k = s.π.app k := by
      refine (hα gk₀).hom_ext ?_ ?_
      · rw [Category.assoc, cE.w gk₀, lift₀, s.w gk₀]
      · rw [Category.assoc, hβ, ← Category.assoc, liftβ, hD.fac]
    rw [← cE.w gkj, ← Category.assoc, key, s.w gkj]
  · refine (hcart j₀).hom_ext ?_ ?_
    · rw [lift₀, hm]
    · rw [liftβ]
      refine hD.hom_ext fun j => ?_
      rw [hD.fac, Category.assoc, ← hβ, ← Category.assoc, hm]

end Cone

section Stage

variable {J : Type w} [Category.{w} J] [IsCofiltered J] {C : Type u} [Category.{v} C]
  {D E : J ⥤ C} (α : E ⟶ D)
  (hα : ∀ {a b : J} (g : a ⟶ b), IsPullback (E.map g) (α.app a) (α.app b) (D.map g))
  {cE : Cone E} (hE : IsLimit cE) {cD : Cone D} (hD : IsLimit cD) (β : cE.pt ⟶ cD.pt)
  (hβ : ∀ j, cE.π.app j ≫ α.app j = β ≫ cD.π.app j)

include hα hE hD hβ in
/-- **Over a cartesian natural transformation, the limit square at every stage is cartesian.**
If `α : E ⟶ D` has cartesian naturality squares and `β : lim E ⟶ lim D` is the induced map of
limits, then `lim E = E j ×_{D j} lim D` for every `j`. -/
theorem isPullback_of_isLimit_of_cartesian (j : J) :
    IsPullback (cE.π.app j) β (α.app j) (cD.π.app j) := by
  classical
  let F := Over.forget j
  have hE' : IsLimit (cE.whisker F) := (Functor.Initial.isLimitWhiskerEquiv F cE).symm hE
  have hD' : IsLimit (cD.whisker F) := (Functor.Initial.isLimitWhiskerEquiv F cD).symm hD
  -- the legs of the lift, on the stages over `j`
  let lk (s : PullbackCone (α.app j) (cD.π.app j)) (k : Over j) : s.pt ⟶ E.obj k.left :=
    (hα k.hom).lift s.fst (s.snd ≫ cD.π.app k.left)
      (by rw [Category.assoc, cD.w, ← s.condition])
  have lk_fst (s : PullbackCone (α.app j) (cD.π.app j)) (k : Over j) :
      lk s k ≫ E.map k.hom = s.fst := IsPullback.lift_fst _ _ _ _
  have lk_snd (s : PullbackCone (α.app j) (cD.π.app j)) (k : Over j) :
      lk s k ≫ α.app k.left = s.snd ≫ cD.π.app k.left := IsPullback.lift_snd _ _ _ _
  have hnat (s : PullbackCone (α.app j) (cD.π.app j)) {k k' : Over j} (h : k ⟶ k') :
      lk s k ≫ E.map h.left = lk s k' := by
    refine (hα k'.hom).hom_ext ?_ ?_
    · rw [Category.assoc, ← E.map_comp, Over.w h, lk_fst, lk_fst]
    · rw [Category.assoc, α.naturality, ← Category.assoc, lk_snd, lk_snd, Category.assoc,
        cD.w]
  let cs (s : PullbackCone (α.app j) (cD.π.app j)) : Cone (F ⋙ E) :=
    ⟨s.pt, { app := lk s
             naturality := fun _ _ h => by
               change 𝟙 _ ≫ lk s _ = lk s _ ≫ E.map h.left
               rw [Category.id_comp, hnat] }⟩
  have hfac (s : PullbackCone (α.app j) (cD.π.app j)) (k : Over j) :
      hE'.lift (cs s) ≫ cE.π.app k.left = lk s k := hE'.fac (cs s) k
  refine ⟨⟨hβ j⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => hE'.lift (cs s))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_)⟩⟩
  · have := hfac s (Over.mk (𝟙 j))
    have h1 := lk_fst s (Over.mk (𝟙 j))
    simp only [Over.mk_left, Over.mk_hom, CategoryTheory.Functor.map_id, Category.comp_id] at h1
    exact this.trans h1
  · refine hD'.hom_ext fun k => ?_
    change _ ≫ cD.π.app k.left = s.snd ≫ cD.π.app k.left
    rw [Category.assoc, ← hβ, ← Category.assoc, hfac, lk_snd]
  · refine hE'.hom_ext fun k => ?_
    change m ≫ cE.π.app k.left = hE'.lift (cs s) ≫ cE.π.app k.left
    rw [hfac]
    refine (hα k.hom).hom_ext ?_ ?_
    · rw [Category.assoc, cE.w, hm₁, lk_fst]
    · rw [lk_snd, Category.assoc, hβ, ← Category.assoc, hm₂]

end Stage

end CategoryTheory.Limits

end
