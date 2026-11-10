module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitExtSystem

/-!
# Restricting a directed system of schemes to an open of its least stage

Let `(X_i)` be an inverse system of schemes over a preorder with a least index `⊥`, with limit
cone `c`, and let `ι : W ⟶ X_⊥`. The base changes `X_i ×_{X_⊥} W` form an inverse system with
limit `c.pt ×_{X_⊥} W` (`isLimitRestrictCone`), whose transition morphisms are affine when those
of `(X_i)` are.

## Main definitions

* `Stacks.EtaleCohomology.LimitExt.restrictSystem`: the inverse system `i ↦ X_i ×_{X_⊥} W`.
* `Stacks.EtaleCohomology.LimitExt.restrictCone`: the cone with vertex `c.pt ×_{X_⊥} W` over it.

## Main results

* `Stacks.EtaleCohomology.LimitExt.isLimitRestrictCone`: base change preserves the limit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LimitExt

section Restrict

variable {J : Type u} [Preorder J] [OrderBot J]
  (E : Jᵒᵖ ⥤ Scheme.{u}) (c : Cone E) {W : Scheme.{u}} (ι : W ⟶ E.obj (op ⊥))

/-- A transition morphism `X_i ⟶ X_{i'}` followed by `X_{i'} ⟶ X_⊥` is the morphism
`X_i ⟶ X_⊥`. -/
theorem map_toBot {i i' : Jᵒᵖ} (a : i ⟶ i') :
    E.map a ≫ toBot E i'.unop = toBot E i.unop := by
  rw [← E.map_comp]
  exact congrArg E.map (Subsingleton.elim _ _)

/-- The system of base changes `X_i ×_{X_⊥} W`. -/
abbrev restrictSystem : Jᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback (toBot E i.unop) ι
  map {i i'} a := pullback.lift (pullback.fst _ _ ≫ E.map a) (pullback.snd _ _)
    (by rw [Category.assoc, map_toBot]; exact pullback.condition)
  map_id i := pullback.hom_ext
    (by rw [pullback.lift_fst, E.map_id, Category.comp_id, Category.id_comp])
    (by rw [pullback.lift_snd, Category.id_comp])
  map_comp a b := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc,
      E.map_comp, Category.assoc])
    (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd])

/-- The transition morphism of `restrictSystem E ι` along `a` is the base change of `E.map a`. -/
theorem restrictSystem_map {i i' : Jᵒᵖ} (a : i ⟶ i') :
    (restrictSystem E ι).map a = pullback.lift (pullback.fst _ _ ≫ E.map a) (pullback.snd _ _)
      (by rw [Category.assoc, map_toBot]; exact pullback.condition) := rfl

/-- The base changed limit cone. -/
abbrev restrictCone (c : Cone E) : Cone (restrictSystem E ι) where
  pt := pullback (c.π.app (op ⊥)) ι
  π :=
    { app i := pullback.lift (pullback.fst (c.π.app (op ⊥)) ι ≫ c.π.app i)
        (pullback.snd (c.π.app (op ⊥)) ι)
        (by rw [Category.assoc, c.w]; exact pullback.condition)
      naturality {i i'} a := by
        apply pullback.hom_ext
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, c.w]
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, pullback.lift_snd] }

/-- The projection of `restrictCone E ι c` to the stage `i` is the base change of `c.π.app i`. -/
theorem restrictCone_π_app (i : Jᵒᵖ) :
    (restrictCone E ι c).π.app i = pullback.lift (pullback.fst (c.π.app (op ⊥)) ι ≫ c.π.app i)
      (pullback.snd (c.π.app (op ⊥)) ι) (by rw [Category.assoc, c.w]; exact pullback.condition) :=
  rfl

/-- The projection of a stage of the restricted system to the stage of the system. -/
abbrev rfst (i : J) : (restrictSystem E ι).obj (op i) ⟶ E.obj (op i) := pullback.fst (toBot E i) ι

/-- The projection of a stage of the restricted system to `W`. -/
abbrev rsnd (i : J) : (restrictSystem E ι).obj (op i) ⟶ W := pullback.snd (toBot E i) ι

/-- The projection of the limit of the restricted system to the limit of the system. -/
abbrev rfstL : (restrictCone E ι c).pt ⟶ c.pt := pullback.fst (c.π.app (op ⊥)) ι

/-- The projection of the limit of the restricted system to `W`. -/
abbrev rsndL : (restrictCone E ι c).pt ⟶ W := pullback.snd (c.π.app (op ⊥)) ι

/-- The transition morphisms of the restricted system commute with the projections to `W`. -/
theorem restrictSystem_map_snd {i i' : J} (a : op i' ⟶ op i) :
    (restrictSystem E ι).map a ≫ rsnd E ι i = rsnd E ι i' :=
  pullback.lift_snd _ _ _

/-- The transition morphisms of the restricted system lie over those of `E` under the projections
`rfst`. -/
theorem restrictSystem_map_fst {i i' : J} (a : op i' ⟶ op i) :
    (restrictSystem E ι).map a ≫ rfst E ι i = rfst E ι i' ≫ E.map a :=
  pullback.lift_fst _ _ _

/-- The projections of `restrictCone E ι c` commute with the projections to `W`. -/
theorem restrictCone_π_snd (i : J) :
    (restrictCone E ι c).π.app (op i) ≫ rsnd E ι i = rsndL E c ι :=
  pullback.lift_snd _ _ _

/-- The projections of `restrictCone E ι c` lie over those of `c` under `rfstL` and `rfst`. -/
theorem restrictCone_π_fst (i : J) :
    (restrictCone E ι c).π.app (op i) ≫ rfst E ι i = rfstL E c ι ≫ c.π.app (op i) :=
  pullback.lift_fst _ _ _

/-- The square defining the stage `X_i ×_{X_⊥} W` of the restricted system commutes. -/
theorem rfst_toBot (i : J) : rfst E ι i ≫ toBot E i = rsnd E ι i ≫ ι := pullback.condition

/-- The square defining the vertex `c.pt ×_{X_⊥} W` of the restricted cone commutes. -/
theorem rfstL_cone : rfstL E c ι ≫ c.π.app (op ⊥) = rsndL E c ι ≫ ι := pullback.condition

/-- **Base change preserves the limit**: `X ×_{X_⊥} W = lim_i (X_i ×_{X_⊥} W)`. -/
def isLimitRestrictCone (hc : IsLimit c) : IsLimit (restrictCone E ι c) where
  lift s := pullback.lift
    (hc.lift
      { pt := s.pt
        π :=
          { app i := s.π.app i ≫ pullback.fst (toBot E i.unop) ι
            naturality {i i'} a := by
              have := s.w a
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this ⊢
              rw [← this, Category.assoc, pullback.lift_fst, Category.assoc] } })
    (s.π.app (op ⊥) ≫ pullback.snd (toBot E ⊥) ι) (by
      have hbotid : toBot E (⊥ : J) = 𝟙 _ := by
        change E.map ((homOfLE bot_le).op : op (⊥ : J) ⟶ op ⊥) = _
        rw [show ((homOfLE bot_le).op : op (⊥ : J) ⟶ op ⊥) = 𝟙 _ from Subsingleton.elim _ _,
          E.map_id]
      rw [hc.fac, Category.assoc, ← pullback.condition]
      exact ((congrArg (fun x => s.π.app (op ⊥) ≫ pullback.fst (toBot E ⊥) ι ≫ x) hbotid).trans
        (by rw [Category.comp_id])).symm)
  fac s i := by
    apply pullback.hom_ext
    · rw [Category.assoc, restrictCone_π_app, pullback.lift_fst, pullback.lift_fst_assoc, hc.fac]
    · rw [Category.assoc, restrictCone_π_app, pullback.lift_snd, pullback.lift_snd,
        ← s.w ((homOfLE bot_le).op : i ⟶ op ⊥), Category.assoc, restrictSystem_map,
        pullback.lift_snd]
  uniq s m hm := by
    refine pullback.hom_ext (f := c.π.app (op ⊥)) (g := ι) (W := s.pt) ?_ ?_
    · rw [pullback.lift_fst]
      refine hc.hom_ext (fun i => ?_)
      rw [hc.fac]
      change _ = s.π.app i ≫ pullback.fst (toBot E i.unop) ι
      rw [← hm i, restrictCone_π_app]
      simp only [Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, ← hm (op ⊥), restrictCone_π_app]
      simp only [Category.assoc, pullback.lift_snd]

/-- If the transition morphisms of `E` are affine, so are those of `restrictSystem E ι`. -/
instance [∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (E.map a)] {i j : Jᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((restrictSystem E ι).map a) := by
  have t : IsPullback (pullback.fst (toBot E j.unop) ι) (pullback.snd _ _) (toBot E j.unop) ι :=
    IsPullback.of_hasPullback _ _
  have s : IsPullback (pullback.fst (toBot E i.unop) ι)
      ((restrictSystem E ι).map a ≫ pullback.snd (toBot E j.unop) ι)
      (E.map a ≫ toBot E j.unop) ι := by
    rw [restrictSystem_map, pullback.lift_snd, map_toBot]
    exact IsPullback.of_hasPullback _ _
  have top := IsPullback.of_bot s (by rw [restrictSystem_map, pullback.lift_fst]) t
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) top inferInstance

end Restrict

end Stacks.EtaleCohomology.LimitExt
