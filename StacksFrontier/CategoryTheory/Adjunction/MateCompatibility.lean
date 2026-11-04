module

public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Mates: compatibility of transitions

## Main results

* `Stacks.CategoryTheory.mate_compat`: transposes of compatible transformations are compatible
  up to the Beck–Chevalley mate of the comparison of right adjoints.

## Implementation notes

This declaration extends `StacksFrontier/CategoryTheory/Adjunction/Mates.lean`; it sits in a file
of its own. The two lemmas it uses,
`Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv` and
`Stacks.CategoryTheory.unit_comp_map_eq_eqToHom`, are in
`StacksFrontier/CategoryTheory/Adjunction/Mates.lean`.
-/

@[expose] public section

open CategoryTheory TwoSquare

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.CategoryTheory

section MateCompat

universe v₅ v₆ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
  {T : Type u₅} [Category.{v₅} T] {T' : Type u₆} [Category.{v₆} T']
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}

/-- **Transitions are compatible with localization.** Let `α` and `θ` be the transposes, across
`L₁ ⊣ R₁` and `L₂ ⊣ R₂`, of two transformations `β : P ⟶ Q ⋙ R₁` and `β' : P' ⟶ Q' ⋙ R₂`, and
let `e : R₁ ⋙ G ⟶ H ⋙ R₂` compare the two right adjoints along `G` and `H`. If `β'` at `J t`
is `G` of `β` at `t`, up to the identifications `hP` and `hQ` and to `e`, then `θ` at `J t` is
`H` of `α` at `t` up to the same identifications and the Beck–Chevalley mate of `e`. -/
theorem mate_compat (e : TwoSquare R₁ H G R₂) {P : T ⥤ C} {Q : T ⥤ D} (β : P ⟶ Q ⋙ R₁)
    {P' : T' ⥤ E} {Q' : T' ⥤ F} (β' : P' ⟶ Q' ⋙ R₂) (J : T ⥤ T') (t : T)
    (hP : P'.obj (J.obj t) ≅ G.obj (P.obj t)) (hQ : Q'.obj (J.obj t) ≅ H.obj (Q.obj t))
    (hβ : β'.app (J.obj t) ≫ R₂.map hQ.hom =
      hP.hom ≫ G.map (β.app t) ≫ e.app (Q.obj t)) :
    L₂.map hP.hom ≫ ((mateEquiv adj₁ adj₂).symm e).app (P.obj t) ≫
        H.map ((adj₁.homEquiv _ _).symm (β.app t)) =
      (adj₂.homEquiv _ _).symm (β'.app (J.obj t)) ≫ hQ.hom := by
  apply (adj₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, hβ, Adjunction.homEquiv_unit]
  have h := unit_mateEquiv_symm adj₁ adj₂ e (P.obj t)
  dsimp only [Functor.id_obj] at h
  rw [← h]
  have hnat := e.naturality ((adj₁.homEquiv _ _).symm (β.app t))
  simp only [Functor.comp_map] at hnat
  have hβ1 : adj₁.unit.app (P.obj t) ≫ R₁.map ((adj₁.homEquiv _ _).symm (β.app t)) = β.app t :=
    (adj₁.homEquiv_unit _ _ _).symm.trans ((adj₁.homEquiv _ _).apply_symm_apply _)
  refine congrArg (hP.hom ≫ ·) ?_
  rw [Category.assoc]
  refine (congrArg (G.map (adj₁.unit.app (P.obj t)) ≫ ·) hnat.symm).trans ?_
  rw [← Category.assoc, ← G.map_comp, hβ1]

end MateCompat

end Stacks.CategoryTheory

end
