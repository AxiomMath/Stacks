module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardIndexIso

/-!
# Adjoint functors induce adjoint pushforwards of presheaves of modules

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, let `S` and `R` be presheaves of rings on `C`
and `D`, and let `φ : S ⟶ F.op ⋙ R` and `ψ : R ⟶ G.op ⋙ S` be morphisms of presheaves of rings
compatible with the unit and the counit of the adjunction.  Then the pushforward of presheaves
of modules along `φ` is left adjoint to the pushforward along `ψ`.

This is the presheaf counterpart of Mathlib's `SheafOfModules.pushforwardPushforwardAdj`, which
asks both functors to be continuous for two Grothendieck topologies.  On presheaves no topology
is involved, and the statement applies to a left adjoint `F` which is not continuous — the
situation of the image-open functor of a small étale site, left adjoint to the inclusion of the
Zariski opens, along which the inverse image of presheaves is a precomposition.

## Main definitions

* `Stacks.PresheafOfModules.pushforwardPushforwardAdj`: `pushforward φ ⊣ pushforward ψ`.  Its
  unit and counit are restriction maps along the counit and the unit of `F ⊣ G`
  (`pushforwardPushforwardAdj_unit_app_app_apply`,
  `pushforwardPushforwardAdj_counit_app_app_apply`).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w t v₁ u₁ v₂ u₂

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{t}} {R : Dᵒᵖ ⥤ RingCat.{t}}
  (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)

/-- **If `F ⊣ G`, the pushforwards of presheaves of modules along `F` and `G` are adjoint**, for
morphisms of presheaves of rings `φ : S ⟶ F.op ⋙ R` and `ψ : R ⟶ G.op ⋙ S` compatible with the
unit and the counit.  The unit at `M` is the restriction of `M` along the counit of `F ⊣ G`, and
the counit at `N` is the restriction of `N` along the unit. -/
def pushforwardPushforwardAdj :
    _root_.PresheafOfModules.pushforward.{w} φ ⊣ _root_.PresheafOfModules.pushforward.{w} ψ where
  unit := pushforwardIndexMap.{w} (K := 𝟭 D) (L := G ⋙ F) (φ := 𝟙 R)
    (ψ := ψ ≫ G.op.whiskerLeft φ) (NatTrans.op adj.counit) (by rw [Category.id_comp, H₁])
  counit := pushforwardIndexMap.{w} (K := F ⋙ G) (L := 𝟭 C)
    (φ := φ ≫ F.op.whiskerLeft ψ) (ψ := 𝟙 S) (NatTrans.op adj.unit)
    (by rw [Category.assoc, H₂])
  left_triangle_components M := by
    refine _root_.PresheafOfModules.hom_ext fun X => ?_
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x => ?_)
    have key : ∀ y : M.obj (op (F.obj X.unop)),
        M.map (F.map (adj.unit.app X.unop)).op (M.map (adj.counit.app (F.obj X.unop)).op y)
          = y := by
      intro y
      rw [← _root_.PresheafOfModules.map_comp_apply]
      have h : (adj.counit.app (F.obj X.unop)).op ≫ (F.map (adj.unit.app X.unop)).op = 𝟙 _ := by
        rw [← op_comp]; exact congrArg Quiver.Hom.op (adj.left_triangle_components X.unop)
      exact (M.congr_map_apply h y).trans
        (_root_.PresheafOfModules.map_id_apply M _ y)
    exact key x
  right_triangle_components N := by
    refine _root_.PresheafOfModules.hom_ext fun X => ?_
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x => ?_)
    have key : ∀ y : N.obj (op (G.obj X.unop)),
        N.map (adj.unit.app (G.obj X.unop)).op (N.map (G.map (adj.counit.app X.unop)).op y)
          = y := by
      intro y
      rw [← _root_.PresheafOfModules.map_comp_apply]
      have h : (G.map (adj.counit.app X.unop)).op ≫ (adj.unit.app (G.obj X.unop)).op = 𝟙 _ := by
        rw [← op_comp]; exact congrArg Quiver.Hom.op (adj.right_triangle_components X.unop)
      exact (N.congr_map_apply h y).trans
        (_root_.PresheafOfModules.map_id_apply N _ y)
    exact key x

/-- The unit of `pushforwardPushforwardAdj` is restriction along the counit of `F ⊣ G`. -/
theorem pushforwardPushforwardAdj_unit_app_app_apply (M : _root_.PresheafOfModules.{w} R)
    (X : Dᵒᵖ) (x : M.obj X) :
    ((pushforwardPushforwardAdj.{w} adj φ ψ H₁ H₂).unit.app M).app X x =
      M.map (adj.counit.app X.unop).op x := rfl

/-- The counit of `pushforwardPushforwardAdj` is restriction along the unit of `F ⊣ G`. -/
theorem pushforwardPushforwardAdj_counit_app_app_apply (N : _root_.PresheafOfModules.{w} S)
    (X : Cᵒᵖ) (x : N.obj (op (G.obj (F.obj X.unop)))) :
    ((pushforwardPushforwardAdj.{w} adj φ ψ H₁ H₂).counit.app N).app X x =
      N.map (adj.unit.app X.unop).op x := rfl

end Stacks.PresheafOfModules

end
