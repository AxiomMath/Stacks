module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint

/-! # The stalk of a representable presheaf at a point

A point of a site given by a functor `p : C ⥤ Type u` computes the stalk of a presheaf `F` as the
colimit of `F` over the opposite of the category of elements of `p`. This file shows that the
stalk of the representable presheaf `h_U` is `p U`, naturally in `U`.

## Main results

* `Phi_bijective`: `Φ_U : p U ⟶ (h_U)_p` is bijective, so `(h_U)_p ≅ p U`
  (Stacks 00Y6, isomorphism).
* `Phi_naturality`: `Φ` is natural in `U` (Stacks 00Y6, functoriality).

Tags covered: 00Y6.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open PresheafPushforwardStalkAdjunction

universe u

variable {C : Type u} [SmallCategory C]

/-- Cocone compatibility: a morphism `φ : Vy ⟶ Vy'` in `p.Elements` lets us
absorb `φ.hom` into the representable section. -/
lemma colimit_ι_yoneda_compatible (p : C ⥤ Type u) (U : C) (Vy Vy' : p.Elements)
    (φ : Vy ⟶ Vy') (f : Vy'.obj ⟶ U) :
    colimit.ι ((Functor.Elements.π p).op ⋙ yoneda.obj U) (op Vy) (φ.hom ≫ f) =
      colimit.ι ((Functor.Elements.π p).op ⋙ yoneda.obj U) (op Vy') f :=
  ConcreteCategory.congr_hom
    (colimit.w ((Functor.Elements.π p).op ⋙ yoneda.obj U) (op φ : op Vy' ⟶ op Vy)) f

/-- **Stacks 00Y6.** The canonical map `Φ_U : p U ⟶ (h_U)_p` from the value of the point at `U`
to the stalk of the representable presheaf `h_U` is bijective. -/
@[stacks 00Y6 "isomorphism"]
theorem Phi_bijective (p : C ⥤ Type u) (U : C) :
    Function.Bijective (theta p U) :=
  ⟨Function.LeftInverse.injective (thetaInv_theta p U),
   Function.RightInverse.surjective (theta_thetaInv p U)⟩

/-- **Stacks 00Y6.** The maps `Φ_U` are natural in `U`: they commute with `p.map g` on the source
and with the stalk of `yoneda.map g` on the target. -/
@[stacks 00Y6 "functoriality"]
theorem Phi_naturality (p : C ⥤ Type u) {U U' : C} (g : U ⟶ U') (x : p.obj U) :
    theta p U' (p.map g x) = (presheafStalk p).map (yoneda.map g) (theta p U x) := by
  unfold theta stalkMk
  rw [presheafStalk_map_ι_apply, show (yoneda.map g).app (op U) (𝟙 U) = g by simp]
  have h := colimit_ι_yoneda_compatible p U' (⟨x⟩ : p.Elements)
    (⟨p.map g x⟩ : p.Elements) ⟨g, rfl⟩ (𝟙 U')
  exact h.symm.trans
    (ConcreteCategory.congr_arg
      (colimit.ι ((Functor.Elements.π p).op ⋙ yoneda.obj U') (op ⟨x⟩))
      (Category.comp_id _))
