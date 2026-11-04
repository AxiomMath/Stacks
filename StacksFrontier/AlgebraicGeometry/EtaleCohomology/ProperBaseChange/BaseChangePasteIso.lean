module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition

/-!
# Invertibility of the base change map of a pasted square

If the étale base change maps of the two squares of a pasting are isomorphisms, so is the base
change map of the outer rectangle: by `Stacks.EtaleCohomology.etaleAbelianBaseChange_comp_app` it
is a composite of the two, whiskered by inverse-image composition isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

/-- Given the upper square's base change is invertible, the outer base change map at `K` is
invertible iff the inverse image along `i` of the lower square's one is. -/
private theorem isIso_app_etaleAbelianBaseChange_iff_of_paste {S T W X Y Z : Scheme.{u}} (f : X ⟶ S)
    (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i) (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T)
    (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (h₂ : IsIso (etaleAbelianBaseChange.{u, v} h i k j sq₂))
    (K : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleAbelianBaseChange.{u, v} g a b j hyp).app K) ↔
      IsIso ((etaleAbelianInverseImage.{u, v} i).map
        ((etaleAbelianBaseChange.{u, v} g f e h sq₁).app K)) := by
  have i₂ : IsIso ((etaleAbelianBaseChange.{u, v} h i k j sq₂).app
      ((etaleAbelianInverseImage.{u, v} e).obj K)) := NatIso.isIso_app_of_isIso _ _
  have i₃ : IsIso ((etaleAbelianDirectImage.{u, v} j).map
      ((etaleAbelianInverseImageCompIso'.{u, v} k e b hb).inv.app K)) := Functor.map_isIso _ _
  rw [etaleAbelianBaseChange_comp_app.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp K,
    isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Base change maps compose along a pasted square.** If the base change maps of the lower and
upper squares of a pasting of two commutative squares are isomorphisms, so is the base change map
of the outer rectangle (`Stacks.EtaleCohomology.etaleAbelianBaseChange_comp_app`). -/
theorem isIso_etaleAbelianBaseChange_of_paste {S T W X Y Z : Scheme.{u}} (f : X ⟶ S)
    (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i) (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T)
    (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (h₁ : IsIso (etaleAbelianBaseChange.{u, v} g f e h sq₁))
    (h₂ : IsIso (etaleAbelianBaseChange.{u, v} h i k j sq₂)) :
    IsIso (etaleAbelianBaseChange.{u, v} g a b j hyp) :=
  (NatTrans.isIso_iff_isIso_app _).2 fun K ↦
    (isIso_app_etaleAbelianBaseChange_iff_of_paste.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp
      h₂ K).2 (Functor.map_isIso _ _)

/-- **Cancelling the upper square of a pasting.** If the base change maps of the outer rectangle
and of the upper square of a pasting are isomorphisms, then the inverse image along `i` of the base
change map of the lower square is an isomorphism at every sheaf. -/
theorem isIso_inverseImage_map_etaleAbelianBaseChange_app_of_paste {S T W X Y Z : Scheme.{u}}
    (f : X ⟶ S)
    (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i) (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T)
    (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (hO : IsIso (etaleAbelianBaseChange.{u, v} g a b j hyp))
    (h₂ : IsIso (etaleAbelianBaseChange.{u, v} h i k j sq₂))
    (K : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleAbelianInverseImage.{u, v} i).map
      ((etaleAbelianBaseChange.{u, v} g f e h sq₁).app K)) :=
  (isIso_app_etaleAbelianBaseChange_iff_of_paste.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp
    h₂ K).1 inferInstance

/-- **Base change maps compose along a pasted square, with the lower square only invertible
after inverse image.** If the inverse image along `i` of the base change map of the lower square is
an isomorphism at every sheaf and the base change map of the upper square is an isomorphism, then
the base change map of the outer rectangle is an isomorphism. -/
theorem isIso_etaleAbelianBaseChange_of_paste_of_isIso_inverseImage {S T W X Y Z : Scheme.{u}}
    (f : X ⟶ S)
    (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i) (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T)
    (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    (h₁ : ∀ K : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      IsIso ((etaleAbelianInverseImage.{u, v} i).map
        ((etaleAbelianBaseChange.{u, v} g f e h sq₁).app K)))
    (h₂ : IsIso (etaleAbelianBaseChange.{u, v} h i k j sq₂)) :
    IsIso (etaleAbelianBaseChange.{u, v} g a b j hyp) :=
  (NatTrans.isIso_iff_isIso_app _).2 fun K ↦
    (isIso_app_etaleAbelianBaseChange_iff_of_paste.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp
      h₂ K).2 (h₁ K)

end Stacks.EtaleCohomology

end
