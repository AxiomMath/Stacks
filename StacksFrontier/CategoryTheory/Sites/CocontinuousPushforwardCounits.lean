module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.PresheafComp
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanBaseChange

/-!
# The cocontinuous pushforward of sheaves, read against the counits of the Kan extensions

For a functor of sites `G : (C, J) ⥤ (D, K)` which is continuous and cocontinuous, the direct
image `G.sheafPushforwardCocontinuous` is, on underlying presheaves, the right Kan extension
`G.op.ran`, and `CategoryTheory.Functor.sheafAdjunctionCocontinuous` is the right Kan extension
adjunction restricted to sheaves.  A right Kan extension is determined by its counit, so every
canonical map built from these adjunctions is pinned down by what it does against the counits.
This file records the two such computations the composition functoriality of a direct image needs,
and the extensionality principle they are consumed through.

## Main results

* `CategoryTheory.Functor.ran_comp_obj_obj_hom_ext` — **two nested right Kan extensions are
  determined, at an object, by the composites of their two counits.**  Two maps into
  `Ran_{L'}(Ran_L P)` read at an object `Y` agree as soon as they agree after restricting along
  each morphism `Y ⟶ L'(L c)` and taking the counit of `Ran_{L'}` and then that of `Ran_L`.  This
  is `CategoryTheory.Functor.ran_obj_obj_hom_ext` for the single right Kan extension along
  `L ⋙ L'` carried across `CategoryTheory.Functor.ranCompIsoOfAdjunctions`.
* `CategoryTheory.Functor.sheafAdjunctionCocontinuous_unit_app_hom_app_comp_ranCounit` — **the
  unit of `π_* ⊣ i_*`, read at an object in the image of the functor of sites and followed by the
  counit, is the identity.**  This is the triangle identity of the right Kan extension
  adjunction, transported to sheaves.
* `CategoryTheory.Functor`
  `.rightAdjointUniq_sheafAdjunctionCocontinuous_inv_app_hom_app_comp_ranCounit`
  — **the comparison of the two cocontinuous pushforwards attached to a factorization
  `F ⋙ G ≅ FG`, read against the counits.**  The comparison runs from the direct image along `FG`
  to the composite of those along `F` and along `G`, and following it with the `2`-cell of the
  factorization and the two counits gives back the counit of the single right Kan extension along
  `FG`.  Both sides are right adjoints of one and the same restriction functor and the comparison
  is `CategoryTheory.Adjunction.rightAdjointUniq`, whose behaviour on counits is
  `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`.

## References

* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace Functor

section Nested

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {H : Type w} [Category.{w'} H]

/-- **Two maps into a pair of nested right Kan extensions, read at an object, agree as soon as
they agree against the two counits.**

The composite `Ran_{L'} ∘ Ran_L` is a right Kan extension along `L ⋙ L'`, by
`CategoryTheory.Functor.ranCompIsoOfAdjunctions`, and that comparison takes the composite of the
two counits to the counit of the single extension,
`CategoryTheory.Functor.ranCompIso_inv_app_app_comp_ranCounit`; so this is
`CategoryTheory.Functor.ran_obj_obj_hom_ext` for `L ⋙ L'`. -/
theorem ran_comp_obj_obj_hom_ext (L : C₁ ⥤ C₂) (L' : C₂ ⥤ C₃)
    [∀ P : C₁ ⥤ H, L.HasRightKanExtension P] [∀ P : C₂ ⥤ H, L'.HasRightKanExtension P]
    (P : C₁ ⥤ H) [(L ⋙ L').HasPointwiseRightKanExtension P] (Y : C₃) {Z : H}
    {f g : Z ⟶ (L'.ran.obj (L.ran.obj P)).obj Y}
    (h : ∀ d : StructuredArrow Y (L ⋙ L'),
      f ≫ (L'.ran.obj (L.ran.obj P)).map d.hom ≫
          (L'.ranCounit.app (L.ran.obj P)).app (L.obj d.right) ≫
            (L.ranCounit.app P).app d.right =
        g ≫ (L'.ran.obj (L.ran.obj P)).map d.hom ≫
          (L'.ranCounit.app (L.ran.obj P)).app (L.obj d.right) ≫
            (L.ranCounit.app P).app d.right) :
    f = g := by
  have : IsIso (ranCompIsoOfAdjunctions H L L').inv := Iso.isIso_inv _
  have : IsIso ((ranCompIsoOfAdjunctions H L L').inv.app P) := NatIso.isIso_app_of_isIso _ _
  have : IsIso (((ranCompIsoOfAdjunctions H L L').inv.app P).app Y) :=
    NatIso.isIso_app_of_isIso _ _
  rw [← cancel_mono (((ranCompIsoOfAdjunctions H L L').inv.app P).app Y)]
  refine ran_obj_obj_hom_ext (L ⋙ L') P Y fun d ↦ ?_
  have hnat : ((ranCompIsoOfAdjunctions H L L').inv.app P).app Y ≫
        ((L ⋙ L').ran.obj P).map d.hom =
      (L'.ran.obj (L.ran.obj P)).map d.hom ≫
        ((ranCompIsoOfAdjunctions H L L').inv.app P).app ((L ⋙ L').obj d.right) :=
    (((ranCompIsoOfAdjunctions H L L').inv.app P).naturality d.hom).symm
  have hc := ranCompIso_inv_app_app_comp_ranCounit H L L' P d.right
  have key : ∀ z : Z ⟶ (L'.ran.obj (L.ran.obj P)).obj Y,
      (z ≫ ((ranCompIsoOfAdjunctions H L L').inv.app P).app Y) ≫
          ((L ⋙ L').ran.obj P).map d.hom ≫ ((L ⋙ L').ranCounit.app P).app d.right =
        z ≫ (L'.ran.obj (L.ran.obj P)).map d.hom ≫
          (L'.ranCounit.app (L.ran.obj P)).app (L.obj d.right) ≫
            (L.ranCounit.app P).app d.right := by
    intro z
    rw [Category.assoc, ← Category.assoc (((ranCompIsoOfAdjunctions H L L').inv.app P).app Y),
      hnat, Category.assoc, hc]
  rw [key f, key g]
  exact h d

end Nested

section Sites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {A : Type w} [Category.{w'} A]

section Unit

variable (ι : C ⥤ D) (A) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [ι.IsCocontinuous J K] [ι.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, ι.op.HasPointwiseRightKanExtension P]

/-- **The unit of the adjunction between restriction and the cocontinuous pushforward, read at an
object in the image of the functor of sites and followed by the counit of the right Kan extension,
is the identity.**

On underlying presheaves the adjunction is the right Kan extension adjunction, by
`CategoryTheory.Functor.sheafAdjunctionCocontinuous_unit_app_hom`, so this is its triangle
identity `CategoryTheory.Functor.ranCounit_app_app_ranAdjunction_unit_app_app`. -/
theorem sheafAdjunctionCocontinuous_unit_app_hom_app_comp_ranCounit
    (W : Sheaf K A) (X : Cᵒᵖ) :
    ((ι.sheafAdjunctionCocontinuous A J K).unit.app W).hom.app (ι.op.obj X) ≫
        (ι.op.ranCounit.app (ι.op ⋙ W.obj)).app X =
      𝟙 (W.obj.obj (ι.op.obj X)) := by
  rw [ι.sheafAdjunctionCocontinuous_unit_app_hom A J K W]
  exact ι.op.ranCounit_app_app_ranAdjunction_unit_app_app W.obj X

end Unit

section Comp

variable {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (e : F ⋙ G ≅ FG)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]
  [F.IsCocontinuous J K] [G.IsCocontinuous K L] [FG.IsCocontinuous J L]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
  [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, FG.op.HasPointwiseRightKanExtension P]

/-- **The comparison of the cocontinuous pushforward along `FG` with the composite of those along
`F` and along `G`, read against the counits.**

The comparison is the canonical isomorphism of two right adjoints of one and the same restriction
functor, so `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit` identifies it by what it
does to the counits: following its inverse with the `2`-cell of the factorization `F ⋙ G ≅ FG` and
then the counit of the right Kan extension along `G` and that along `F` gives back the counit of
the right Kan extension along `FG`.  The counit of the composite adjunction is the composite of
the two counits, `CategoryTheory.Adjunction.comp_counit_app`, and that of each cocontinuous
pushforward adjunction is the corresponding Kan extension counit,
`CategoryTheory.Functor.sheafAdjunctionCocontinuous_counit_app_hom`. -/
theorem rightAdjointUniq_sheafAdjunctionCocontinuous_inv_app_hom_app_comp_ranCounit
    (W : Sheaf J A) (X : Cᵒᵖ) :
    ((Adjunction.rightAdjointUniq
            (Adjunction.ofNatIsoLeft
              ((G.sheafAdjunctionCocontinuous A K L).comp (F.sheafAdjunctionCocontinuous A J K))
              (Functor.sheafPushforwardContinuousComp' (A := A) e J K L))
            (FG.sheafAdjunctionCocontinuous A J L)).inv.app W).hom.app (FG.op.obj X) ≫
        (G.op.ran.obj (F.op.ran.obj W.obj)).map (e.hom.app X.unop).op ≫
          (G.op.ranCounit.app (F.op.ran.obj W.obj)).app (F.op.obj X) ≫
            (F.op.ranCounit.app W.obj).app X =
      (FG.op.ranCounit.app W.obj).app X := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (FG.sheafAdjunctionCocontinuous A J L)
    (Adjunction.ofNatIsoLeft
      ((G.sheafAdjunctionCocontinuous A K L).comp (F.sheafAdjunctionCocontinuous A J K))
      (Functor.sheafPushforwardContinuousComp' (A := A) e J K L)) W
  have h2 : (FG.sheafPushforwardContinuous A J L).map
        ((Adjunction.rightAdjointUniq (FG.sheafAdjunctionCocontinuous A J L)
          (Adjunction.ofNatIsoLeft
            ((G.sheafAdjunctionCocontinuous A K L).comp (F.sheafAdjunctionCocontinuous A J K))
            (Functor.sheafPushforwardContinuousComp' (A := A) e J K L))).hom.app W) ≫
      (Functor.sheafPushforwardContinuousComp' (A := A) e J K L).inv.app
          ((G.sheafPushforwardCocontinuous A K L).obj
            ((F.sheafPushforwardCocontinuous A J K).obj W)) ≫
        (F.sheafPushforwardContinuous A J K).map
            ((G.sheafAdjunctionCocontinuous A K L).counit.app
              ((F.sheafPushforwardCocontinuous A J K).obj W)) ≫
          (F.sheafAdjunctionCocontinuous A J K).counit.app W =
      (FG.sheafAdjunctionCocontinuous A J L).counit.app W := by
    simpa only [Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc] using h
  have hcomp := NatTrans.congr_app ((sheafToPresheaf J A).congr_map h2) X
  have h3 : ((Adjunction.rightAdjointUniq (FG.sheafAdjunctionCocontinuous A J L)
            (Adjunction.ofNatIsoLeft
              ((G.sheafAdjunctionCocontinuous A K L).comp (F.sheafAdjunctionCocontinuous A J K))
              (Functor.sheafPushforwardContinuousComp' (A := A) e J K L))).hom.app W).hom.app
          (FG.op.obj X) ≫
      ((G.op.ran.obj (F.op.ran.obj W.obj)).map (e.hom.app X.unop).op ≫ 𝟙 _) ≫
        ((G.sheafAdjunctionCocontinuous A K L).counit.app
            ((F.sheafPushforwardCocontinuous A J K).obj W)).hom.app (F.op.obj X) ≫
          ((F.sheafAdjunctionCocontinuous A J K).counit.app W).hom.app X =
      ((FG.sheafAdjunctionCocontinuous A J L).counit.app W).hom.app X := hcomp
  have hGc : ((G.sheafAdjunctionCocontinuous A K L).counit.app
        ((F.sheafPushforwardCocontinuous A J K).obj W)).hom.app (F.op.obj X) =
      (G.op.ranCounit.app (F.op.ran.obj W.obj)).app (F.op.obj X) :=
    (NatTrans.congr_app (G.sheafAdjunctionCocontinuous_counit_app_hom A K L
        ((F.sheafPushforwardCocontinuous A J K).obj W)) (F.op.obj X)).trans
      (NatTrans.congr_app (NatTrans.congr_app (Functor.ranAdjunction_counit G.op A)
        (F.op.ran.obj W.obj)) (F.op.obj X))
  have hFc : ((F.sheafAdjunctionCocontinuous A J K).counit.app W).hom.app X =
      (F.op.ranCounit.app W.obj).app X :=
    (NatTrans.congr_app (F.sheafAdjunctionCocontinuous_counit_app_hom A J K W) X).trans
      (NatTrans.congr_app (NatTrans.congr_app (Functor.ranAdjunction_counit F.op A) W.obj) X)
  have hFGc : ((FG.sheafAdjunctionCocontinuous A J L).counit.app W).hom.app X =
      (FG.op.ranCounit.app W.obj).app X :=
    (NatTrans.congr_app (FG.sheafAdjunctionCocontinuous_counit_app_hom A J L W) X).trans
      (NatTrans.congr_app (NatTrans.congr_app (Functor.ranAdjunction_counit FG.op A) W.obj) X)
  rw [Adjunction.rightAdjointUniq_inv_app, ← hGc, ← hFc, ← hFGc,
    ← Category.comp_id ((G.op.ran.obj (F.op.ran.obj W.obj)).map (e.hom.app X.unop).op)]
  exact h3

end Comp

end Sites

end Functor

end CategoryTheory

end
