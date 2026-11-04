module

public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison

/-!
# Sheaf pullback as pullback followed by a direct image, at arbitrary coefficients

Let `a : C ⥤ D`, `i : D ⥤ E` and `j : C ⥤ E` be functors of sites, with `i` cocontinuous, and
`ε : a ⋙ i ⟶ j` a natural transformation whose components are initial among the structured
arrows over `i.op`. Then the sheaf pullback along `a` is the pullback along `j` followed by the
direct image along `i`. This file proves this for sheaves with values in an arbitrary category
`A`, generalizing the statements for sheaves of sets of
`StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison`.

## Main definitions

* `CategoryTheory.sheafPushforwardRanComparisonValued` — the comparison
  `i^{cocont}_* ⋙ j_* ⟶ a_*` of direct images induced by `ε`.
* `CategoryTheory.sheafPullbackIsoOfInitialValued` — the isomorphism `a⁻¹ ≅ P ⋙ i_*`, for a left
  adjoint `P` of `j_*`.

## Main results

* `CategoryTheory.sheafPushforwardRanComparisonValued_isIso` — the comparison is invertible when
  the components of `ε` are initial.
* `CategoryTheory.sheafPullbackIsoOfInitialValued_unit` — the equation pinning down
  `CategoryTheory.sheafPullbackIsoOfInitialValued` through the units of the two adjunctions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₅ u₁ u₂ u₃ u₅

namespace CategoryTheory

section Canonical

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {A : Type u₅} [Category.{v₅} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (i : D ⥤ E) (j : C ⥤ E)
  [a.IsContinuous J K] [i.IsContinuous K L] [j.IsContinuous J L]
  [i.IsCocontinuous K L]
  [∀ F : Dᵒᵖ ⥤ A, i.op.HasPointwiseRightKanExtension F]
  (ε : a ⋙ i ⟶ j)

/-- The comparison of the composite of the cocontinuous direct image along `i` with the
continuous direct image along `j` with the continuous direct image along `a`, induced by a
natural transformation `ε : a ⋙ i ⟶ j`, for sheaves with values in `A`. -/
public def sheafPushforwardRanComparisonValued :
    i.sheafPushforwardCocontinuous A K L ⋙
        j.sheafPushforwardContinuous A J L ⟶
      a.sheafPushforwardContinuous A J K where
  app G := ⟨{
    app U := ((i.sheafPushforwardCocontinuous A K L).obj G).obj.map
      (ε.app U.unop).op ≫ (i.op.ranCounit.app G.obj).app (a.op.obj U)
    naturality := by
      intro U V f
      change (i.op.ran.obj G.obj).map (j.op.map f) ≫
          (i.op.ran.obj G.obj).map (ε.app V.unop).op ≫
            (i.op.ranCounit.app G.obj).app (a.op.obj V) =
        ((i.op.ran.obj G.obj).map (ε.app U.unop).op ≫
          (i.op.ranCounit.app G.obj).app (a.op.obj U)) ≫ G.obj.map (a.op.map f)
      have hn := (i.op.ranCounit.app G.obj).naturality (a.op.map f)
      dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        Functor.whiskeringLeft_obj_obj] at hn
      rw [Category.assoc, ← hn,
        ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      congr 2
      exact congrArg Quiver.Hom.op (ε.naturality f.unop).symm }⟩
  naturality := by
    intro G H f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (i.op.ran.map f.hom).app (j.op.obj U) ≫
        ((i.op.ran.obj H.obj).map (ε.app U.unop).op ≫
          (i.op.ranCounit.app H.obj).app (a.op.obj U)) =
      ((i.op.ran.obj G.obj).map (ε.app U.unop).op ≫
        (i.op.ranCounit.app G.obj).app (a.op.obj U)) ≫ f.hom.app (a.op.obj U)
    rw [← Category.assoc, ← NatTrans.naturality, Category.assoc, Category.assoc]
    congr 1
    exact NatTrans.congr_app (i.op.ranCounit.naturality f.hom) (a.op.obj U)

omit [i.IsContinuous K L] in
/-- If each comparison arrow `ε.app U` is initial among the structured arrows over `i.op`, then
the Kan extension comparison `sheafPushforwardRanComparisonValued` is an isomorphism. -/
public lemma sheafPushforwardRanComparisonValued_isIso
    (hε : ∀ U : C, IsInitial (StructuredArrow.mk (T := i.op) ((ε.app U).op))) :
    IsIso (sheafPushforwardRanComparisonValued (A := A) J K L a i j ε) := by
  have hG (G : Sheaf K A) :
      IsIso ((sheafPushforwardRanComparisonValued (A := A) J K L a i j ε).app G) := by
    have hU (U : Cᵒᵖ) :
        IsIso (((sheafPushforwardRanComparisonValued (A := A) J K L a i j ε).app G).hom.app U) :=
      (i.op.isPointwiseRightKanExtensionRanCounit G.obj
          (j.op.obj U)).isIso_π_app_of_isInitial
        (StructuredArrow.mk (T := i.op) ((ε.app U.unop).op)) (hε U.unop)
    have : IsIso ((sheafToPresheaf J A).map
        ((sheafPushforwardRanComparisonValued (A := A) J K L a i j ε).app G)) :=
      NatIso.isIso_of_isIso_app
        ((sheafPushforwardRanComparisonValued (A := A) J K L a i j ε).app G).hom
    exact isIso_of_reflects_iso
      ((sheafPushforwardRanComparisonValued (A := A) J K L a i j ε).app G) (sheafToPresheaf J A)
  exact NatIso.isIso_of_isIso_app _

variable (P : Sheaf J A ⥤ Sheaf L A)
  (adjP : P ⊣ j.sheafPushforwardContinuous A J L)
  [(a.sheafPushforwardContinuous A J K).IsRightAdjoint]
  (hε : ∀ U : C, IsInitial (StructuredArrow.mk (T := i.op) ((ε.app U).op)))

/-- Under the initiality hypothesis of `sheafPushforwardRanComparisonValued_isIso`, the sheaf
pullback along `a` is the pullback along `j` followed by the direct image along `i`, for sheaves
with values in `A`. -/
public def sheafPullbackIsoOfInitialValued :
    a.sheafPullback A J K ≅ P ⋙ i.sheafPushforwardContinuous A K L := by
  letI := sheafPushforwardRanComparisonValued_isIso (A := A) J K L a i j ε hε
  exact Adjunction.leftAdjointUniq (a.sheafAdjunctionContinuous A J K)
    ((adjP.comp (i.sheafAdjunctionCocontinuous A K L)).ofNatIsoRight
      (asIso (sheafPushforwardRanComparisonValued (A := A) J K L a i j ε)))

/-- The unit of the right Kan extension adjunction, followed by restriction along an arrow in
the image of `i.op` and the Kan extension counit, is restriction along that arrow, for presheaves
with values in `A`. -/
public lemma ran_unit_map_ranCounit_valued (i : D ⥤ E)
    [∀ F : Dᵒᵖ ⥤ A, i.op.HasPointwiseRightKanExtension F]
    (G : Eᵒᵖ ⥤ A) {X : Eᵒᵖ} {Y : Dᵒᵖ} (f : X ⟶ i.op.obj Y) :
    ((i.op.ranAdjunction A).unit.app G).app X ≫
        (i.op.ran.obj (i.op ⋙ G)).map f ≫ (i.op.ranCounit.app (i.op ⋙ G)).app Y =
      G.map f := by
  have hn := ((i.op.ranAdjunction A).unit.app G).naturality f
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at hn
  rw [← Category.assoc, ← hn, Category.assoc,
    Functor.ranCounit_app_app_ranAdjunction_unit_app_app]
  exact Category.comp_id _

/-- The equation pinning down `sheafPullbackIsoOfInitialValued`: it carries the unit of the
adjunction for `a` to the unit of the adjunction for `P`, followed by restriction along
`ε`. -/
public lemma sheafPullbackIsoOfInitialValued_unit (F : Sheaf J A) (U : Cᵒᵖ) :
    ((a.sheafAdjunctionContinuous A J K).unit.app F).hom.app U ≫
        ((sheafPullbackIsoOfInitialValued J K L a i j ε P adjP hε).hom.app F).hom.app
          (a.op.obj U) =
      (adjP.unit.app F).hom.app U ≫ (P.obj F).obj.map (ε.app U.unop).op := by
  let := sheafPushforwardRanComparisonValued_isIso (A := A) J K L a i j ε hε
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (a.sheafAdjunctionContinuous A J K)
    ((adjP.comp (i.sheafAdjunctionCocontinuous A K L)).ofNatIsoRight
      (asIso (sheafPushforwardRanComparisonValued (A := A) J K L a i j ε))) F
  have h' := congrArg (fun t => t.hom.app U) h
  refine h'.trans ?_
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.whiskerLeft_app,
    asIso_hom, sheafPushforwardRanComparisonValued, Category.assoc]
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom]
  change (adjP.unit.app F).hom.app U ≫
      ((i.op.ranAdjunction A).unit.app (P.obj F).obj).app (j.op.obj U) ≫
        (i.op.ran.obj (i.op ⋙ (P.obj F).obj)).map (ε.app U.unop).op ≫
          (i.op.ranCounit.app (i.op ⋙ (P.obj F).obj)).app (a.op.obj U) = _
  congr 1
  exact ran_unit_map_ranCounit_valued i (P.obj F).obj (ε.app U.unop).op

end Canonical

end CategoryTheory

end
