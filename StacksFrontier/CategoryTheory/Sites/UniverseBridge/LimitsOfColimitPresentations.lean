module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-! # Transporting limit preservation through colimit presentations -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.UniverseBridge

/-- A natural transformation between colimit-preserving functors is invertible at a
colimit if it is invertible on every object in the presenting diagram. -/
theorem isIso_app_of_isColimit
    {A B I : Type*} [Category* A] [Category* B] [Category* I]
    {P Q : A ⥤ B} (α : P ⟶ Q) (E : I ⥤ A) (c : Cocone E) (hc : IsColimit c)
    [PreservesColimit E P] [PreservesColimit E Q]
    (h : ∀ i, IsIso (α.app (E.obj i))) : IsIso (α.app c.pt) := by
  have : IsIso (Functor.whiskerLeft E α) := NatTrans.isIso_iff_isIso_app _ |>.mpr h
  let e := asIso (Functor.whiskerLeft E α)
  let t : P.mapCocone c ⟶ (Cocone.precompose e.hom).obj (Q.mapCocone c) :=
    { hom := α.app c.pt
      w := fun i ↦ α.naturality (c.ι.app i) }
  have : IsIso t := (isColimitOfPreserves P hc).hom_isIso
    ((IsColimit.precomposeHomEquiv e (Q.mapCocone c)).symm
      (isColimitOfPreserves Q hc)) t
  exact (Cocone.forget (E ⋙ P)).map_isIso t

/-- The limit comparison, natural in the diagram. -/
def limitPostNatTrans {A B K : Type*} [Category* A] [Category* B] [Category* K]
    [HasLimitsOfShape K A] [HasLimitsOfShape K B] (F : A ⥤ B) :
    (lim : (K ⥤ A) ⥤ A) ⋙ F ⟶
      (Functor.whiskeringRight K A B).obj F ⋙ lim where
  app D := limit.post D F
  naturality {D _} a := limit.map_post (F := D) (α := a) F

/-- Limit preservation passes from the pieces of a colimit presentation to its colimit,
provided the two limit-comparison functors preserve that presenting colimit. -/
theorem preservesLimit_of_isColimit
    {A B K I : Type*} [Category* A] [Category* B] [Category* K] [Category* I]
    [HasLimitsOfShape K A] [HasLimitsOfShape K B]
    (F : A ⥤ B) (E : I ⥤ (K ⥤ A)) (c : Cocone E) (hc : IsColimit c)
    [PreservesColimit E ((lim : (K ⥤ A) ⥤ A) ⋙ F)]
    [PreservesColimit E ((Functor.whiskeringRight K A B).obj F ⋙ lim)]
    (h : ∀ i, PreservesLimit (E.obj i) F) : PreservesLimit c.pt F := by
  have : IsIso (limit.post c.pt F) :=
    isIso_app_of_isColimit (limitPostNatTrans F) E c hc fun i ↦ by
      have := h i
      change IsIso (limit.post (E.obj i) F)
      infer_instance
  exact preservesLimit_of_isIso_post (F := c.pt) (G := F)

/-- If `Q` and `Q ⋙ F` preserve a limit, `F` preserves its image under `Q`. -/
theorem preservesLimit_image_of_comp
    {A B C K : Type*} [Category* A] [Category* B] [Category* C] [Category* K]
    (Q : A ⥤ B) (F : B ⥤ C) (D : K ⥤ A) [HasLimit D]
    [PreservesLimit D Q] [PreservesLimit D (Q ⋙ F)] : PreservesLimit (D ⋙ Q) F :=
  preservesLimit_of_preserves_limit_cone (isLimitOfPreserves Q (limit.isLimit D))
    (isLimitOfPreserves (Q ⋙ F) (limit.isLimit D))

/-- Commutation of the colimit functor with limits also expresses commutation of the
limit functor with those colimits. -/
theorem preservesColimitsOfShape_lim_of_colim
    {A K I : Type*} [Category* A] [Category* K] [Category* I]
    [HasLimitsOfShape K A] [HasColimitsOfShape I A]
    [PreservesLimitsOfShape K (colim : (I ⥤ A) ⥤ A)] :
    PreservesColimitsOfShape I (lim : (K ⥤ A) ⥤ A) := by
  refine ⟨fun {E} ↦ ?_⟩
  let e : colimit (E ⋙ lim) ≅ limit (colimit E) :=
    HasColimit.isoOfNatIso (limitFlipIsoCompLim E).symm ≪≫ colimitLimitIso E.flip
  have he : colimit.post E (lim : (K ⥤ A) ⥤ A) = e.hom := by
    refine colimit.hom_ext fun i ↦ limit.hom_ext fun k ↦ ?_
    simp only [Functor.comp_obj, lim_obj, colimit.ι_post, lim_map, limMap_π, limitFlipIsoCompLim,
      Iso.trans_hom, HasColimit.isoOfNatIso_ι_hom_assoc, Iso.symm_hom,
      NatIso.ofComponents_inv_app, Iso.trans_inv, Category.assoc, e]
    have hi := ι_colimitLimitIso_limit_π E.flip i k
    change colimit.ι (limit E.flip) i ≫ (colimitLimitIso E.flip).hom ≫
      limit.π (colimit E) k =
      (limit.π E.flip k).app i ≫ (colimit.ι E i).app k at hi
    rw [hi]
    simp
  have : IsIso (colimit.post E (lim : (K ⥤ A) ⥤ A)) := he ▸ inferInstance
  exact preservesColimit_of_isIso_post (F := E) (G := lim)

end Stacks.Sites.UniverseBridge

end
