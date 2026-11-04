module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackTensorLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFourField

/-! # The canonical internal-Hom map for a localization -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.SheafOfModules.InternalHom

/-- Transporting the two factors of a bifunctor cancels an inverse in the second factor. -/
theorem bifunctor_transport_cancel {C D : Type*} [Category* C] [Category* D]
    (B : C ⥤ C ⥤ D) {A A' F F' : C} (a : A ⟶ A') (b : F ≅ F') :
    (B.obj A).map b.inv ≫ ((B.map a).app F ≫ (B.obj A').map b.hom) =
      (B.map a).app F' := by
  rw [← Category.assoc, (B.map a).naturality b.inv, Category.assoc,
    ← CategoryTheory.Functor.map_comp, b.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Cancel a prefix before specializing the category and its objects. -/
theorem comp_prefix_cancel_tail {C : Type*} [Category* C] {A B D E F : C}
    (a : A ⟶ B) (d : B ⟶ D) (s : A ⟶ D) (m : D ⟶ E) (n : E ⟶ F)
    (h : a ≫ d = s) : a ≫ ((d ≫ m) ≫ n) = s ≫ m ≫ n := by
  rw [Category.assoc d m n, ← Category.assoc a d, h]

universe u

section Comparison

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (O : Sheaf J CommRingCat.{u}) (O' : Sheaf K CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (P R : SheafOfModules.{u} (Tensor.ringSheaf O') ⥤
    SheafOfModules.{u} (Tensor.ringSheaf O)) (e : P ≅ R)
  (H F G : SheafOfModules.{u} (Tensor.ringSheaf O'))

/-- A tensor-compatible comparison with a functor commuting with internal Hom is invertible. -/
theorem isIso_internalHomComparison_of_iso
    (r : R.obj H ≅
      (internalHomSecondFunctor J O (R.obj F)).obj (R.obj G))
    (t : ((sheafTensor O').obj H).obj F ⟶ G)
    (m : ((sheafTensor O).obj (R.obj H)).obj
      (R.obj F) ⟶ R.obj (((sheafTensor O').obj
        H).obj F))
    (c : ((sheafTensor O).obj (P.obj H)).obj
      (P.obj F) ⟶ P.obj (((sheafTensor O').obj
        H).obj F))
    (d : ((sheafTensor O).obj (P.obj H)).obj
      (P.obj F) ⟶ ((sheafTensor O).obj
        (R.obj H)).obj (R.obj F))
    (α : P.obj H ⟶
      (internalHomSecondFunctor J O (P.obj F)).obj (P.obj G))
    (hα : tensorEvaluation O (P.obj F) (P.obj G) α =
      c ≫ P.map t)
    (hc : c ≫ e.hom.app (((sheafTensor O').obj
        H).obj F) =
      d ≫ m)
    (hd : ((sheafTensor O).obj (P.obj H)).map
        (e.inv.app F) ≫ d =
      ((sheafTensor O).map (e.hom.app H)).app
        (R.obj F))
    (hr : tensorEvaluation O (R.obj F) (R.obj G) r.hom =
      m ≫ R.map t) : IsIso α := by
  let β := α ≫ (internalHomPre O (e.inv.app F)).app (P.obj G) ≫
    (internalHomSecondFunctor J O (R.obj F)).map (e.hom.app G)
  have hβ : β = e.hom.app H ≫ r.hom := by
    apply tensorEvaluation_injective O (R.obj F) (R.obj G)
    dsimp only [β]
    rw [tensorEvaluation_comp_internalHomPre_comp_map, hα,
      tensorEvaluation_comp, hr, Category.assoc, e.hom.naturality, ← Category.assoc c, hc]
    exact comp_prefix_cancel_tail _ d _ m (R.map t) hd
  have : IsIso β := by
    rw [hβ]
    infer_instance
  exact IsIso.of_isIso_comp_right (g := α)
    (f := (internalHomPre O (e.inv.app F)).app (P.obj G) ≫
      (internalHomSecondFunctor J O (R.obj F)).map (e.hom.app G))

end Comparison

/-- The defining evaluation identity with its right side exposed before specializing `h`. -/
theorem tensorEvaluation_modulesPullbackInternalHomMap_explicit
    {X Y : RingedSite.{u, u, u}}
    (h : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
    (F G : SheafOfModules.{u} (Tensor.ringSheaf Y.O)) :
    Eq (tensorEvaluation X.O ((modulesPullback h).obj F) ((modulesPullback h).obj G)
        (modulesPullbackInternalHomMap h F G))
      ((pullbackTensorIso h).inv.app ((internalHomSecondFunctor Y.J Y.O F).obj G, F) ≫
        (modulesPullback h).map (internalHomEvaluation Y.O F G)) :=
  tensorEvaluation_modulesPullbackInternalHomMap h F G

/-- Apply the abstract comparison criterion while the morphism of ringed topoi is a variable.
The compatibility hypotheses retain the raw pullback spelling of the tensor comparison. -/
theorem isIso_modulesPullbackInternalHomMap_of_comparison
    {X Y : RingedSite.{u, u, u}}
    (h : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
    (R : SheafOfModules.{u} (Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Tensor.ringSheaf X.O)) (e : h.pullbackModules ≅ R)
    (H F G : SheafOfModules.{u} (Tensor.ringSheaf Y.O))
    (r : R.obj H ≅
      (internalHomSecondFunctor X.J X.O (R.obj F)).obj (R.obj G))
    (t : ((sheafTensor Y.O).obj H).obj F ⟶ G)
    (m : ((sheafTensor X.O).obj (R.obj H)).obj
      (R.obj F) ⟶ R.obj (((sheafTensor Y.O).obj
        H).obj F))
    (d : ((sheafTensor X.O).obj (h.pullbackModules.obj
        H)).obj (h.pullbackModules.obj F) ⟶
      ((sheafTensor X.O).obj (R.obj H)).obj
        (R.obj F))
    (α : (modulesPullback h).obj H ⟶
      (internalHomSecondFunctor X.J X.O ((modulesPullback h).obj F)).obj
        ((modulesPullback h).obj G))
    (hα : tensorEvaluation X.O ((modulesPullback h).obj F) ((modulesPullback h).obj G) α =
      (pullbackTensorIso h).inv.app (H, F) ≫ (modulesPullback h).map t)
    (hc : (pullbackTensorIso h).inv.app (H, F) ≫
        e.hom.app (((sheafTensor Y.O).obj H).obj F) =
      d ≫ m)
    (hd : ((sheafTensor X.O).obj (h.pullbackModules.obj
        H)).map (e.inv.app F) ≫ d =
      ((sheafTensor X.O).map (e.hom.app H)).app
        (R.obj F))
    (hr : tensorEvaluation X.O (R.obj F) (R.obj G) r.hom =
      m ≫ R.map t) : IsIso α :=
  isIso_internalHomComparison_of_iso X.O Y.O (modulesPullback h) R e H F G r t m
    ((pullbackTensorIso h).inv.app (H, F)) d α hα hc hd hr

section Localization

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F G : SheafOfModules.{u} (Tensor.ringSheaf X.O))

/-- The named two-factor tensor transport cancels an inverse in its second variable. -/
theorem tensorTransport_cancel_inverse
    (A : SheafOfModules.{u} (Tensor.ringSheaf X.O))
    {A' F' : SheafOfModules.{u} (Tensor.ringSheaf (X.O.over U))}
    (a : A' ⟶ A.over U) (b : F' ≅ F.over U) :
    ((sheafTensor (X.O.over U)).obj A').map b.inv ≫
        (tensorTransportFirst X U A a F' ≫ tensorTransportSecond X U A F b.hom) =
      ((sheafTensor (X.O.over U)).map a).app (F.over U) :=
  bifunctor_transport_cancel (sheafTensor (X.O.over U)) a b

/-- The localization comparison criterion with its tensor factors still independent. -/
theorem isIso_localization_internalHomComparison
    (H : SheafOfModules.{u} (Tensor.ringSheaf X.O))
    (r : H.over U ≅ (internalHomSecondFunctor (X.J.over U) (X.O.over U)
      (F.over U)).obj (G.over U))
    (t : ((sheafTensor X.O).obj H).obj F ⟶ G)
    (α : (modulesPullback (X.localizationMorphism U)).obj H ⟶
      (internalHomSecondFunctor (X.over U).J (X.over U).O
        ((modulesPullback (X.localizationMorphism U)).obj F)).obj
          ((modulesPullback (X.localizationMorphism U)).obj G))
    (hα : tensorEvaluation (X.over U).O
        ((modulesPullback (X.localizationMorphism U)).obj F)
        ((modulesPullback (X.localizationMorphism U)).obj G) α =
      (pullbackTensorIso (X.localizationMorphism U)).inv.app (H, F) ≫
        (modulesPullback (X.localizationMorphism U)).map t)
    (hr : tensorEvaluation (X.O.over U) (F.over U) (G.over U) r.hom =
      (ExtensionByZero.tensorRestrictionComparison X U F).natTrans.app H ≫
        (_root_.SheafOfModules.overFunctor (Tensor.ringSheaf X.O) U).map t) : IsIso α :=
  isIso_modulesPullbackInternalHomMap_of_comparison (X.localizationMorphism U)
    (_root_.SheafOfModules.overFunctor (Tensor.ringSheaf X.O) U)
    (X.localizationPullbackIsoRestriction U) H F G r t
    ((ExtensionByZero.tensorRestrictionComparison X U F).natTrans.app H)
    (tensorTransportFirst X U H
        ((X.localizationPullbackIsoRestriction U).hom.app H)
        ((X.localizationMorphism U).pullbackModules.obj F) ≫
      tensorTransportSecond X U H F
        ((X.localizationPullbackIsoRestriction U).hom.app F))
    α hα
    (localizationPullbackTensorIso_inv_app X U H F)
    (tensorTransport_cancel_inverse X U F H
      ((X.localizationPullbackIsoRestriction U).hom.app H)
      ((X.localizationPullbackIsoRestriction U).app F)) hr

/-- Read restriction evaluation at the component isomorphism without unfolding that iso. -/
theorem tensorEvaluation_internalHomRestrictionNatIso_app :
    tensorEvaluation (X.O.over U) (F.over U) (G.over U)
        (((ExtensionByZero.internalHomRestrictionNatIso X U F).app G).hom) =
      (ExtensionByZero.tensorRestrictionComparison X U F).natTrans.app
          ((internalHomSecondFunctor X.J X.O F).obj G) ≫
        (_root_.SheafOfModules.overFunctor (Tensor.ringSheaf X.O) U).map
          (internalHomEvaluation X.O F G) := by
  simpa only [Iso.app_hom] using
    ExtensionByZero.tensorEvaluation_internalHomRestrictionNatIso X U F G

/-- Localization commutes with internal Hom through the canonical pullback map. -/
theorem isIso_modulesPullbackInternalHomMap_localization :
    IsIso (modulesPullbackInternalHomMap (X.localizationMorphism U) F G) := by
  refine isIso_localization_internalHomComparison X U F G
    ((internalHomSecondFunctor X.J X.O F).obj G)
    ((ExtensionByZero.internalHomRestrictionNatIso X U F).app G)
    (internalHomEvaluation X.O F G)
    (modulesPullbackInternalHomMap (X.localizationMorphism U) F G)
    (tensorEvaluation_modulesPullbackInternalHomMap_explicit (X.localizationMorphism U) F G)
    ?_
  exact tensorEvaluation_internalHomRestrictionNatIso_app X U F G

/-- The same invertibility at the two-field presentation, by transport of a proposition. -/
theorem isIso_toposPullbackInternalHomMap_localization :
    IsIso (toposPullbackInternalHomMap (X.localizationRingedToposHom U) F G) :=
  isIso_modulesPullbackInternalHomMap_of_eq
    (X.localizationRingedToposHom U).toModulesHom F G
    (X.toModulesHom_localizationRingedToposHom U)
    (isIso_modulesPullbackInternalHomMap_localization X U F G)

end Localization

end Stacks.SheafOfModules.InternalHom

end
