module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorIsoTransport
public import StacksFrontier.CategoryTheory.Sites.SheafSectionsPairing

/-!
# The comparison of Stacks 03EL on local sections

For a morphism of ringed topoi `f`, the inverse of the comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of
Stacks 03EL sends the sheafified pure tensor of two units of Tag 03CZ to the unit of the canonical
pairing. This file records that formula, its reading through an isomorphism `f^* ≅ F` (and through
the `eqToIso` of an equation of two morphisms of ringed topoi), and the transport of the canonical
pairing along an identification of the inverse image of sheaves of sets with a restriction.

## Main results

* `pullbackTensorIso_inv_val_app_toSheafify_unit`: the inverse of the comparison of Stacks 03EL
  sends the sheafified pure tensor of two units of Tag 03CZ to the unit of the canonical pairing.
* `tensorIsoOfNatIsoRight_trans_eqToIso_pullbackTensorIso_inv_val_app_toSheafify`: for a
  morphism `g₁` equal to `g₂`, the inverse comparison read through the `eqToIso` of the equation
  and `e : g₂^* ≅ F` is computed by the comparison of `g₂`.
* `sectionsFunctor_map_invImageCanonicalPairing`: an identification of the inverse image of
  sheaves of sets with a restriction carries the canonical pairing over `U` to the canonical
  pairing over `F U`.
* `pullbackTensorIso_inv_val_app_toSheafify_pushforward`: when `f^*` is identified with a
  pushforward `F_*` compatibly with the units of Tag 03CZ, the inverse of 03EL sends the
  sheafified pure tensor `x ⊗ y` over `U` to `x ⊗ y` over `F U`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open Stacks.SheafSections
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.SheafOfModules

namespace Stacks.SheafOfModules.RingedToposPullback

universe w w' v u v' u'

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The inverse of the comparison of Stacks 03EL on local pure tensors of units**: it sends the
sheafified pure tensor `(1 ⊗ a) ⊗ (1 ⊗ b)` of two units of Tag 03CZ to the unit of the canonical
pairing of `a` and `b`. -/
theorem pullbackTensorIso_inv_val_app_toSheafify_unit
    (F G : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      ((inverseImageModules f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj F)))
    (b : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      ((inverseImageModules f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G))) :
    ((Stacks.SheafOfModules.pullbackTensorIso f).inv.app (F, G)).val.app U
      ((TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          (((RingedToposHom.pullbackModules f).obj F).val ⊗
              ((RingedToposHom.pullbackModules f).obj G).val)).app U
        (((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom
                ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj F)).val.app U a ⊗ₜ
          ((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom
                ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G)).val.app U b)) =
      ((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj (F ⊗ G))).val.app U
        (pairingApp (inverseImageRingSheaf f.toToposHom
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (invImageCanonicalPairing f F G) U a b) :=
  (congrArg (fun z ↦ ((Stacks.SheafOfModules.pullbackTensorIso f).inv.app (F, G)).val.app U z)
      (comparison_val_app_unit_canonicalPairing f F G U a b).symm).trans
    (inv_val_app_hom_val_app ((Stacks.SheafOfModules.pullbackTensorIso f).app (F, G)) U _)


/-- Sheafification of a morphism of presheaves commutes with the units, on local sections. -/
private theorem sheafification_map_app_toSheafify
    {X : RingedTopos.{v, u, w}} [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P Q : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    (g : P ⟶ Q) (U : X.Cᵒᵖ) (z : P.obj U) :
    ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map g).val.app U
        ((TensorSheafification.toSheafify X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property P).app U z) =
      (TensorSheafification.toSheafify X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property Q).app U (g.app U z) :=
  (congrArg (fun w ↦ w.app U z)
    ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality g)).symm

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Tensoring a morphism in the first factor, on a sheafified local pure tensor. -/
theorem sheafTensor_map_app_val_app_toSheafify
    {A A' : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (φ : A ⟶ A')
    (N : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (U : X.Cᵒᵖ)
    (x : A.val.obj U) (y : N.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map φ).app N).val.app U
        ((TensorSheafification.toSheafify X.O.obj
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          (A.val ⊗ N.val)).app U (x ⊗ₜ y)) =
      (TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          (A'.val ⊗ N.val)).app U (φ.val.app U x ⊗ₜ y) :=
  sheafification_map_app_toSheafify (MonoidalCategory.whiskerRight φ.val N.val) U (x ⊗ₜ y)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Tensoring a morphism in the second factor, on a sheafified local pure tensor. -/
theorem sheafTensor_obj_map_val_app_toSheafify
    (A : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {N N' : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ψ : N ⟶ N') (U : X.Cᵒᵖ)
    (x : A.val.obj U) (y : N.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj A).map ψ).val.app U
        ((TensorSheafification.toSheafify X.O.obj
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          (A.val ⊗ N.val)).app U (x ⊗ₜ y)) =
      (TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          (A.val ⊗ N'.val)).app U (x ⊗ₜ ψ.val.app U y) :=
  sheafification_map_app_toSheafify (MonoidalCategory.whiskerLeft A.val ψ.val) U (x ⊗ₜ y)


/-- The inverse of the comparison of Stacks 03EL read through an isomorphism `e : f^* ≅ F`, at a
pair of modules: `e⁻¹ ⊗ e⁻¹`, then the inverse comparison, then `e`. -/
theorem tensorIsoOfNatIsoRight_pullbackTensorIso_inv_app
    {Fe : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : RingedToposHom.pullbackModules f ≅ Fe)
    (A M : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (PullbackInternalHom.tensorIsoOfNatIsoRight (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) e.symm
        (NatIso.ofComponents
          (F := Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
            RingedToposHom.pullbackModules f)
          (G := (RingedToposHom.pullbackModules f).prod (RingedToposHom.pullbackModules f) ⋙
            Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
          (fun AB ↦ (Stacks.SheafOfModules.pullbackTensorIso f).app AB)
          (Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_uncurry f))).inv.app (A, M) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (e.inv.app A)).app (Fe.obj M) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            ((RingedToposHom.pullbackModules f).obj A)).map
          (e.inv.app M) ≫
        (Stacks.SheafOfModules.pullbackTensorIso f).inv.app (A, M) ≫
        e.hom.app
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O).obj A).obj M) := by
  rw [PullbackInternalHom.tensorIsoOfNatIsoRight_inv_app]
  simp only [Iso.symm_inv, Iso.symm_hom, NatIso.ofComponents_inv_app, Category.assoc]
  rfl


/-- The inverse of the comparison of Stacks 03EL read through an isomorphism `e : f^* ≅ F`, on a
sheafified local pure tensor `x ⊗ y`. -/
theorem tensorIsoOfNatIsoRight_pullbackTensorIso_inv_val_app_toSheafify
    {Fe : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : RingedToposHom.pullbackModules f ≅ Fe)
    (A M : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (x : (Fe.obj A).val.obj U) (y : (Fe.obj M).val.obj U) :
    ((PullbackInternalHom.tensorIsoOfNatIsoRight
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O) e.symm
        (NatIso.ofComponents
          (F := Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
            RingedToposHom.pullbackModules f)
          (G := (RingedToposHom.pullbackModules f).prod (RingedToposHom.pullbackModules f) ⋙
            Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
          (fun AB ↦ (Stacks.SheafOfModules.pullbackTensorIso f).app AB)
          (Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_uncurry f))).inv.app
          (A, M)).val.app U
      ((TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          ((Fe.obj A).val ⊗ (Fe.obj M).val)).app U (x ⊗ₜ y)) =
      (e.hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O).obj A).obj
            M)).val.app U
        (((Stacks.SheafOfModules.pullbackTensorIso f).inv.app (A, M)).val.app U
          ((TensorSheafification.toSheafify X.O.obj
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
              (((RingedToposHom.pullbackModules f).obj A).val ⊗
                  ((RingedToposHom.pullbackModules f).obj M).val)).app U
            ((e.inv.app A).val.app U x ⊗ₜ (e.inv.app M).val.app U y))) := by
  rw [tensorIsoOfNatIsoRight_pullbackTensorIso_inv_app]
  exact (comp_val_app_apply (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).map
        (e.inv.app A)).app (Fe.obj M)) _ U _).trans
    ((congrArg (fun w ↦ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          ((RingedToposHom.pullbackModules f).obj A)).map (e.inv.app M) ≫
        (Stacks.SheafOfModules.pullbackTensorIso f).inv.app (A, M) ≫
        e.hom.app
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O).obj A).obj
              M)).val.app U w)
      (sheafTensor_map_app_val_app_toSheafify (e.inv.app A) (Fe.obj M) U x y)).trans
    ((comp_val_app_apply (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          ((RingedToposHom.pullbackModules f).obj A)).map (e.inv.app M)) _ U _).trans
    ((congrArg (fun w ↦ ((Stacks.SheafOfModules.pullbackTensorIso f).inv.app (A, M) ≫
        e.hom.app (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).obj M)).val.app U w)
      (sheafTensor_obj_map_val_app_toSheafify ((RingedToposHom.pullbackModules f).obj A)
          (e.inv.app M) U
        ((e.inv.app A).val.app U x) y)).trans
    (comp_val_app_apply ((Stacks.SheafOfModules.pullbackTensorIso f).inv.app (A, M)) _ U _))))


section SameUniverse

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- If the inverse image of sheaves of sets is identified by `ε` with restriction along a
continuous functor `F`, then `ε` carries the canonical pairing of two inverse images, on a pair of
local sections over `U`, to the canonical pairing over `F U` of the transported sections. -/
theorem sectionsFunctor_map_invImageCanonicalPairing (F : X.C ⥤ Y.C) [F.IsContinuous X.J Y.J]
    (ε : f.toToposHom.inverseImage ≅ F.sheafPushforwardContinuous (Type w) X.J Y.J)
    (A M : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      ((inverseImageModules f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj A)))
    (b : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      ((inverseImageModules f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj M))) :
    (Sheaf.sectionsFunctor X.J U).map
        (ε.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (A ⊗ M)))
      (pairingApp (inverseImageRingSheaf f.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        (invImageCanonicalPairing f A M) U a b) =
    pairingApp ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (canonicalPairing ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property A M) (F.op.obj U)
        ((Sheaf.sectionsFunctor X.J U).map
          (ε.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) A)) a)
        ((Sheaf.sectionsFunctor X.J U).map
          (ε.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) M)) b) :=
  (sectionsFunctor_map_pairing_natIso ε
      (canonicalPairing ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property A M) U a b).trans
    (sectionsFunctor_map_pairing_sheafPushforwardContinuous F
      (canonicalPairing ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property A M) U _ _)

end SameUniverse


/-- The same, for a comparison `μ` of a morphism `g₁` equal to `g₂`, read through the composite of
the `eqToIso` of the equation with `e : g₂^* ≅ F`: it is computed by the comparison of `g₂`. -/
theorem tensorIsoOfNatIsoRight_trans_eqToIso_pullbackTensorIso_inv_val_app_toSheafify
    {g₁ g₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y} (hg : g₁ = g₂)
    {Fe : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e₁ : RingedToposHom.pullbackModules g₁ ≅ RingedToposHom.pullbackModules g₂)
    (he₁ : e₁ = eqToIso (congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
      RingedToposHom.pullbackModules g) hg))
    (e : RingedToposHom.pullbackModules g₂ ≅ Fe)
    (μ : Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
        RingedToposHom.pullbackModules g₁ ≅
      (RingedToposHom.pullbackModules g₁).prod (RingedToposHom.pullbackModules g₁) ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
    (hμ : μ = NatIso.ofComponents
          (F := Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
            RingedToposHom.pullbackModules g₁)
          (G := (RingedToposHom.pullbackModules g₁).prod (RingedToposHom.pullbackModules g₁) ⋙
            Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
          (fun AB ↦ (Stacks.SheafOfModules.pullbackTensorIso g₁).app AB)
          (Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_uncurry g₁))
    (A M : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (x : (Fe.obj A).val.obj U) (y : (Fe.obj M).val.obj U) :
    ((PullbackInternalHom.tensorIsoOfNatIsoRight
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O) (e₁ ≪≫ e).symm μ).inv.app
          (A, M)).val.app U
      ((TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          ((Fe.obj A).val ⊗ (Fe.obj M).val)).app U (x ⊗ₜ y)) =
      (e.hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w', w'} Y.O).obj A).obj
            M)).val.app U
        (((Stacks.SheafOfModules.pullbackTensorIso g₂).inv.app (A, M)).val.app U
          ((TensorSheafification.toSheafify X.O.obj
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
              (((RingedToposHom.pullbackModules g₂).obj A).val ⊗
                  ((RingedToposHom.pullbackModules g₂).obj M).val)).app U
            ((e.inv.app A).val.app U x ⊗ₜ (e.inv.app M).val.app U y))) := by
  subst he₁ hμ
  subst hg
  rw [Iso.trans_symm, PullbackInternalHom.tensorIsoOfNatIsoRight_trans,
    Stacks.SheafOfModules.tensorIsoOfNatIsoRight_eqToIso_pullbackTensorIso rfl]
  exact tensorIsoOfNatIsoRight_pullbackTensorIso_inv_val_app_toSheafify _ e A M U x y

section SameUniverse

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The inverse of the comparison of Stacks 03EL through a restriction.** Let `e : f^* ≅ F_*`
identify the pullback with the pushforward along a continuous functor `F`, compatibly with an
identification `ε : f⁻¹ ≅ F_*` of sheaves of sets on the units of Tag 03CZ. Then the inverse of
the comparison, read through `e`, sends the sheafified pure tensor `x ⊗ y` over `U` to the
sheafified pure tensor `x ⊗ y` over `F U`. -/
theorem pullbackTensorIso_inv_val_app_toSheafify_pushforward
    (F : X.C ⥤ Y.C) [F.IsContinuous X.J Y.J]
    (ε : f.toToposHom.inverseImage ≅ F.sheafPushforwardContinuous (Type w) X.J Y.J)
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (F.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (e : RingedToposHom.pullbackModules f ≅ _root_.SheafOfModules.pushforward.{w} φ)
    (he : ∀ (G : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        (U : X.Cᵒᵖ)
      (m : ((inverseImageModules f.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G).val.obj U),
      (e.hom.app G).val.app U (((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G)).val.app U m) =
        (ε.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)).hom.app
            U m)
    (A M : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (x : ((_root_.SheafOfModules.pushforward.{w} φ).obj A).val.obj U)
    (y : ((_root_.SheafOfModules.pushforward.{w} φ).obj M).val.obj U) :
    (e.hom.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O).obj A).obj M)).val.app U
        (((Stacks.SheafOfModules.pullbackTensorIso f).inv.app (A, M)).val.app U
          ((TensorSheafification.toSheafify X.O.obj
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
              (((RingedToposHom.pullbackModules f).obj A).val ⊗
                  ((RingedToposHom.pullbackModules f).obj M).val)).app U
            ((e.inv.app A).val.app U x ⊗ₜ (e.inv.app M).val.app U y))) =
      (TensorSheafification.toSheafify Y.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (A.val ⊗ M.val)).app (F.op.obj U) (x ⊗ₜ y) := by
  have hε : ∀ (P : Sheaf Y.J (Type w))
      (z : ((F.sheafPushforwardContinuous (Type w) X.J Y.J).obj P).obj.obj U),
      (ε.hom.app P).hom.app U ((ε.inv.app P).hom.app U z) = z := fun P z ↦ by
    show ((ε.inv.app P ≫ ε.hom.app P).hom.app U z) = z
    rw [Iso.inv_hom_id_app]
    rfl
  have h1 : ∀ (G : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
      (z : ((_root_.SheafOfModules.pushforward.{w} φ).obj G).val.obj U),
      (e.inv.app G).val.app U z = ((structureAdjunction f).unit.app
          ((inverseImageModules f.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G)).val.app U
        ((ε.inv.app (Sheaf.moduleSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)).hom.app U z) := fun G z ↦
    (congrArg (fun q ↦ (e.inv.app G).val.app U q)
        ((he G U _).trans (hε (Sheaf.moduleSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G) z))).symm.trans
      (inv_val_app_hom_val_app (e.app G) U _)
  refine (congrArg (fun z ↦
      (e.hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O).obj A).obj
            M)).val.app U z)
    ((congrArg (fun z ↦ ((Stacks.SheafOfModules.pullbackTensorIso f).inv.app (A, M)).val.app U
      ((TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
              (((RingedToposHom.pullbackModules f).obj A).val ⊗
                  ((RingedToposHom.pullbackModules f).obj M).val)).app U z))
      (congrArg₂ (fun p q ↦ p ⊗ₜ q) (h1 A x) (h1 M y))).trans
      (pullbackTensorIso_inv_val_app_toSheafify_unit f A M U _ _))).trans ?_
  refine (he _ U _).trans ?_
  refine (sectionsFunctor_map_invImageCanonicalPairing f F ε A M U _ _).trans ?_
  refine (congrArg₂ (pairingApp ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (canonicalPairing ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property A M) (F.op.obj U))
    (hε (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) A) x)
    (hε (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) M) y)).trans ?_
  exact pairingApp_canonicalPairing _ A M (F.op.obj U) x y

/-- The same, for the comparison of a morphism `g₁` equal to `g₂`, read through the composite of
the `eqToIso` of the equation with `e`. -/
theorem tensorIsoOfNatIsoRight_trans_eqToIso_pullbackTensorIso_inv_val_app_toSheafify_pushforward
    {g₁ g₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y} (hg : g₁ = g₂)
    (e₁ : RingedToposHom.pullbackModules g₁ ≅ RingedToposHom.pullbackModules g₂)
    (he₁ : e₁ = eqToIso (congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
      RingedToposHom.pullbackModules g) hg))
    (F : X.C ⥤ Y.C) [F.IsContinuous X.J Y.J]
    (ε : g₂.toToposHom.inverseImage ≅ F.sheafPushforwardContinuous (Type w) X.J Y.J)
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (F.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (e : RingedToposHom.pullbackModules g₂ ≅ _root_.SheafOfModules.pushforward.{w} φ)
    (he : ∀ (G : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        (U : X.Cᵒᵖ)
      (m : ((inverseImageModules g₂.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G).val.obj U),
      (e.hom.app G).val.app U (((structureAdjunction g₂).unit.app
          ((inverseImageModules g₂.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G)).val.app U m) =
        (ε.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G)).hom.app
            U m)
    (μ : Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
        RingedToposHom.pullbackModules g₁ ≅
      (RingedToposHom.pullbackModules g₁).prod (RingedToposHom.pullbackModules g₁) ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
    (hμ : μ = NatIso.ofComponents
          (F := Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
            RingedToposHom.pullbackModules g₁)
          (G := (RingedToposHom.pullbackModules g₁).prod (RingedToposHom.pullbackModules g₁) ⋙
            Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))
          (fun AB ↦ (Stacks.SheafOfModules.pullbackTensorIso g₁).app AB)
          (Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_uncurry g₁))
    (A M : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (U : X.Cᵒᵖ)
    (x : ((_root_.SheafOfModules.pushforward.{w} φ).obj A).val.obj U)
    (y : ((_root_.SheafOfModules.pushforward.{w} φ).obj M).val.obj U) :
    ((PullbackInternalHom.tensorIsoOfNatIsoRight
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O) (e₁ ≪≫ e).symm μ).inv.app
          (A, M)).val.app U
      ((TensorSheafification.toSheafify X.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
          (((_root_.SheafOfModules.pushforward.{w} φ).obj A).val ⊗
            ((_root_.SheafOfModules.pushforward.{w} φ).obj M).val)).app U (x ⊗ₜ y)) =
      (TensorSheafification.toSheafify Y.O.obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (A.val ⊗ M.val)).app (F.op.obj U) (x ⊗ₜ y) :=
  (tensorIsoOfNatIsoRight_trans_eqToIso_pullbackTensorIso_inv_val_app_toSheafify hg e₁ he₁ e μ hμ
    A M U x y).trans
    (pullbackTensorIso_inv_val_app_toSheafify_pushforward g₂ F ε φ e he A M U x y)

end SameUniverse

end Stacks.SheafOfModules.RingedToposPullback


end
