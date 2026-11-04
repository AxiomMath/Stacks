module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic

/-!
# The two module-level forms of a morphism of ringed topoi have the same pullback adjunction

A morphism of ringed topoi `f` gives two four-field morphisms of the modules development,
`f.toModulesHom` and `f.toRingedToposModulesHom`, which are equal but not definitionally so, and
two identifications of their direct images of sheaves of modules with `f.pushforwardModules`. This
file shows that those identifications agree up to the equation of the two four-field morphisms, and
deduces that the comparison of left adjoints of the transported adjunctions of Stacks 03D7 is the
`eqToIso` of the equation of pullbacks.

## Main results

* `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso_hom_app_comp_eqToHom`: the two
  identifications of direct images agree.
* `Stacks.Sheaves.RingedToposModules.leftAdjointUniq_ofNatIsoRight_eq_eqToIso`: the comparison of
  left adjoints along equal morphisms of ringed topoi is an `eqToIso`.

## Implementation notes

The objects attached to `f.toModulesHom` and to `f.toRingedToposModulesHom` must never be compared
definitionally: their structure maps differ as terms, and both the elaborator and the kernel time
out deciding the comparison. They are kept apart by `eqToHom` along
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`, and the comparisons on
local sections are stated as heterogeneous equalities.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

/-- `eqToHom` of sheaves of modules is the identity on local sections. -/
private theorem eqToHom_val_app_heq {Y : RingedTopos.{v', u', w'}}
    {M N : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (p : M = N) {V : Y.Cᵒᵖ} (y : M.val.obj V) : HEq ((eqToHom p).val.app V y) y := by
  subst p; rfl

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y)

omit [Y.J.HasSheafCompose (forget CommRingCat)] in
/-- `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` is the identity on local
sections. -/
theorem toModulesPushforwardIso_inv_app_val_app_heq
    (F : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (V : Y.Cᵒᵖ)
    (x : ((pushforwardModules f).obj F).val.obj V) :
    HEq ((f.toModulesPushforwardIso.inv.app F).val.app V x) x :=
  HEq.rfl

omit [Y.J.HasSheafCompose (forget CommRingCat)] in
/-- `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso` is the identity on local
sections. -/
theorem pushforwardModulesIso_hom_app_val_app_heq
    (F : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (V : Y.Cᵒᵖ)
    (x : ((Stacks.Sheaves.RingedToposModules.pushforwardModules
      f.toRingedToposModulesHom).obj F).val.obj V) :
    HEq ((f.pushforwardModulesIso.hom.app F).val.app V x) x :=
  (heq_of_eq (congrArg (fun φ ↦ φ.val.app V
    (((_root_.SheafOfModules.restrictScalars
      (ringUnit f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).map
      ((pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage).hom.app
        F)).val.app V x))
    (eqToHom_app f.pushforwardModules_eq F))).trans
    (eqToHom_val_app_heq _ _)

omit [Y.J.HasSheafCompose (forget CommRingCat)] in
/-- **The two identifications of the direct image of sheaves of modules agree**, up to the
equation `f.toModulesHom = f.toRingedToposModulesHom`. -/
theorem pushforwardModulesIso_hom_app_comp_eqToHom
    (F : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    f.pushforwardModulesIso.hom.app F ≫ f.toModulesPushforwardIso.inv.app F ≫
      eqToHom (congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
        (Stacks.Sheaves.RingedToposModules.pushforwardModules g).obj F)
        (toModulesHom_eq_toRingedToposModulesHom f)) = 𝟙 _ := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  refine ((Stacks.SheafOfModules.comp_val_app_apply _ _ V x).trans
    (Stacks.SheafOfModules.comp_val_app_apply _ _ V _)).trans (eq_of_heq ?_)
  exact (eqToHom_val_app_heq _ _).trans
    ((toModulesPushforwardIso_inv_app_val_app_heq f F V _).trans
      (pushforwardModulesIso_hom_app_val_app_heq f F V x))

end AlgebraicGeometry.RingedToposHom

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Two pullbacks of sheaves of modules along equal morphisms are compared by `eqToIso`.** Let
`g₁ = g₂`, and let the adjunctions of Stacks 03D7 for `g₁` and `g₂` be transported to a common
right adjoint `P` along `α` and along `i` followed by an equation `P = Q` and back. If `i` and `α`
agree up to that equation, the comparison of the two left adjoints is the `eqToIso` of the
equation of pullbacks. -/
theorem leftAdjointUniq_ofNatIsoRight_eq_eqToIso {g₁ g₂ : RingedToposHom X Y} (hg : g₁ = g₂)
    {P Q : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (α : pushforwardModules g₁ ≅ P) (i : pushforwardModules g₂ ≅ P) (p : P = Q)
    (hαi : ∀ F, i.hom.app F ≫ α.inv.app F ≫
      eqToHom (congrArg (fun g : RingedToposHom X Y ↦ (pushforwardModules g).obj F) hg) = 𝟙 _) :
    ((pullbackAdjPushforwardModules g₁).ofNatIsoRight α).leftAdjointUniq
        (((pullbackAdjPushforwardModules g₂).ofNatIsoRight (i ≪≫ eqToIso p)).ofNatIsoRight
          (eqToIso p).symm) =
      eqToIso (congrArg (fun g : RingedToposHom X Y ↦ g.pullbackModules) hg) := by
  subst hg p
  have hβ : i = α := by
    refine Iso.ext (NatTrans.ext (funext fun F => ?_))
    have := hαi F
    rw [eqToHom_refl, Category.comp_id] at this
    have h' := congrArg (· ≫ α.hom.app F) this
    simp only [Category.assoc, Iso.inv_hom_id_app] at h'
    exact h'.trans (Category.id_comp _)
  subst hβ
  have hadj : ((pullbackAdjPushforwardModules g₁).ofNatIsoRight (i ≪≫ eqToIso rfl)).ofNatIsoRight
      (eqToIso rfl).symm = (pullbackAdjPushforwardModules g₁).ofNatIsoRight i := by
    refine Adjunction.ext (NatTrans.ext (funext fun G => ?_))
    simp [Adjunction.ofNatIsoRight]
  rw [hadj]
  exact Iso.ext (by rw [Adjunction.leftAdjointUniq_refl, eqToIso_refl, Iso.refl_hom])

end Stacks.Sheaves.RingedToposModules

end
